//! Module containing the central solving infrastructure.

pub(crate) mod activation_list;
pub(crate) mod bool_to_int;
pub(crate) mod engine;
pub(crate) mod int_var;
pub(crate) mod queue;
pub(crate) mod solving_context;
pub(crate) mod trail;

use std::{
	cell::{Ref, RefCell},
	fmt::{self, Debug, Display, Formatter},
	hash::Hash,
	num::NonZeroI32,
	ops::{Add, AddAssign, Deref, Mul, Neg, Not},
	rc::Rc,
};

use flatzinc_serde::FlatZinc;
use itertools::Itertools;
use pindakaas::{
	solver::{
		cadical::Cadical, propagation::ExternalPropagation, Assumptions, FailedAssumptions,
		LearnCallback, SolveResult as SatSolveResult, TermSignal, TerminateCallback,
	},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Lit as RawLit, Unsatisfiable,
	Valuation as SatValuation,
};
use tracing::{debug, trace};

use crate::{
	actions::{
		BrancherInitActions, DecisionActions, ExplanationActions, InspectionActions,
		PropagatorInitActions, TrailingActions,
	},
	branchers::BoxedBrancher,
	constraints::BoxedPropagator,
	flatzinc::{FlatZincError, FlatZincStatistics},
	reformulate::InitConfig,
	solver::{
		activation_list::{ActivationAction, IntPropCond},
		engine::{trace_new_lit, AdvisorDef, Engine, PropRef},
		int_var::{DirectStorage, IntVarRef, LazyLitDef, OrderStorage},
		queue::{PriorityLevel, PropagatorInfo},
		trail::TrailedInt,
	},
	Clause, IntVal, LinearTransform, Model, NonZeroIntVal, ReformulationError,
};

/// Trait implemented by the object given to the callback on detecting failure
pub trait AssumptionChecker {
	/// Check if the given assumption literal was used to prove the
	/// unsatisfiability of the formula under the assumptions used for the last
	/// SAT search.
	///
	/// Note that for literals 'bv' which are not assumption literals, the
	/// behavior of is not specified.
	fn fail(&self, bv: BoolView) -> bool;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to a Boolean type value in the solver that can be expected as
/// part of a solution.
pub struct BoolView(pub(crate) BoolViewInner);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(variant_size_differences, reason = "`Lit` cannot be as smal as `bool`")]
/// The internal representation of a [`BoolView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub(crate) enum BoolViewInner {
	/// A Boolean literal in the solver.
	Lit(RawLit),
	/// A constant boolean value.
	Const(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Type of the optimization objective
pub enum Goal {
	/// Maximize the value of the given objective
	Maximize,
	/// Minimize the value of the given objective
	Minimize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Statistics related to the initialization of the solver
pub struct InitStatistics {
	// TODO
	// /// Number of (non-view) boolean variables present in the solver
	// bool_vars: usize,
	/// Number of (non-view) integer variables represented in the solver
	int_vars: usize,
	/// Number of propagators in the solver
	propagators: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// The meaning of a literal in the context of a integer decision variable `x`.
pub enum IntLitMeaning {
	/// Literal representing the condition `x = i`.
	Eq(IntVal),
	/// Literal representing the condition `x ≠ i`.
	NotEq(IntVal),
	/// Literal representing the condition `x ≥ i`.
	GreaterEq(IntVal),
	/// Literal representing the condition `x < i`.
	Less(IntVal),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// A reference to a integer type value in the solver that can be expected as
/// part of a solution.
pub struct IntView(pub(crate) IntViewInner);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// The internal representation of [`IntView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub(crate) enum IntViewInner {
	/// (Raw) Integer Variable
	/// Reference to location in the Engine's State
	VarRef(IntVarRef),
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear {
		/// Linear transformation on the integer value of the variable.
		transformer: LinearTransform,
		/// Reference to an integer variable.
		var: IntVarRef,
	},
	/// Linear View of an Boolean Literal.
	Bool {
		/// Linear transformation on the integer value of the Boolean literal.
		transformer: LinearTransform,
		/// The Boolean literal that is being treated as an integer (`false` ->
		/// `0` and `true` -> `1`).
		lit: RawLit,
	},
}

/// An assumption checker that can be used when no assumptions are used.
///
/// Note that this checker will always return false.
pub(crate) struct NoAssumptions;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// Structure capturing statitical information about the search performed by the
/// solver instance.
pub struct SearchStatistics {
	/// Number of conflicts encountered
	pub(crate) conflicts: u64,
	/// Number of search decisions left to the oracle solver
	pub(crate) oracle_decisions: u64,
	/// Peak search depth
	pub(crate) peak_depth: u32,
	/// Number of times a CP propagator was called
	pub(crate) propagations: u64,
	/// Number of backtracks to level 0
	pub(crate) restarts: u32,
	/// Number of decisions following the user-specified search heuristics
	pub(crate) user_decisions: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Result of a solving attempt
pub enum SolveResult {
	/// The solver has found a solution.
	Satisfied,
	/// The solver has proven that the problem is unsatisfiable.
	Unsatisfiable,
	/// The solver that no more/better solutions can be found.
	Complete,
	/// The solver was interrupted before a result could be reached.
	Unknown,
}
#[derive(Debug)]
/// The main solver object that is used to interact with the LCG solver.
pub struct Solver<Oracle = Cadical> {
	/// The oracle solver that has been connected to [`Self::engine`] to perform
	/// external propagation.
	pub(crate) oracle: Oracle,
	/// A reference to the [`Engine`] instance that is connected to
	/// [`Self::oracle`].
	pub(crate) engine: Rc<RefCell<Engine>>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Structure holding the options using to configure the solver during its
/// initialization.
pub(crate) struct SolverConfiguration {
	/// Switch between the activity-based search heuristic and the user-specific
	/// search heuristic after each restart.
	///
	/// This option is ignored if [`vsids_only`] is set to `true`.
	toggle_vsids: bool,
	/// Switch to the activity-based search heuristic after the given number of
	/// conflicts.
	///
	/// This option is ignored if [`toggle_vsids`] or [`vsids_only`] is set to
	/// `true`.
	vsids_after_conflict: Option<u32>,
	/// Switch to the activity-based search heuristic after restart.
	///
	/// This option is ignored if [`toggle_vsids`] or [`vsids_only`] is set to
	/// `true`.
	vsids_after_restart: bool,
	/// Only use the activity-based search heuristic provided by the SAT solver.
	/// Ignore the user-specific search heuristic.
	vsids_only: bool,
}

/// A trait for a function that can be used to evaluate a `SolverView` to a
/// `Value`, which can be used when inspecting a solution.
pub trait Valuation: Fn(View) -> Value {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(variant_size_differences, reason = "`Int` cannot be as smal as `Bool`")]
/// The general representation of a solution value in the solver.
pub enum Value {
	/// A Boolean value.
	Bool(bool),
	/// An integer value.
	Int(IntVal),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to a value in the solver that can be expected as part of a
/// solution.
pub enum View {
	/// A Boolean type value.
	Bool(BoolView),
	/// An integer type value.
	Int(IntView),
}

fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

impl<A: FailedAssumptions> AssumptionChecker for A {
	fn fail(&self, bv: BoolView) -> bool {
		match bv {
			BoolView(BoolViewInner::Lit(lit)) => self.fail(lit),
			BoolView(BoolViewInner::Const(false)) => true,
			BoolView(BoolViewInner::Const(true)) => false,
		}
	}
}

impl From<BoolView> for BoolVal {
	fn from(val: BoolView) -> Self {
		match val.0 {
			BoolViewInner::Lit(l) => l.into(),
			BoolViewInner::Const(b) => b.into(),
		}
	}
}

impl BoolView {
	/// Return an integers that can used to identify the literal, if there is
	/// one.
	pub fn reverse_map_info(&self) -> Option<NonZeroI32> {
		match self.0 {
			BoolViewInner::Lit(v) => Some(v.into()),
			BoolViewInner::Const(_) => None,
		}
	}
}

impl Add<IntVal> for BoolView {
	type Output = IntView;

	fn add(self, rhs: IntVal) -> Self::Output {
		match self.0 {
			BoolViewInner::Lit(lit) => IntView(IntViewInner::Bool {
				transformer: LinearTransform::offset(rhs),
				lit,
			}),
			BoolViewInner::Const(b) => (b as IntVal + rhs).into(),
		}
	}
}

impl From<bool> for BoolView {
	fn from(value: bool) -> Self {
		BoolView(BoolViewInner::Const(value))
	}
}

impl Mul<IntVal> for BoolView {
	type Output = IntView;

	fn mul(self, rhs: IntVal) -> Self::Output {
		match self.0 {
			_ if rhs == 0 => IntView(IntViewInner::Const(0)),
			BoolViewInner::Lit(lit) => IntView(IntViewInner::Bool {
				transformer: LinearTransform::scaled(NonZeroIntVal::new(rhs).unwrap()),
				lit,
			}),
			BoolViewInner::Const(b) => (b as IntVal * rhs).into(),
		}
	}
}

impl Not for BoolView {
	type Output = Self;

	fn not(self) -> Self::Output {
		BoolView(match self.0 {
			BoolViewInner::Lit(l) => BoolViewInner::Lit(!l),
			BoolViewInner::Const(b) => BoolViewInner::Const(!b),
		})
	}
}

impl<F: Fn(View) -> Value> Valuation for F {}

impl InitStatistics {
	/// Number of integer variables present in the solver
	pub fn int_vars(&self) -> usize {
		self.int_vars
	}
	/// Number of propagators present in the solver
	pub fn propagators(&self) -> usize {
		self.propagators
	}
}

impl IntLitMeaning {
	/// Returns the clauses that can be used to define the given literal
	/// according to the meaning `self`.
	///
	/// Note this method is only intended to be used to define positive
	/// literals, and it is thus assumed to be unreachable to be called on
	/// [`LitMeaning::NotEq`] or [`LitMeaning::GreaterEq`].
	pub(crate) fn defining_clauses(
		&self,
		lit: RawLit,
		prev: Option<RawLit>,
		next: Option<RawLit>,
	) -> Vec<Clause> {
		let mut ret = Vec::<Clause>::new();
		match self {
			IntLitMeaning::Eq(_) => {
				let prev = prev.expect("prev should contain the GreaterEq literal for the value"); // x≥i
				let next =
					next.expect("next should contain the GreaterEq literal for the next value"); // x≥i+n

				ret.push(vec![!lit, !prev]); // x=i -> x≥i
				ret.push(vec![!lit, next]); // x=i -> x<i+n
				ret.push(vec![lit, prev, !next]); // x!=i -> x<i \/ x>i+n
			}
			IntLitMeaning::Less(_) => {
				if let Some(prev) = prev {
					ret.push(vec![!prev, lit]); // x<(i-n) -> x<i
				}
				if let Some(next) = next {
					ret.push(vec![!lit, next]); // x<i -> x<(i+n)
				}
			}
			_ => unreachable!(),
		}
		ret
	}
}

impl Not for IntLitMeaning {
	type Output = IntLitMeaning;

	fn not(self) -> Self::Output {
		match self {
			IntLitMeaning::Eq(i) => IntLitMeaning::NotEq(i),
			IntLitMeaning::NotEq(i) => IntLitMeaning::Eq(i),
			IntLitMeaning::GreaterEq(i) => IntLitMeaning::Less(i),
			IntLitMeaning::Less(i) => IntLitMeaning::GreaterEq(i),
		}
	}
}

impl IntView {
	/// Returns an integer that can be used to identify the associated integer
	/// decision variable and whether the int view is a view on another decision
	/// variable.
	pub fn int_reverse_map_info(&self) -> (Option<usize>, bool) {
		match self.0 {
			IntViewInner::VarRef(v) => (Some(v.into()), false),
			IntViewInner::Bool { .. } => (None, true),
			IntViewInner::Linear { var, .. } => (Some(var.into()), true),
			_ => (None, true),
		}
	}
	/// Return a list of integers that can used to identify the literals that
	/// are associated to an integer view, and the meaning of those literals.
	pub fn lit_reverse_map_info<Oracle: Assumptions>(
		&self,
		slv: &Solver<Oracle>,
	) -> Vec<(NonZeroI32, IntLitMeaning)> {
		let transformer = match self.0 {
			IntViewInner::Bool { transformer, .. } | IntViewInner::Linear { transformer, .. } => {
				transformer
			}
			_ => LinearTransform::default(),
		};
		match self.0 {
			IntViewInner::VarRef(v) | IntViewInner::Linear { var: v, .. } => {
				let var = &slv.engine.borrow().state.int_vars[v];
				let mut lits = Vec::new();

				if let OrderStorage::Eager { storage, .. } = &var.order_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					let _ = val_iter.next();
					for (lit, val) in (*storage).zip(val_iter) {
						let i: NonZeroI32 = lit.into();
						let orig = IntLitMeaning::Less(val);
						let lt = transformer.transform_lit(orig);
						let geq = !lt.clone();
						lits.extend([(i, lt), (-i, geq)]);
					}
				}

				if let DirectStorage::Eager(vars) = &var.direct_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					let _ = val_iter.next();
					let _ = val_iter.next_back();
					for (lit, val) in (*vars).zip(val_iter) {
						let i: NonZeroI32 = lit.into();
						let orig = IntLitMeaning::Eq(val);
						let eq = transformer.transform_lit(orig);
						let ne = !eq.clone();
						lits.extend([(i, eq), (-i, ne)]);
					}
				}
				lits
			}
			IntViewInner::Bool { lit, .. } => {
				let i: NonZeroI32 = lit.into();
				let lb = IntLitMeaning::Eq(transformer.transform(0));
				let ub = IntLitMeaning::Eq(transformer.transform(1));
				vec![(i, ub), (-i, lb)]
			}
			_ => Vec::new(),
		}
	}
}

impl Add<IntVal> for IntView {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		Self(match self.0 {
			IntViewInner::VarRef(var) => IntViewInner::Linear {
				transformer: LinearTransform::offset(rhs),
				var,
			},
			IntViewInner::Const(i) => IntViewInner::Const(i + rhs),
			IntViewInner::Linear {
				transformer: transform,
				var,
			} => IntViewInner::Linear {
				transformer: transform + rhs,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: transformer + rhs,
				lit,
			},
		})
	}
}

impl From<BoolView> for IntView {
	fn from(value: BoolView) -> Self {
		Self(match value.0 {
			BoolViewInner::Lit(l) => IntViewInner::Bool {
				transformer: LinearTransform::offset(0),
				lit: l,
			},
			BoolViewInner::Const(c) => IntViewInner::Const(c as IntVal),
		})
	}
}

impl From<IntVal> for IntView {
	fn from(value: IntVal) -> Self {
		Self(IntViewInner::Const(value))
	}
}

impl Mul<NonZeroIntVal> for IntView {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		Self(match self.0 {
			x if rhs.get() == 1 => x,
			IntViewInner::VarRef(iv) => IntViewInner::Linear {
				transformer: LinearTransform::scaled(rhs),
				var: iv,
			},
			IntViewInner::Const(c) => IntViewInner::Const(c * rhs.get()),
			IntViewInner::Linear { transformer, var } => IntViewInner::Linear {
				transformer: transformer * rhs,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: transformer * rhs,
				lit,
			},
		})
	}
}

impl Neg for IntView {
	type Output = Self;

	fn neg(self) -> Self::Output {
		Self(match self.0 {
			IntViewInner::VarRef(var) => IntViewInner::Linear {
				transformer: LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()),
				var,
			},
			IntViewInner::Const(i) => IntViewInner::Const(-i),
			IntViewInner::Linear {
				transformer: transform,
				var,
			} => IntViewInner::Linear {
				transformer: -transform,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: -transformer,
				lit,
			},
		})
	}
}

impl AssumptionChecker for NoAssumptions {
	fn fail(&self, bv: BoolView) -> bool {
		matches!(bv, BoolView(BoolViewInner::Const(false)))
	}
}

impl SearchStatistics {
	/// Returns the number of conflicts encountered during the search.
	pub fn conflicts(&self) -> u64 {
		self.conflicts
	}

	/// Returns the number of propagations performed by the constraint
	/// programming engine during the search.
	pub fn cp_propagations(&self) -> u64 {
		self.propagations
	}

	/// Return the number of search decisions that was left to the oracle
	/// solver.
	pub fn oracle_decisions(&self) -> u64 {
		self.oracle_decisions
	}

	/// Returns the peak depth of the search tree.
	pub fn peak_depth(&self) -> u32 {
		self.peak_depth
	}

	/// Returns the number of times the search was restarted by the oracle
	/// solver.
	pub fn restarts(&self) -> u32 {
		self.restarts
	}

	/// Returns the number of search decisions that followed the user specified
	/// search heuristic.
	pub fn user_decisions(&self) -> u64 {
		self.user_decisions
	}
}

impl Add for SearchStatistics {
	type Output = SearchStatistics;

	fn add(mut self, other: SearchStatistics) -> SearchStatistics {
		self += other;
		self
	}
}

impl AddAssign for SearchStatistics {
	fn add_assign(&mut self, other: SearchStatistics) {
		self.conflicts += other.conflicts;
		self.oracle_decisions += other.oracle_decisions;
		self.peak_depth = self.peak_depth.max(other.peak_depth);
		self.propagations += other.propagations;
		self.restarts += other.restarts;
		self.user_decisions += other.user_decisions;
	}
}

impl<Oracle: ClauseDatabase> Solver<Oracle> {
	/// Add a clause to the solver
	pub fn add_clause<Iter>(&mut self, clause: Iter) -> Result<(), ReformulationError>
	where
		Iter: IntoIterator,
		Iter::Item: Into<BoolView>,
	{
		Ok(ClauseDatabaseTools::add_clause(
			self,
			clause.into_iter().map(Into::into),
		)?)
	}
}

impl<Oracle: LearnCallback> Solver<Oracle> {
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	pub fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = RawLit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		if let Some(mut f) = cb {
			self.oracle.set_learn_callback(Some(
				move |clause: &mut dyn Iterator<Item = RawLit>| {
					trace_learned_clause(clause);
					f(clause);
				},
			));
		} else {
			self.oracle.set_learn_callback(Some(trace_learned_clause));
		}
	}
}

impl<Oracle: TerminateCallback> Solver<Oracle> {
	/// Set a callback function used to indicate a termination requirement to
	/// the solver.
	///
	/// The solver will periodically call this function and check its return
	/// value during the search. Subsequent calls to this method override the
	/// previously set callback function.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	pub fn set_terminate_callback<F: FnMut() -> TermSignal + 'static>(&mut self, cb: Option<F>) {
		self.oracle.set_terminate_callback(cb);
	}
}

impl<Oracle: ExternalPropagation> Solver<Oracle> {
	#[doc(hidden)]
	/// Method used to add a no-good clause from a solution. This clause can be
	/// used to ensure that the same solution is not found again.
	///
	/// ## Warning
	/// This method will panic if the number of variables and values do not
	/// match.
	pub fn add_no_good(&mut self, vars: &[View], vals: &[Value]) -> Result<(), ReformulationError> {
		let clause = vars
			.iter()
			.zip_eq(vals)
			.map(|(var, val)| match *var {
				View::Bool(bv) => match val {
					Value::Bool(true) => !bv,
					Value::Bool(false) => bv,
					_ => unreachable!(),
				},
				View::Int(iv) => {
					let Value::Int(val) = val.clone() else {
						unreachable!()
					};
					self.get_int_lit(iv, IntLitMeaning::NotEq(val))
				}
			})
			.collect_vec();
		debug!(clause = ?clause.iter().filter_map(|&x| if let BoolView(BoolViewInner::Lit(x)) = x { Some(i32::from(x)) } else { None }).collect::<Vec<i32>>(), "add solution nogood");
		self.add_clause(clause)
	}

	/// Internal method used to add an advisor that is triggered when a
	/// [`RawLit`] changes.
	///
	/// Used by [`Solver::advise_on_bool_change`] and
	/// [`Solver::advise_on_int_change`].
	fn advise_on_lit_change(&mut self, prop: PropRef, lit: RawLit, data: u64, bool2int: bool) {
		self.oracle.add_observed_var(lit.var());
		let state = &mut self.engine.borrow_mut().state;
		state.trail.grow_to_boolvar(lit.var());
		let adv = state.advisors.push(AdvisorDef {
			bool2int,
			data,
			negated: false,
			propagator: prop,
		});
		state
			.bool_activation
			.entry(lit.var())
			.or_default()
			.push(ActivationAction::Advise(adv).into());
	}

	/// Find all solutions with regard to a list of given variables.
	/// The given closure will be called for each solution found.
	///
	/// WARNING: This method will add additional clauses into the solver to
	/// prevent the same solution from being generated twice. This will make
	/// repeated use of the Solver object impossible. Note that you can clone
	/// the Solver object before calling this method to work around this
	/// limitation.
	pub fn all_solutions(
		mut self,
		vars: &[View],
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> (SolveResult, SearchStatistics) {
		use SolveResult::*;

		let ret = |x: Self, status: SolveResult| (status, x.search_statistics());

		let mut num_sol = 0;
		loop {
			let mut vals = Vec::with_capacity(vars.len());
			let status = self.solve(|value| {
				num_sol += 1;
				for v in vars {
					vals.push(value(*v));
				}
				on_sol(value);
			});
			match status {
				Satisfied => {
					if self.add_no_good(vars, &vals).is_err() {
						return ret(self, Complete);
					}
				}
				Unsatisfiable => {
					if num_sol == 0 {
						return ret(self, Unsatisfiable);
					} else {
						return ret(self, Complete);
					}
				}
				Unknown => {
					if num_sol == 0 {
						return ret(self, Unknown);
					} else {
						return ret(self, Satisfied);
					}
				}
				_ => unreachable!(),
			}
		}
	}

	/// Find an optimal solution with regards to the given objective and goal.
	///
	/// Note that this method uses assumptions iteratively increase the lower
	/// bound of the objective. This does not impact the state of the solver
	/// for continued use.
	pub fn branch_and_bound(
		mut self,
		objective: IntView,
		goal: Goal,
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> (SolveResult, SearchStatistics, Option<IntVal>) {
		use SolveResult::*;
		let ret = |x: Self, status: SolveResult, obj: Option<IntVal>| {
			(status, x.search_statistics(), obj)
		};

		let mut obj_curr = None;
		let obj_bound = match goal {
			Goal::Minimize => self.get_int_lower_bound(objective),
			Goal::Maximize => self.get_int_upper_bound(objective),
		};
		debug!(obj_bound, "start branch and bound");
		loop {
			let status = self.solve(|value| {
				obj_curr = if let Value::Int(i) = value(View::Int(objective)) {
					Some(i)
				} else {
					unreachable!()
				};
				on_sol(value);
			});
			debug!(?status, ?obj_curr, obj_bound, ?goal, "oracle solve result");
			match status {
				Satisfied => {
					if obj_curr == Some(obj_bound) {
						return ret(self, Complete, obj_curr);
					} else {
						let bound_lit = match goal {
							Goal::Minimize => Some(
								self.get_int_lit(objective, IntLitMeaning::Less(obj_curr.unwrap())),
							),
							Goal::Maximize => Some(self.get_int_lit(
								objective,
								IntLitMeaning::GreaterEq(obj_curr.unwrap() + 1),
							)),
						};
						debug!(
							lit = i32::from({
								let BoolViewInner::Lit(l) = bound_lit.unwrap().0 else {
									unreachable!()
								};
								l
							}),
							"add objective bound"
						);
						self.add_clause([bound_lit.unwrap()]).unwrap();
					}
				}
				Unsatisfiable => {
					return if obj_curr.is_none() {
						ret(self, Unsatisfiable, None)
					} else {
						ret(self, Complete, obj_curr)
					};
				}
				Unknown => {
					return if obj_curr.is_none() {
						ret(self, Unknown, None)
					} else {
						ret(self, Satisfied, obj_curr)
					}
				}
				Complete => unreachable!(),
			}
		}
	}

	/// Create a new [`Solver`] instance from a [`FlatZinc`] instance.
	pub fn from_fzn<S, MapTy: FromIterator<(S, View)>>(
		fzn: &FlatZinc<S>,
		config: &InitConfig,
	) -> Result<(Self, MapTy, FlatZincStatistics), FlatZincError>
	where
		S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
		Solver<Oracle>: for<'a> From<&'a Cnf>,
		Oracle: 'static,
	{
		let (mut prb, map, fzn_stats) = Model::from_fzn::<S, Vec<_>>(fzn, config)?;
		let (mut slv, remap) = prb.to_solver(config)?;
		let map = map
			.into_iter()
			.map(|(k, v)| (k, remap.get(&mut slv, &v)))
			.collect();
		Ok((slv, map, fzn_stats))
	}

	/// Wrapper function for `all_solutions` that collects all solutions and
	/// returns them in a vector of solution values.
	///
	/// WARNING: This method will add additional clauses into the solver to
	/// prevent the same solution from being generated twice. This will make
	/// repeated use of the Solver object impossible. Note that you can clone
	/// the Solver object before calling this method to work around this
	/// limitation.
	pub fn get_all_solutions(
		self,
		vars: &[View],
	) -> (SolveResult, SearchStatistics, Vec<Vec<Value>>) {
		let mut solutions = Vec::new();
		let (status, stats) = self.all_solutions(vars, |sol| {
			let mut sol_vec = Vec::with_capacity(vars.len());
			for v in vars {
				sol_vec.push(sol(*v));
			}
			solutions.push(sol_vec);
		});
		(status, stats, solutions)
	}

	/// Access the initilization statistics of the [`Solver`] object.
	pub fn init_statistics(&self) -> InitStatistics {
		InitStatistics {
			int_vars: self.engine.borrow().state.int_vars.len(),
			propagators: self.engine.borrow().propagators.len(),
		}
	}

	/// Access the search statistics for the search process up to this point.
	pub fn search_statistics(&self) -> SearchStatistics {
		let cp_stats = &self.engine.borrow().state.statistics;
		SearchStatistics {
			conflicts: cp_stats.conflicts,
			oracle_decisions: cp_stats.oracle_decisions,
			peak_depth: cp_stats.peak_depth,
			propagations: cp_stats.propagations,
			restarts: cp_stats.restarts,
			user_decisions: cp_stats.user_decisions,
		}
	}

	/// Set whether the solver should toggle between VSIDS and a user defined
	/// search strategy after every restart.
	///
	/// Note that this setting is ignored if the solver is set to use VSIDS
	/// only.
	pub fn set_toggle_vsids(&mut self, enable: bool) {
		self.engine.borrow_mut().state.set_toggle_vsids(enable);
	}

	/// Set the number of conflicts after which the solver should switch to
	/// using VSIDS to make search decisions.
	pub fn set_vsids_after_conflict(&mut self, conflicts: Option<u32>) {
		self.engine
			.borrow_mut()
			.state
			.set_vsids_after_conflict(conflicts);
	}

	/// Set whether the solver should switch to VSIDS after restart to make
	/// search.
	pub fn set_vsids_after_restart(&mut self, enable: bool) {
		self.engine
			.borrow_mut()
			.state
			.set_vsids_after_restart(enable);
	}

	/// Set whether the solver should make all search decisions based on the
	/// VSIDS only.
	pub fn set_vsids_only(&mut self, enable: bool) {
		self.engine.borrow_mut().state.set_vsids_only(enable);
	}

	/// Try and find a solution to the problem for which the Solver was
	/// initialized.
	pub fn solve(&mut self, mut on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		let result = self.oracle.solve();
		match result {
			SatSolveResult::Satisfied(sol) => {
				let wrapped_valuation = Self::wrap_valuation(self.engine.borrow(), sol);
				on_sol(&wrapped_valuation);
				SolveResult::Satisfied
			}
			SatSolveResult::Unsatisfiable(_) => SolveResult::Unsatisfiable,
			SatSolveResult::Unknown => SolveResult::Unknown,
		}
	}

	/// Wraps a [`SatValuation`] into a [`Valuation`] instance using the
	/// provided [`Engine`] instance as context.
	fn wrap_valuation<'a>(
		engine: Ref<'a, Engine>,
		sol: impl SatValuation + 'a,
	) -> impl Valuation + 'a {
		let get_int_val = |engine: Ref<Engine>, iv: IntVarRef| {
			let var_def = &engine.state.int_vars[iv];
			let val = var_def.get_lower_bound(&engine.state.trail);
			debug_assert!(
				matches!(var_def.order_encoding, OrderStorage::Lazy(_))
					|| val == var_def.get_upper_bound(&engine.state.trail)
			);
			val
		};
		move |x| match x {
			View::Bool(lit) => Value::Bool(match lit.0 {
				BoolViewInner::Lit(lit) => sol.value(lit),
				BoolViewInner::Const(b) => b,
			}),
			View::Int(var) => Value::Int(match var.0 {
				IntViewInner::VarRef(iv) => get_int_val(Ref::clone(&engine), iv),
				IntViewInner::Const(i) => i,
				IntViewInner::Linear {
					transformer: transform,
					var,
				} => transform.transform(get_int_val(Ref::clone(&engine), var)),
				IntViewInner::Bool { transformer, lit } => {
					transformer.transform(sol.value(lit) as IntVal)
				}
			}),
		}
	}
}

impl<Oracle: ExternalPropagation + Assumptions> Solver<Oracle> {
	/// Try and find a solution to the problem for which the Solver was
	/// initialized, given a list of Boolean assumptions.
	pub fn solve_assuming(
		&mut self,
		assumptions: impl IntoIterator<Item = BoolView>,
		mut on_sol: impl FnMut(&dyn Valuation),
		on_fail: impl FnOnce(&dyn AssumptionChecker),
	) -> SolveResult {
		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assumptions
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolViewInner::Lit(lit) => Some(Ok(lit)),
				BoolViewInner::Const(true) => None,
				BoolViewInner::Const(false) => Some(Err(ReformulationError::TrivialUnsatisfiable)),
			})
			.collect()
		else {
			on_fail(&NoAssumptions);
			return SolveResult::Unsatisfiable;
		};

		let result = self.oracle.solve_assuming(assumptions);
		match result {
			SatSolveResult::Satisfied(sol) => {
				let wrapped_valuation = Self::wrap_valuation(self.engine.borrow(), sol);
				on_sol(&wrapped_valuation);
				SolveResult::Satisfied
			}
			SatSolveResult::Unsatisfiable(fail) => {
				on_fail(&fail);
				SolveResult::Unsatisfiable
			}
			SatSolveResult::Unknown => SolveResult::Unknown,
		}
	}
}

impl<Oracle: ExternalPropagation> BrancherInitActions for Solver<Oracle> {
	fn ensure_decidable(&mut self, view: View) {
		match view {
			View::Bool(BoolView(BoolViewInner::Lit(lit)))
			| View::Int(IntView(IntViewInner::Bool { lit, .. })) => {
				self.engine
					.borrow_mut()
					.state
					.trail
					.grow_to_boolvar(lit.var());
				self.oracle.add_observed_var(lit.var());
			}
			_ => {
				// Nothing has to happend for constants and all literals for
				// integer variables are already marked as observed.
			}
		}
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		<Self as PropagatorInitActions>::new_trailed_int(self, init)
	}

	fn push_brancher(&mut self, brancher: BoxedBrancher) {
		self.engine.borrow_mut().branchers.push(brancher);
	}
}

impl<Oracle: ClauseDatabase> ClauseDatabase for Solver<Oracle> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		self.oracle.add_clause_from_slice(clause)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.oracle.new_var_range(len)
	}
}

impl Clone for Solver<Cadical> {
	fn clone(&self) -> Self {
		let mut oracle = self.oracle.shallow_clone();
		let engine: Engine = self.engine.borrow().clone();
		let engine = Rc::new(RefCell::new(engine));
		oracle.connect_propagator(Rc::clone(&engine));
		for var in oracle.emitted_vars() {
			if self.oracle.is_observed(var.into()) {
				oracle.add_observed_var(var);
			}
		}
		Solver { oracle, engine }
	}
}

impl<Oracle: ExternalPropagation> DecisionActions for Solver<Oracle> {
	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: IntLitMeaning) -> BoolView {
		let mut clauses = Vec::new();
		let bv = {
			let mut engine = self.engine.borrow_mut();
			let state = &mut engine.state;
			let var = &mut state.int_vars[iv];
			let new_var = |def: LazyLitDef| {
				// Create new variable
				let v = self.oracle.new_var();
				self.oracle.add_observed_var(v);
				trace_new_lit!(iv, def, v);
				state.trail.grow_to_boolvar(v);
				state.bool_to_int.insert_lazy(v, iv, def.meaning.clone());
				// Add clauses to define the new variable
				for cl in def.meaning.defining_clauses(
					v.into(),
					def.prev.map(Into::into),
					def.next.map(Into::into),
				) {
					trace!(clause = ?cl.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add clause");
					clauses.push(cl);
				}
				v
			};
			var.bool_lit(meaning, new_var)
		};
		for cl in clauses {
			self.oracle
				.add_clause_from_slice(&cl)
				.expect("functional definition cannot make the problem unsatisfiable");
		}
		bv
	}

	fn get_num_conflicts(&self) -> u64 {
		self.engine.borrow().state.statistics.conflicts
	}
}

impl<Oracle: ExternalPropagation> ExplanationActions for Solver<Oracle> {
	fn get_int_lit_meaning(&self, var: IntView, lit: RawLit) -> Option<IntLitMeaning> {
		self.engine.borrow().state.get_int_lit_meaning(var, lit)
	}

	fn get_int_lit_relaxed(
		&mut self,
		var: IntView,
		meaning: IntLitMeaning,
	) -> (BoolView, IntLitMeaning) {
		self.engine
			.borrow_mut()
			.state
			.get_int_lit_relaxed(var, meaning)
	}

	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView {
		self.engine.borrow_mut().state.get_int_lower_bound_lit(var)
	}

	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView {
		self.engine.borrow_mut().state.get_int_upper_bound_lit(var)
	}
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		let val = self.get_int_val(var)?;
		Some(self.get_int_lit(var, IntLitMeaning::Eq(val)))
	}

	fn try_int_lit(&self, var: IntView, meaning: IntLitMeaning) -> Option<BoolView> {
		self.engine.borrow().state.try_int_lit(var, meaning)
	}
}

impl<Oracle> From<&Cnf> for Solver<Oracle>
where
	Oracle: ExternalPropagation + for<'a> From<&'a Cnf> + LearnCallback,
{
	fn from(value: &Cnf) -> Self {
		let mut oracle: Oracle = value.into();
		let engine = Rc::default();
		oracle.set_learn_callback(Some(trace_learned_clause));
		oracle.connect_propagator(Rc::clone(&engine));
		Self { oracle, engine }
	}
}

impl<Oracle: ExternalPropagation> InspectionActions for Solver<Oracle> {
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		self.engine.borrow().state.check_int_in_domain(var, val)
	}

	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		self.engine.borrow().state.get_int_bounds(var)
	}

	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		self.engine.borrow().state.get_int_lower_bound(var)
	}

	fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		self.engine.borrow().state.get_int_upper_bound(var)
	}

	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		self.engine.borrow().state.get_int_val(var)
	}
}

impl<Oracle: ExternalPropagation> PropagatorInitActions for Solver<Oracle> {
	fn add_propagator(&mut self, propagator: BoxedPropagator, priority: PriorityLevel) -> PropRef {
		let mut engine = self.engine.borrow_mut();
		let prop_ref = engine.propagators.push(propagator);
		let p = engine.state.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(prop_ref, p);
		p
	}

	fn advise_on_backtrack(&mut self, prop: PropRef) {
		self.engine.borrow_mut().notify_of_backtrack.push(prop);
	}

	fn advise_on_bool_change(&mut self, prop: PropRef, var: BoolView, data: u64) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				self.advise_on_lit_change(prop, lit, data, false);
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn advise_on_int_change(
		&mut self,
		prop: PropRef,
		var: IntView,
		condition: IntPropCond,
		data: u64,
	) {
		let (var, cond, negated) = match var.0 {
			IntViewInner::VarRef(var) => (var, condition, false),
			IntViewInner::Linear { transformer, var } => {
				let condition = match condition {
					IntPropCond::LowerBound if !transformer.positive_scale() => {
						IntPropCond::UpperBound
					}
					IntPropCond::UpperBound if !transformer.positive_scale() => {
						IntPropCond::LowerBound
					}
					_ => condition,
				};
				(var, condition, !transformer.positive_scale())
			}
			IntViewInner::Const(_) => return, // ignore
			IntViewInner::Bool { lit, .. } => {
				return self.advise_on_lit_change(prop, lit, data, true);
			}
		};

		let state = &mut self.engine.borrow_mut().state;
		let adv = state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated,
			propagator: prop,
		});
		state.int_activation[var].add(ActivationAction::Advise(adv), cond);
	}

	fn enqueue_now(&mut self, prop: PropRef) {
		let state = &mut self.engine.borrow_mut().state;
		state.propagator_queue.enqueue_propagator(prop);
	}

	fn enqueue_on_bool_change(&mut self, prop: PropRef, var: BoolView) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				{
					let state = &mut self.engine.borrow_mut().state;
					state.trail.grow_to_boolvar(lit.var());
					state
						.bool_activation
						.entry(lit.var())
						.or_default()
						.push(ActivationAction::Enqueue(prop).into());
				}
				self.oracle.add_observed_var(lit.var());
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn enqueue_on_int_change(&mut self, prop: PropRef, var: IntView, condition: IntPropCond) {
		let (var, cond) = match var.0 {
			IntViewInner::VarRef(var) => (var, condition),
			IntViewInner::Linear { transformer, var } => {
				let condition = if transformer.positive_scale() {
					condition
				} else {
					match condition {
						IntPropCond::LowerBound => IntPropCond::UpperBound,
						IntPropCond::UpperBound => IntPropCond::LowerBound,
						_ => condition,
					}
				};
				(var, condition)
			}
			IntViewInner::Const(_) => return, // ignore
			IntViewInner::Bool { lit, .. } => {
				return self.enqueue_on_bool_change(prop, BoolView(BoolViewInner::Lit(lit)))
			}
		};
		self.engine.borrow_mut().state.int_activation[var]
			.add(ActivationAction::Enqueue(prop), cond);
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.engine.borrow_mut().state.trail.track_int(init)
	}
}

impl<Oracle: ExternalPropagation> TrailingActions for Solver<Oracle> {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		self.engine.borrow().state.get_bool_val(bv)
	}

	fn get_trailed_int(&self, x: TrailedInt) -> IntVal {
		self.engine.borrow().state.get_trailed_int(x)
	}

	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal {
		self.engine.borrow_mut().state.set_trailed_int(x, v)
	}
}

impl Value {
	/// If the `Value` is a Boolean, represent it as bool. Returns None
	/// otherwise.
	pub fn as_bool(&self) -> Option<bool> {
		match self {
			Value::Bool(b) => Some(*b),
			_ => None,
		}
	}
	/// If the `Value` is an integer, represent it as `IntVal`. Returns None
	/// otherwise.
	pub fn as_int(&self) -> Option<IntVal> {
		match self {
			Value::Int(i) => Some(*i),
			_ => None,
		}
	}
}

impl Display for Value {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match self {
			Value::Bool(b) => write!(f, "{b}"),
			Value::Int(i) => write!(f, "{i}"),
		}
	}
}

impl From<BoolView> for View {
	fn from(value: BoolView) -> Self {
		Self::Bool(value)
	}
}

impl From<IntView> for View {
	fn from(value: IntView) -> Self {
		Self::Int(value)
	}
}
