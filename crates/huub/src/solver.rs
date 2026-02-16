//! Module containing the central solving infrastructure.

pub(crate) mod activation_list;
pub(crate) mod bool_to_int;
pub mod branchers;
pub(crate) mod decision;
pub(crate) mod engine;
pub(crate) mod initialization_context;
pub(crate) mod queue;
pub(crate) mod solution;
pub(crate) mod solving_context;
pub(crate) mod trail;
pub(crate) mod view;

use std::{
	any::Any,
	cell::{RefCell, RefMut},
	fmt::Debug,
	hash::Hash,
	mem,
	ops::{Add, AddAssign, Not},
	rc::Rc,
};

use itertools::Itertools;
use pindakaas::{
	ClauseDatabase, ClauseDatabaseTools, Lit as RawLit, Unsatisfiable,
	solver::{
		Assumptions, FailedAssumptions, LearnCallback, SolveResult as SatSolveResult,
		TerminateCallback,
		cadical::Cadical,
		propagation::{ExternalPropagation, SolvingActions},
	},
};
use tracing::debug;

pub use crate::solver::{
	decision::{Decision, DecisionReference},
	solution::{AnyView, BoolValuation, IntValuation, Solution, Value},
	view::{DefaultView, View, boolean::BoolView, integer::IntView},
};
use crate::{
	Clause, Goal, IntVal, TerminationSignal,
	actions::{
		BrancherInitActions, ConstructionActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, PostingActions, ReasoningContext, ReasoningEngine, Trailed,
		TrailingActions,
	},
	constraints::{BoxedPropagator, Conflict},
	helpers::bytes::Bytes,
	solver::{
		branchers::BoxedBrancher,
		engine::{Engine, PropRef},
		initialization_context::InitializationContext,
		queue::PropagatorInfo,
	},
	views::LinearBoolView,
};

/// Trait implemented by the object given to the callback on detecting failure
pub trait AssumptionChecker {
	/// Check if the given assumption literal was used to prove the
	/// unsatisfiability of the formula under the assumptions used for the last
	/// SAT search.
	///
	/// Note that for literals 'bv' which are not assumption literals, the
	/// behavior of is not specified.
	fn fail(&self, bv: View<bool>) -> bool;
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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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

/// An assumption checker that can be used when no assumptions are used.
///
/// Note that this checker will always return false.
pub(crate) struct NoAssumptions;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// Structure capturing statistical information about the search performed by
/// the solver instance.
pub struct SearchStatistics {
	/// Number of conflicts encountered
	pub(crate) conflicts: u64,
	/// Number of search decisions left to the SAT solver
	pub(crate) sat_decisions: u64,
	/// Peak search depth
	pub(crate) peak_depth: u32,
	/// Number of times a CP propagator was called
	pub(crate) propagations: u64,
	/// Number of backtracks to level 0
	pub(crate) restarts: u32,
	/// Number of decisions following the user-specified search heuristics
	pub(crate) user_decisions: u64,
}

#[derive(Debug)]
/// The main solver object that is used to interact with the LCG solver.
pub struct Solver<Sat = Cadical> {
	/// The SAT solver that has been connected to [`Self::engine`] to perform
	/// external propagation.
	pub(crate) sat: Sat,
	/// A reference to the [`Engine`] instance that is connected to
	/// [`Self::sat`].
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Result of a solving attempt
pub enum Status {
	/// The solver has found a solution.
	Satisfied,
	/// The solver has proven that the problem is unsatisfiable.
	Unsatisfiable,
	/// The solver that no more/better solutions can be found.
	Complete,
	/// The solver was interrupted before a result could be reached.
	Unknown,
}

/// Helper function that calls [`tracing::debug!`] on learned clauses.
///
/// This function is used as part of the callback given to the SAT solver.
fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

impl<A: FailedAssumptions> AssumptionChecker for A {
	fn fail(&self, bv: View<bool>) -> bool {
		match bv.0 {
			BoolView::Lit(lit) => self.fail(lit.0),
			BoolView::Const(false) => true,
			BoolView::Const(true) => false,
		}
	}
}

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
	) -> Vec<Clause<RawLit>> {
		let mut ret = Vec::<Clause<RawLit>>::new();
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

impl AssumptionChecker for NoAssumptions {
	fn fail(&self, bv: View<bool>) -> bool {
		matches!(bv.0, BoolView::Const(false))
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

	/// Returns the peak depth of the search tree.
	pub fn peak_depth(&self) -> u32 {
		self.peak_depth
	}

	/// Returns the number of times the search was restarted by the SAT
	/// solver.
	pub fn restarts(&self) -> u32 {
		self.restarts
	}

	/// Return the number of search decisions that was left to the SAT
	/// solver.
	pub fn sat_decisions(&self) -> u64 {
		self.sat_decisions
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
		self.sat_decisions += other.sat_decisions;
		self.peak_depth = self.peak_depth.max(other.peak_depth);
		self.propagations += other.propagations;
		self.restarts += other.restarts;
		self.user_decisions += other.user_decisions;
	}
}

impl<Sat: ClauseDatabase> Solver<Sat> {
	/// Add a clause to the solver
	pub fn add_clause<Iter>(
		&mut self,
		clause: Iter,
	) -> Result<(), <Self as ReasoningContext>::Conflict>
	where
		Iter: IntoIterator,
		Iter::Item: Into<View<bool>>,
	{
		let clause = clause.into_iter().map(Into::into).collect_vec();
		match ClauseDatabaseTools::add_clause(&mut self.sat, clause.clone()) {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => Err(Conflict::new(
				self,
				None,
				clause.into_iter().map(|l| !l).collect_vec(),
			)),
		}
	}
}

impl<Sat: ExternalPropagation + Assumptions> Solver<Sat> {
	/// Try and find a solution to the problem for which the Solver was
	/// initialized, given a list of Boolean assumptions.
	pub fn solve_assuming(
		&mut self,
		assumptions: impl IntoIterator<Item = View<bool>>,
		mut on_sol: impl FnMut(Solution<'_>),
		on_fail: impl FnOnce(&dyn AssumptionChecker),
	) -> Status {
		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assumptions
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => None,
				BoolView::Const(false) => Some(Err(())),
			})
			.collect()
		else {
			on_fail(&NoAssumptions);
			return Status::Unsatisfiable;
		};

		let result = self.sat.solve_assuming(assumptions);
		match result {
			SatSolveResult::Satisfied(value) => {
				let sol = Solution {
					sat: &value,
					state: &self.engine.borrow().state,
				};
				on_sol(sol);
				Status::Satisfied
			}
			SatSolveResult::Unsatisfiable(fail) => {
				on_fail(&fail);
				Status::Unsatisfiable
			}
			SatSolveResult::Unknown => Status::Unknown,
		}
	}
}

impl<Sat: ExternalPropagation> Solver<Sat> {
	#[doc(hidden)]
	/// Method used to add a no-good clause from a solution. This clause can be
	/// used to ensure that the same solution is not found again.
	///
	/// ## Warning
	/// This method will panic if the number of variables and values do not
	/// match.
	pub fn add_no_good(
		&mut self,
		vars: &[AnyView],
		vals: &[Value],
	) -> Result<(), <Self as ReasoningContext>::Conflict> {
		let clause = vars
			.iter()
			.zip_eq(vals)
			.map(|(var, val)| match *var {
				AnyView::Bool(bv) => match val {
					Value::Bool(true) => !bv,
					Value::Bool(false) => bv,
					_ => unreachable!(),
				},
				AnyView::Int(iv) => {
					let Value::Int(val) = val.clone() else {
						unreachable!()
					};
					iv.lit(self, IntLitMeaning::NotEq(val))
				}
			})
			.collect_vec();
		debug!(clause = ?clause.iter().filter_map(|&x| if let BoolView::Lit(x) = x.0 { Some(i32::from(x.0)) } else { None }).collect::<Vec<i32>>(), "add solution nogood");
		self.add_clause(clause)
	}

	/// Add a constraint propagator to the solver to enforce a constraint.
	pub(crate) fn add_propagator(&mut self, propagator: BoxedPropagator, from_model: bool) {
		let mut handle = self.engine.borrow_mut();
		let engine = &mut *handle;
		engine.propagators.push(propagator);
		let prop_ref = PropRef::new(engine.propagators.len() - 1);
		let mut ctx = InitializationContext::new(&mut engine.state, prop_ref);
		engine.propagators[prop_ref.index()].initialize(&mut ctx);
		let priority = ctx.priority();
		let enqueue = ctx.enqueue(from_model);
		let new_observed = mem::take(&mut ctx.observed_variables);
		engine.state.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(
			prop_ref.index(),
			engine.state.propagator_queue.info.len() - 1
		);
		if enqueue {
			engine
				.state
				.propagator_queue
				.enqueue_propagator(prop_ref.raw());
		}
		drop(handle);
		for v in new_observed {
			// Ensure that the trail has a space to track the literal
			{
				self.engine.borrow_mut().state.trail.grow_to_boolvar(v);
			}
			// Ensure the SAT solver knows the literal is observed.
			self.sat.add_observed_var(v);
		}
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
		vars: &[AnyView],
		mut on_sol: impl FnMut(Solution<'_>),
	) -> (Status, SearchStatistics) {
		use Status::*;

		let ret = |x: Self, status: Status| (status, x.search_statistics());

		let mut num_sol = 0;
		loop {
			let mut vals = Vec::with_capacity(vars.len());
			let status = self.solve(|sol| {
				num_sol += 1;
				for v in vars {
					vals.push(v.val(sol));
				}
				on_sol(sol);
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

	/// Split the solver into an solving actions objects (limiting the
	/// interaction with the SAT) and the dynamic engine reference.
	fn as_parts_mut(&mut self) -> (impl SolvingActions + '_, RefMut<'_, Engine>) {
		struct SA<'a, O>(&'a mut O);
		impl<O: ExternalPropagation> SolvingActions for SA<'_, O> {
			fn is_decision(&mut self, _: RawLit) -> bool {
				false
			}
			fn new_observed_var(&mut self) -> pindakaas::Var {
				self.0.new_observed_var()
			}
			fn phase(&mut self, lit: RawLit) {
				self.0.phase(lit);
			}
			fn unphase(&mut self, lit: RawLit) {
				self.0.unphase(lit);
			}
		}

		(SA(&mut self.sat), self.engine.borrow_mut())
	}

	/// Find an optimal solution with regards to the given objective and goal.
	///
	/// Note that this method uses assumptions iteratively increase the lower
	/// bound of the objective. This does not impact the state of the solver
	/// for continued use.
	pub fn branch_and_bound(
		mut self,
		goal: Goal<View<IntVal>>,
		mut on_sol: impl FnMut(Solution<'_>),
	) -> (Status, SearchStatistics, Option<IntVal>) {
		use Status::*;
		let ret =
			|x: Self, status: Status, obj: Option<IntVal>| (status, x.search_statistics(), obj);

		let mut obj_curr = None;
		let (obj_bound, objective) = match goal {
			Goal::Minimize(objective) => (objective.min(&self), objective),
			Goal::Maximize(objective) => (objective.max(&self), objective),
		};
		debug!(obj_bound, "start branch and bound");
		loop {
			let status = self.solve(|sol| {
				obj_curr = Some(IntValuation::val(&objective, sol));
				on_sol(sol);
			});
			debug!(?status, ?obj_curr, obj_bound, ?goal, "SAT solve result");
			match status {
				Satisfied => {
					if obj_curr == Some(obj_bound) {
						return ret(self, Complete, obj_curr);
					} else {
						let bound_lit = match goal {
							Goal::Minimize(_) => Some(
								objective.lit(&mut self, IntLitMeaning::Less(obj_curr.unwrap())),
							),
							Goal::Maximize(_) => {
								Some(objective.lit(
									&mut self,
									IntLitMeaning::GreaterEq(obj_curr.unwrap() + 1),
								))
							}
						};
						debug!(
							lit = i32::from({
								let BoolView::Lit(l) = bound_lit.unwrap().0 else {
									unreachable!()
								};
								l.0
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
					};
				}
				Complete => unreachable!(),
			}
		}
	}

	/// Wrapper function for `all_solutions` that collects all solutions and
	/// returns them in a vector of solution values.
	///
	/// WARNING: This method will add additional clauses into the solver to
	/// prevent the same solution from being generated twice. This will make
	/// repeated use of the Solver object impossible. Note that you can clone
	/// the Solver object before calling this method to work around this
	/// limitation.
	pub fn collect_all_solutions(
		self,
		vars: &[AnyView],
	) -> (Status, SearchStatistics, Vec<Vec<Value>>) {
		let mut solutions = Vec::new();
		let (status, stats) = self.all_solutions(vars, |sol| {
			let mut sol_vec = Vec::with_capacity(vars.len());
			for v in vars {
				sol_vec.push(v.val(sol));
			}
			solutions.push(sol_vec);
		});
		(status, stats, solutions)
	}

	/// Access the initialization statistics of the [`Solver`] object.
	pub fn init_statistics(&self) -> InitStatistics {
		InitStatistics {
			int_vars: self.engine.borrow().state.int_vars.len(),
			propagators: self.engine.borrow().propagators.len(),
		}
	}

	/// Create a new Boolean decision variable in the solver.
	pub fn new_bool_decision(&mut self) -> Decision<bool> {
		let lit = self.sat.new_lit();
		Decision(lit)
	}

	/// Access the search statistics for the search process up to this point.
	pub fn search_statistics(&self) -> SearchStatistics {
		let cp_stats = &self.engine.borrow().state.statistics;
		SearchStatistics {
			conflicts: cp_stats.conflicts,
			sat_decisions: cp_stats.sat_decisions,
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
	pub fn solve(&mut self, mut on_sol: impl FnMut(Solution<'_>)) -> Status {
		let result = self.sat.solve();
		match result {
			SatSolveResult::Satisfied(value) => {
				let sol = Solution {
					sat: &value,
					state: &self.engine.borrow().state,
				};
				on_sol(sol);
				Status::Satisfied
			}
			SatSolveResult::Unsatisfiable(_) => Status::Unsatisfiable,
			SatSolveResult::Unknown => Status::Unknown,
		}
	}
}

impl<Sat: TerminateCallback> Solver<Sat> {
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
	pub fn set_terminate_callback<F: FnMut() -> TerminationSignal + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		self.sat.set_terminate_callback(cb);
	}
}

impl<Sat: LearnCallback> Solver<Sat> {
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
			self.sat
				.set_learn_callback(Some(move |clause: &mut dyn Iterator<Item = RawLit>| {
					trace_learned_clause(clause);
					f(clause);
				}));
		} else {
			self.sat.set_learn_callback(Some(trace_learned_clause));
		}
	}
}

impl<Sat: ExternalPropagation> BrancherInitActions for Solver<Sat> {
	fn ensure_decidable<T: DefaultView>(&mut self, view: impl Into<View<T>>) {
		let view: View<T> = view.into();
		let any: &dyn Any = &view;
		if let Some(view) = any.downcast_ref::<View<bool>>() {
			match view.0 {
				BoolView::Lit(var) => {
					let var = var.0.var();
					self.engine.borrow_mut().state.trail.grow_to_boolvar(var);
					self.sat.add_observed_var(var);
				}
				BoolView::Const(_) => {}
			}
		} else if let Some(view) = any.downcast_ref::<View<IntVal>>() {
			match view.0 {
				IntView::Bool(LinearBoolView { var, .. }) => {
					let var = var.0.var();
					self.engine.borrow_mut().state.trail.grow_to_boolvar(var);
					self.sat.add_observed_var(var);
				}
				_ => {
					// Nothing has to happened for constants and all literals
					// for integer variables are already marked as
					// observed.
				}
			}
		} else {
			unreachable!()
		}
	}

	fn push_brancher(&mut self, brancher: BoxedBrancher) {
		self.engine.borrow_mut().branchers.push(brancher);
	}
}

impl Clone for Solver<Cadical> {
	fn clone(&self) -> Self {
		let mut sat = self.sat.shallow_clone();
		let engine: Engine = self.engine.borrow().clone();
		let engine = Rc::new(RefCell::new(engine));
		sat.connect_propagator(Rc::clone(&engine));
		for var in sat.emitted_vars() {
			if self.sat.is_observed(var.into()) {
				sat.add_observed_var(var);
			}
		}
		Solver { sat, engine }
	}
}

impl<Sat: ExternalPropagation> ConstructionActions for Solver<Sat> {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		self.engine.borrow_mut().state.trail.track(init)
	}
}

impl<Sat: ExternalPropagation> DecisionActions for Solver<Sat> {
	fn num_conflicts(&self) -> u64 {
		self.engine.borrow().state.statistics.conflicts
	}
}

impl<Sat: Default + ExternalPropagation + LearnCallback> Default for Solver<Sat> {
	fn default() -> Self {
		let mut sat = Sat::default();
		let engine = Rc::default();
		sat.set_learn_callback(Some(trace_learned_clause));
		sat.connect_propagator(Rc::clone(&engine));
		Self { sat, engine }
	}
}

impl<Sat: ExternalPropagation> PostingActions for Solver<Sat> {
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict> {
		Solver::add_clause(self, clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.add_propagator(propagator, false);
	}
}

impl<Sat> ReasoningContext for Solver<Sat> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl<Sat> TrailingActions for Solver<Sat> {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		self.engine.borrow_mut().state.set_trailed(i, v)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		self.engine.borrow().state.trailed(i)
	}
}
