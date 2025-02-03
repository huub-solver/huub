//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use delegate::delegate;
use index_vec::{define_index_type, IndexVec};
use pindakaas::{
	propositional_logic::{Formula, TseitinEncoder},
	solver::propagation::PropagatingSolver,
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit as RawLit, Unsatisfiable,
};
use thiserror::Error;

use crate::{
	actions::{
		DecisionActions, InspectionActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions, TrailingActions,
	},
	constraints::{
		bool_array_element::BoolDecisionArrayElement,
		disjunctive_strict::DisjunctiveStrict,
		int_abs::IntAbs,
		int_all_different::IntAllDifferent,
		int_array_element::{IntDecisionArrayElement, IntValArrayElement},
		int_array_minimum::IntArrayMinimum,
		int_div::IntDiv,
		int_in_set::IntInSetReif,
		int_linear::IntLinear,
		int_pow::IntPow,
		int_table::IntTable,
		int_times::IntTimes,
		BoxedConstraint, BoxedPropagator, Constraint, SimplificationStatus,
	},
	helpers::linear_transform::LinearTransform,
	solver::{
		activation_list::IntPropCond,
		engine::{Engine, PropRef},
		int_var::IntVarRef,
		queue::PriorityLevel,
		trail::TrailedInt,
		BoolView, BoolViewInner, IntView, IntViewInner, View,
	},
	BoolDecision, BoolFormula, Decision, IntDecision, IntLitMeaning, IntSetVal, IntVal, Model,
	Solver,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
/// Inner storage for [`BoolDecision`], kept private to prevent access from
/// users.
pub(crate) enum BoolDecisionInner {
	/// A Boolean decision variable or its negation.
	Lit(RawLit),
	/// A constant Boolean value.
	Const(bool),
	/// Wether an integer is equal to a constant.
	IntEq(IntDecisionIndex, IntVal),
	/// Wether an integer is greater or equal to a constant.
	IntGreaterEq(IntDecisionIndex, IntVal),
	/// Wether an integer is less than a constant.
	IntLess(IntDecisionIndex, IntVal),
	/// Wether an integer is not equal to a constant.
	IntNotEq(IntDecisionIndex, IntVal),
}

#[allow(
	clippy::missing_docs_in_private_items,
	reason = "constraints are generally documented on their own types"
)]
#[derive(Clone, Debug)]
/// An disambiguation of the different constraints objects that can be used in a
/// [`Model`] object.
///
/// This enum type is used to store and analyze the constraints in a [`Model`].
pub(crate) enum ConstraintStore {
	BoolDecisionArrayElement(BoolDecisionArrayElement),
	BoolFormula(BoolFormula),
	DisjunctiveStrict(DisjunctiveStrict),
	IntAbs(IntAbs),
	IntAllDifferent(IntAllDifferent),
	IntArrayMinimum(IntArrayMinimum),
	IntDecisionArrayElement(IntDecisionArrayElement),
	IntDiv(IntDiv),
	IntInSetReif(IntInSetReif),
	IntLinear(IntLinear),
	IntPow(IntPow),
	IntTable(IntTable),
	IntTimes(IntTimes),
	IntValArrayElement(IntValArrayElement),
	Other(BoxedConstraint),
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
/// Configuration object for the reformulation process of creating a [`Solver`]
/// object from a [`crate::Model`].
pub struct InitConfig {
	/// The maximum cardinality of the domain of an integer variable before its
	/// order encoding is created lazily.
	int_eager_limit: Option<usize>,
	/// Whether to enable restarts in the oracle solver.
	restart: bool,
	/// Whether to enable the vivification in the oracle solver.
	vivification: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Definition of an integer decision variable in a [`Model`].
pub(crate) struct IntDecisionDef {
	/// The set of possible values that the variable can take.
	pub(crate) domain: IntSetVal,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// Inner storage for [`IntDecision`], kept private to prevent access from
/// users.
pub(crate) enum IntDecisionInner {
	/// Direct reference to an integer variable.
	Var(IntDecisionIndex),
	/// Constant integer value.
	Const(i64),
	/// Linear transformation of an integer variable.
	Linear(LinearTransform, IntDecisionIndex),
	/// Linear transformation of a Boolean variable.
	Bool(LinearTransform, BoolDecision),
}

/// Context object used during the reformulation process that creates a
/// [`Solver`] object from a [`crate::Model`].
pub(crate) struct ReformulationContext<'a> {
	/// The resulting [`Solver`] object.
	pub(crate) slv: &'a mut dyn PropagatorInitActions,
	/// The mapping from variable in the [`crate::Model`] to the corresponding
	/// view in the [`Solver`].
	pub(crate) map: &'a ReformulationMap,
}

#[derive(Error, Debug, PartialEq, Eq)]
/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`crate::Model`].
pub enum ReformulationError {
	#[error("The problem is trivially unsatisfiable")]
	/// Error used when the problem is found to be unsatisfiable without requiring
	/// any search.
	TrivialUnsatisfiable,
}

/// A reformulation helper that maps decisions in a [`Model`] objects to the
/// [`View`] that is used to represent it in a [`Solver`] object.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct ReformulationMap {
	/// Map of integer decisions to integer views.
	pub(crate) int_map: IndexVec<IntDecisionIndex, IntView>,
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<BoolView>,
}

impl<S: SimplificationActions> Constraint<S> for BoolFormula {
	fn simplify(&mut self, _: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let mut resolver = |bv: BoolDecision| {
			let inner = slv.get_solver_bool(bv);
			match inner.0 {
				BoolViewInner::Const(b) => Err(b),
				BoolViewInner::Lit(l) => Ok(l),
			}
		};
		let result: Result<Formula<RawLit>, _> = self.clone().simplify_with(&mut resolver);
		match result {
			Err(false) => Err(ReformulationError::TrivialUnsatisfiable),
			Err(true) => Ok(()),
			Ok(f) => {
				let mut wrapper = slv.with_conditions(vec![]);
				Ok(TseitinEncoder.encode(&mut wrapper, &f)?)
			}
		}
	}
}

impl ConstraintStore {
	/// Map the constraint into propagators and clauses to be added to the given
	/// solver, using the variable mapping provided.
	pub(crate) fn to_solver<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &ReformulationMap,
	) -> Result<(), ReformulationError> {
		let mut actions = ReformulationContext { slv, map };
		match self {
			ConstraintStore::BoolDecisionArrayElement(con) => {
				<BoolDecisionArrayElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::BoolFormula(exp) => {
				<Formula<BoolDecision> as Constraint<Model>>::to_solver(exp, &mut actions)
			}
			ConstraintStore::DisjunctiveStrict(con) => {
				<DisjunctiveStrict as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntAbs(con) => {
				<IntAbs as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntAllDifferent(con) => {
				<IntAllDifferent as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntArrayMinimum(con) => {
				<IntArrayMinimum as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntDecisionArrayElement(con) => {
				<IntDecisionArrayElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntDiv(con) => {
				<IntDiv as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntInSetReif(con) => {
				<IntInSetReif as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntLinear(con) => {
				<IntLinear as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntPow(con) => {
				<IntPow as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntTable(con) => {
				<IntTable as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntTimes(con) => {
				<IntTimes as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntValArrayElement(con) => {
				<IntValArrayElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::Other(con) => con.to_solver(&mut actions),
		}
	}
}

impl InitConfig {
	/// The default maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;

	/// Get the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn int_eager_limit(&self) -> usize {
		self.int_eager_limit
			.unwrap_or(Self::DEFAULT_INT_EAGER_LIMIT)
	}

	/// Get whether to enable restarts in the oracle solver.
	pub fn restart(&self) -> bool {
		self.restart
	}

	/// Get whether to enable the vivification in the oracle solver.
	pub fn vivification(&self) -> bool {
		self.vivification
	}

	/// Change the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn with_int_eager_limit(mut self, limit: usize) -> Self {
		self.int_eager_limit = Some(limit);
		self
	}

	/// Change whether to enable restarts in the oracle solver.
	pub fn with_restart(mut self, restart: bool) -> Self {
		self.restart = restart;
		self
	}

	/// Change whether to enable the vivification in the oracle solver.
	pub fn with_vivification(mut self, vivification: bool) -> Self {
		self.vivification = vivification;
		self
	}
}

impl IntDecisionDef {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSetVal) -> Self {
		Self {
			domain: dom,
			constraints: Vec::new(),
		}
	}
}

impl ClauseDatabase for ReformulationContext<'_> {
	delegate! {
		to self.slv {
			fn add_clause_from_slice(&mut self, clause: &[RawLit])  -> Result<(), Unsatisfiable>;
			fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange;
		}
	}
}

impl DecisionActions for ReformulationContext<'_> {
	delegate! {
		to self.slv {
			fn get_intref_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView;
			fn get_num_conflicts(&self) -> u64;
		}
	}
}

impl InspectionActions for ReformulationContext<'_> {
	delegate! {
		to self.slv {
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl PropagatorInitActions for ReformulationContext<'_> {
	delegate! {
		to self.slv {
			fn add_propagator(&mut self, propagator: BoxedPropagator, priority: PriorityLevel) -> PropRef;
			fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
			fn enqueue_now(&mut self, prop: PropRef);
			fn enqueue_on_bool_change(&mut self, prop: PropRef, var: BoolView);
			fn enqueue_on_int_change(&mut self, prop: PropRef, var: IntView, condition: IntPropCond);
		}
	}
}

impl ReformulationActions for ReformulationContext<'_> {
	fn get_solver_bool(&mut self, bv: BoolDecision) -> BoolView {
		self.map.get_bool(self.slv, bv)
	}

	fn get_solver_int(&mut self, iv: IntDecision) -> IntView {
		self.map.get_int(self.slv, iv)
	}

	fn new_bool_var(&mut self) -> BoolView {
		BoolView(BoolViewInner::Lit(self.slv.new_lit()))
	}
}

impl TrailingActions for ReformulationContext<'_> {
	delegate! {
		to self.slv {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
			fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

impl From<Unsatisfiable> for ReformulationError {
	fn from(_: Unsatisfiable) -> Self {
		Self::TrivialUnsatisfiable
	}
}

impl ReformulationMap {
	/// Lookup the [`SolverView`] to which the given model [`ModelView`] maps.
	pub fn get<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		index: &Decision,
	) -> View {
		match index {
			Decision::Bool(b) => View::Bool(self.get_bool(slv, *b)),
			Decision::Int(i) => View::Int(self.get_int(slv, *i)),
		}
	}

	/// Lookup the solver [`BoolView`] to which the given model [`bool::BoolView`]
	/// maps.
	pub fn get_bool(&self, slv: &mut dyn PropagatorInitActions, bv: BoolDecision) -> BoolView {
		use BoolDecisionInner::*;

		let get_int_lit = |slv: &mut dyn PropagatorInitActions,
		                   iv: IntDecisionIndex,
		                   lit_meaning: IntLitMeaning| {
			let iv = self.get_int(slv, IntDecision(IntDecisionInner::Var(iv)));
			slv.get_int_lit(iv, lit_meaning)
		};

		match bv.0 {
			Lit(l) => {
				let idx = Into::<i32>::into(l.var()) as usize - 1;
				let bv: BoolView = self.bool_map[idx];
				if l.is_negated() {
					!bv
				} else {
					bv
				}
			}
			Const(c) => c.into(),
			IntEq(v, i) => get_int_lit(slv, v, IntLitMeaning::Eq(i)),
			IntGreaterEq(v, i) => get_int_lit(slv, v, IntLitMeaning::GreaterEq(i)),
			IntLess(v, i) => get_int_lit(slv, v, IntLitMeaning::Less(i)),
			IntNotEq(v, i) => get_int_lit(slv, v, IntLitMeaning::NotEq(i)),
		}
	}

	/// Lookup the solver [`IntView`] to which the given model [`int::IntView`]
	/// maps.
	pub fn get_int(&self, slv: &mut dyn PropagatorInitActions, iv: IntDecision) -> IntView {
		use IntDecisionInner::*;

		match iv.0 {
			Var(i) => self.int_map[i],
			Const(c) => (c).into(),
			Linear(t, i) => self.int_map[i] * t.scale + t.offset,
			Bool(t, bv) => {
				let bv = self.get_bool(slv, bv);
				match bv.0 {
					BoolViewInner::Lit(lit) => IntView(IntViewInner::Bool {
						transformer: t,
						lit,
					}),
					BoolViewInner::Const(b) => t.transform(b as IntVal).into(),
				}
			}
		}
	}
}

define_index_type! {
	/// Reference type for integer decision variables in a [`Model`].
	pub(crate) struct IntDecisionIndex = u32;
}
