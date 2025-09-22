//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use std::{
	collections::HashSet,
	error::Error,
	fmt::{self, Display},
};

use index_vec::{define_index_type, IndexVec};
use pindakaas::{
	propositional_logic::{Formula, TseitinEncoder},
	solver::propagation::ExternalPropagation,
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit as RawLit, Unsatisfiable,
};
use rangelist::IntervalIterator;

use crate::{
	actions::{
		DecisionActions, InspectionActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions, TrailingActions,
	},
	constraints::{
		bool_array_element::BoolDecisionArrayElement,
		cumulative::Cumulative,
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
		int_value_precede::{IntSeqPrecedeChain, IntValuePrecedeChain},
		BoxedConstraint, BoxedPropagator, Constraint, SimplificationStatus,
	},
	helpers::linear_transform::LinearTransform,
	solver::{
		activation_list::IntPropCond,
		engine::PropRef,
		int_var::{EncodingType, IntVar, IntVarRef},
		queue::PriorityLevel,
		trail::TrailedInt,
		BoolView, BoolViewInner, IntView, IntViewInner, View,
	},
	BoolDecision, BoolFormula, Decision, IntDecision, IntEq, IntLitMeaning, IntSetVal, IntVal,
	Model, Solver,
};
use crate::actions::BrancherInitActions;
use crate::branchers::BoxedBrancher;
use crate::constraints::difference_logic::DifferenceLogicModel;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Definition of an Boolean decision variable in a [`Model`].
pub(crate) struct BoolDecisionDef {
	/// Whether the Boolean variable has already been assigned a value, or has
	/// been aliased to another variable.
	pub(crate) alias: Option<BoolDecision>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<usize>,
}

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
	/// Whether an integer is equal to a constant.
	IntEq(IntDecisionIndex, IntVal),
	/// Whether an integer is greater or equal to a constant.
	IntGreaterEq(IntDecisionIndex, IntVal),
	/// Whether an integer is less than a constant.
	IntLess(IntDecisionIndex, IntVal),
	/// Whether an integer is not equal to a constant.
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
	Cumulative(Cumulative),
	DisjunctiveStrict(DisjunctiveStrict),
	IntAbs(IntAbs),
	IntAllDifferent(IntAllDifferent),
	IntArrayMinimum(IntArrayMinimum),
	IntDecisionArrayElement(IntDecisionArrayElement),
	IntDiv(IntDiv),
	IntEq(IntEq),
	IntInSetReif(IntInSetReif),
	IntLinear(IntLinear),
	IntPow(IntPow),
	IntSeqPrecedeChain(IntSeqPrecedeChain),
	IntTable(IntTable),
	IntTimes(IntTimes),
	IntValArrayElement(IntValArrayElement),
	IntValuePrecedeChain(IntValuePrecedeChain),
	DifferenceLogic(DifferenceLogicModel),
	Other(BoxedConstraint),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Wrapper type to distinguish between a variable with a domain, and an alias
/// to another variable.
pub(crate) enum Domain<E, Alias> {
	/// A normal variable with a domain.
	Domain(E),
	/// An alias to another variable.
	Alias(Alias),
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
/// Configuration object for the reformulation process of creating a [`Solver`]
/// object from a [`crate::Model`].
pub struct InitConfig {
	/// Whether to enable the globally blocked clause elimination (conditioning)
	conditioning: bool,
	/// Whether to enable inprocessing in the oracle solver.
	inprocessing: bool,
	/// The maximum cardinality of the domain of an integer variable before its
	/// order encoding is created lazily.
	int_eager_limit: Option<usize>,
	/// The number of preprocessing rounds in the oracle solver
	preprocessing: Option<usize>,
	/// Whether to enable the failed literal probing in the oracle solver.
	probing: bool,
	/// Whether to enable restarts in the oracle solver.
	restart: bool,
	/// Whether to enable the global forward subsumption in the oracle solver.
	subsumption: bool,
	/// Whether to enable the bounded variable elimination in the oracle solver.
	variable_elimination: bool,
	/// Whether to enable the vivification in the oracle solver.
	vivification: bool,
	/// Difference logic mode.
	pub(crate) diff_logic: u32,
	/// Difference logic priority for bound propagation.
	pub(crate) diff_logic_prio_bounds: u8,
	/// Difference logic priority for boolean propagation.
	pub(crate) diff_logic_prio_bools: u8,
	/// Whether to use inc_imp to check implied booleans proactively.
	pub(crate) diff_logic_inc_imp: bool,
	/// Difference logic priority for boolean propagation.
	pub(crate) diff_logic_branching: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Definition of an integer decision variable in a [`Model`].
pub(crate) struct IntDecisionDef {
	/// The set of possible values that the variable can take.
	pub(crate) domain: Domain<IntSetVal, IntDecision>,
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

#[derive(Debug, PartialEq, Eq)]
/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`crate::Model`].
pub enum ReformulationError {
	/// Error used when the problem is found to be unsatisfiable without
	/// requiring any search.
	TrivialUnsatisfiable,
}

/// A reformulation helper that maps decisions in a [`Model`] objects to the
/// [`View`] that is used to represent it in a [`Solver`] object.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct ReformulationMap {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<BoolView>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: IndexVec<IntDecisionIndex, IntView>,
}

/// Helper type to create a [`ReformulationMap`] object.
///
/// This type is primiraly meant to resolve the order of creation issue when
/// dealing with aliased variables.
pub(crate) struct ReformulationMapBuilder {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<Option<BoolView>>,
	/// Set of integer decision for which the direct encoding should be created
	/// eagerly.
	pub(crate) int_eager_direct: HashSet<IntDecisionIndex>,
	/// The (default) maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub(crate) int_eager_limit: usize,
	/// Set of integer decision for which the order encoding should be created
	/// eagerly.
	pub(crate) int_eager_order: HashSet<IntDecisionIndex>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: IndexVec<IntDecisionIndex, Option<IntView>>,
}

impl<S: SimplificationActions> Constraint<S> for BoolFormula {
	fn simplify(&mut self, _: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
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
	pub(crate) fn to_solver<Oracle: ExternalPropagation>(
		&mut self,
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
			ConstraintStore::Cumulative(con) => {
				<Cumulative as Constraint<Model>>::to_solver(con, &mut actions)
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
			ConstraintStore::IntEq(con) => {
				<IntEq as Constraint<Model>>::to_solver(con, &mut actions)
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
			ConstraintStore::IntSeqPrecedeChain(con) => {
				<IntSeqPrecedeChain as Constraint<Model>>::to_solver(con, &mut actions)
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
			ConstraintStore::IntValuePrecedeChain(con) => {
				<IntValuePrecedeChain as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::DifferenceLogic(con) => {
				<DifferenceLogicModel as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::Other(con) => con.to_solver(&mut actions),
		}
	}
}

impl InitConfig {
	/// The default maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;

	/// Get the default number of preprocessing rounds in the oracle solver.
	pub const DEFAULT_PREPROCESSING: usize = 0;

	/// Get whether to enable the globally blocked clause elimination
	/// (conditioning) in the oracle solver.
	pub fn conditioning(&self) -> bool {
		self.conditioning
	}

	/// Get whether to enable inprocessing in the oracle solver.
	pub fn inprocessing(&self) -> bool {
		self.inprocessing
	}

	/// Get the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn int_eager_limit(&self) -> usize {
		self.int_eager_limit
			.unwrap_or(Self::DEFAULT_INT_EAGER_LIMIT)
	}

	/// Get whether to enable preprocessing in the oracle solver.
	pub fn preprocessing(&self) -> usize {
		self.preprocessing.unwrap_or(Self::DEFAULT_PREPROCESSING)
	}

	/// Get whether to enable the failed literal probing in the oracle solver.
	pub fn probing(&self) -> bool {
		self.probing
	}

	/// Get whether to enable restarts in the oracle solver.
	pub fn restart(&self) -> bool {
		self.restart
	}

	/// Get whether to enable the global forward subsumption in the oracle
	/// solver.
	pub fn subsumption(&self) -> bool {
		self.subsumption
	}

	/// Get whether to enable the bounded variable elimination in the oracle
	/// solver.
	pub fn variable_elimination(&self) -> bool {
		self.variable_elimination
	}

	/// Get whether to enable the vivification in the oracle solver.
	pub fn vivification(&self) -> bool {
		self.vivification
	}

	/// Change whether to enable the globally blocked clause elimination
	/// (conditioning) in the oracle solver.
	pub fn with_conditioning(mut self, conditioning: bool) -> Self {
		self.conditioning = conditioning;
		self
	}

	/// Change whether to enable inprocessing in the oracle solver.
	pub fn with_inprocessing(mut self, inprocessing: bool) -> Self {
		self.inprocessing = inprocessing;
		self
	}

	/// Change the maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub fn with_int_eager_limit(mut self, limit: usize) -> Self {
		self.int_eager_limit = Some(limit);
		self
	}

	/// Change the number of preprocessing rounds in the oracle solver.
	pub fn with_preprocessing(mut self, preprocessing: usize) -> Self {
		self.preprocessing = Some(preprocessing);
		self
	}

	/// Change whether to enable the failed literal probing in the oracle
	/// solver.
	pub fn with_probing(mut self, probing: bool) -> Self {
		self.probing = probing;
		self
	}

	/// Change whether to enable restarts in the oracle solver.
	pub fn with_restart(mut self, restart: bool) -> Self {
		self.restart = restart;
		self
	}

	/// Change whether to enable the global forward subsumption in the oracle
	/// solver.
	pub fn with_subsumption(mut self, subsumption: bool) -> Self {
		self.subsumption = subsumption;
		self
	}

	/// Change whether to enable the bounded variable elimination in the oracle
	/// solver.
	pub fn with_variable_elimination(mut self, variable_elimination: bool) -> Self {
		self.variable_elimination = variable_elimination;
		self
	}

	/// Change whether to enable the vivification in the oracle solver.
	pub fn with_vivification(mut self, vivification: bool) -> Self {
		self.vivification = vivification;
		self
	}

	/// Change the difference logic mode in the oracle solver.
	pub fn with_diff_logic(mut self, diff_logic: Option<u32>,
						   diff_logic_prio_bounds: Option<u8>,
						   diff_logic_prio_bools: Option<u8>,
						   diff_logic_inc_imp: bool, 
						   diff_logic_branching: Option<u8>) -> Self {
		self.diff_logic = diff_logic.unwrap_or(0);
		self.diff_logic_prio_bounds = diff_logic_prio_bounds.unwrap_or(1);
		self.diff_logic_prio_bools = diff_logic_prio_bools.unwrap_or(1);
		self.diff_logic_inc_imp = diff_logic_inc_imp;
		self.diff_logic_branching = diff_logic_branching.unwrap_or(0);
		self
	}

}

impl IntDecisionDef {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSetVal) -> Self {
		Self {
			domain: Domain::Domain(dom),
			constraints: Vec::new(),
		}
	}
}

impl ClauseDatabase for ReformulationContext<'_> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		self.slv.add_clause_from_slice(clause)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.slv.new_var_range(len)
	}
}

impl DecisionActions for ReformulationContext<'_> {
	fn get_intref_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView {
		self.slv.get_intref_lit(var, meaning)
	}

	fn get_num_conflicts(&self) -> u64 {
		self.slv.get_num_conflicts()
	}
}

impl InspectionActions for ReformulationContext<'_> {
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		self.slv.check_int_in_domain(var, val)
	}

	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		self.slv.get_int_lower_bound(var)
	}

	fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		self.slv.get_int_upper_bound(var)
	}
}

impl BrancherInitActions for ReformulationContext<'_> {
	fn ensure_decidable(&mut self, view: View) {
		self.slv.ensure_decidable(view);
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.slv.new_trailed_int(init)
	}

	fn push_brancher(&mut self, brancher: BoxedBrancher) {
		self.slv.push_brancher(brancher);
	}
}

impl PropagatorInitActions for ReformulationContext<'_> {
	fn add_propagator(&mut self, propagator: BoxedPropagator, priority: PriorityLevel) -> PropRef {
		self.slv.add_propagator(propagator, priority)
	}

	fn advise_on_backtrack(&mut self, prop: PropRef) {
		self.slv.advise_on_backtrack(prop);
	}

	fn advise_on_bool_change(&mut self, prop: PropRef, var: BoolView, data: u64) {
		self.slv.advise_on_bool_change(prop, var, data);
	}

	fn advise_on_int_change(
		&mut self,
		prop: PropRef,
		var: IntView,
		condition: IntPropCond,
		data: u64,
	) {
		self.slv.advise_on_int_change(prop, var, condition, data);
	}

	fn enqueue_now(&mut self, prop: PropRef) {
		self.slv.enqueue_now(prop);
	}

	fn enqueue_on_bool_change(&mut self, prop: PropRef, var: BoolView) {
		self.slv.enqueue_on_bool_change(prop, var);
	}

	fn enqueue_on_int_change(&mut self, prop: PropRef, var: IntView, condition: IntPropCond) {
		self.slv.enqueue_on_int_change(prop, var, condition);
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
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		self.slv.get_bool_val(bv)
	}

	fn get_trailed_int(&self, i: TrailedInt) -> IntVal {
		self.slv.get_trailed_int(i)
	}

	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal {
		self.slv.set_trailed_int(i, v)
	}
}

impl Display for ReformulationError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::TrivialUnsatisfiable => write!(f, "The problem is trivially unsatisfiable"),
		}
	}
}

impl Error for ReformulationError {}

impl From<Unsatisfiable> for ReformulationError {
	fn from(_: Unsatisfiable) -> Self {
		Self::TrivialUnsatisfiable
	}
}

impl ReformulationMap {
	/// Lookup the [`SolverView`] to which the given model [`ModelView`] maps.
	pub fn get<Oracle: ExternalPropagation>(
		&self,
		slv: &mut Solver<Oracle>,
		index: &Decision,
	) -> View {
		match index {
			Decision::Bool(b) => View::Bool(self.get_bool(slv, *b)),
			Decision::Int(i) => View::Int(self.get_int(slv, *i)),
		}
	}

	/// Lookup the solver [`BoolView`] to which the given model
	/// [`bool::BoolView`] maps.
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

impl ReformulationMapBuilder {
	/// Create the [`ReformulationMap`] object ensuring that all variables have
	/// a representation in the [`Solver`].
	pub(crate) fn finalize(self) -> ReformulationMap {
		ReformulationMap {
			bool_map: self
				.bool_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
			int_map: self
				.int_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
		}
	}

	/// Get the representation of a Boolean decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (toghether with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_bool<Oracle: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Oracle>,
		bv: BoolDecision,
	) -> BoolView {
		use BoolDecisionInner::*;
		match bv.0 {
			Lit(lit) => {
				let idx = Into::<i32>::into(lit.var()) as usize - 1;
				if let Some(v) = self.bool_map[idx] {
					return if lit.is_negated() { !v } else { v };
				}
				let def = &model.bool_vars[idx];
				let view = match def.alias {
					Some(alias) => self.get_or_create_bool(model, slv, alias),
					None => {
						let v = slv.new_lit();
						BoolView(BoolViewInner::Lit(v))
					}
				};
				self.bool_map[idx] = Some(view);
				view
			}
			Const(b) => b.into(),
			IntEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				slv.get_int_lit(iv, IntLitMeaning::Eq(val))
			}
			IntGreaterEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				slv.get_int_lit(iv, IntLitMeaning::GreaterEq(val))
			}
			IntLess(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				slv.get_int_lit(iv, IntLitMeaning::Less(val))
			}
			IntNotEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				slv.get_int_lit(iv, IntLitMeaning::NotEq(val))
			}
		}
	}

	/// Get the representation of a Integer decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (toghether with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_int<Oracle: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Oracle>,
		iv: IntDecisionIndex,
	) -> IntView {
		use IntDecisionInner::*;

		if let Some(v) = self.int_map[iv] {
			return v;
		}

		let def = &model.int_vars[iv];
		let view = match &def.domain {
			Domain::Domain(dom) => {
				let direct_enc = if self.int_eager_direct.contains(&iv) {
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				let card = dom.card();
				let order_enc = if self.int_eager_order.contains(&iv)
					|| self.int_eager_direct.contains(&iv)
					|| card.is_some() && card.unwrap() <= self.int_eager_limit
				{
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				IntVar::new_in(slv, dom.clone(), order_enc, direct_enc)
			}
			Domain::Alias(alias) => match alias.0 {
				Var(idx) => self.get_or_create_int(model, slv, idx),
				Const(c) => c.into(),
				Linear(lt, idx) => {
					let iv = self.get_or_create_int(model, slv, idx);
					iv * lt.scale + lt.offset
				}
				Bool(lt, bv) => {
					let bv = self.get_or_create_bool(model, slv, bv);
					bv * lt.scale.get() + lt.offset
				}
			},
		};

		self.int_map[iv] = Some(view);
		view
	}
}

define_index_type! {
	/// Reference type for integer decision variables in a [`Model`].
	pub(crate) struct IntDecisionIndex = u32;
}
