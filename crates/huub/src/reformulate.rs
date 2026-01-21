//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use std::{
	error::Error,
	fmt::{self, Display},
	num::NonZero,
	ops::AddAssign,
};

use index_vec::{IndexVec, define_index_type};
use pindakaas::{
	ClauseDatabase, ClauseDatabaseTools, Lit as RawLit, Unsatisfiable,
	propositional_logic::{Formula, TseitinEncoder},
	solver::propagation::ExternalPropagation,
};
use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;

use crate::{
	BoolDecision, BoolFormula, Clause, Decision, IntDecision, IntLitMeaning, IntSetVal, IntVal,
	Model, Solver,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, ConstructionActions,
		DecisionActions, InitActions, IntDecisionActions, IntInspectionActions, PropagationActions,
		ReasoningEngine, ReformulationActions, SimplificationActions, TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelBoolView, Propagator, SimplificationStatus,
		SolverBoolView,
	},
	solver::{
		BoolView, BoolViewInner, IntView, IntViewInner, View,
		activation_list::{ActivationActionS, ActivationList},
		int_var::{EncodingType, IntVar, IntVarRef},
		trail::TrailedInt,
	},
	views::{LinearBoolView, LinearView},
};

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
	pub(crate) constraints: Vec<ActivationActionS>,
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
	/// Whether to enable asking reason eagerly in the oracle solver.
	reason_eager: bool,
	/// Whether to enable the bounded variable elimination in the oracle solver.
	variable_elimination: bool,
	/// Whether to enable the vivification in the oracle solver.
	vivification: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Definition of an integer decision variable in a [`Model`].
pub(crate) struct IntDecisionDef {
	/// The set of possible values that the variable can take.
	pub(crate) domain: Domain<IntSetVal, IntDecision>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: ActivationList,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// The internal representation of [`IntDecision`].
///
/// Note that this representation is not meant to be exposed to the user.
pub(crate) enum IntDecisionInner {
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear(LinearView<NonZero<IntVal>, IntVal, IntDecisionIndex>),
	/// Linear View of an Boolean Literal.
	Bool(LinearBoolView<NonZero<IntVal>, IntVal, BoolDecision>),
}

/// Context object used during the reformulation process that creates a
/// [`Solver`] object from a [`crate::Model`].
pub(crate) struct ReformulationContext<'a, Oracle> {
	/// The resulting [`Solver`] object.
	pub(crate) slv: &'a mut Solver<Oracle>,
	/// The mapping from variable in the [`crate::Model`] to the corresponding
	/// view in the [`Solver`].
	pub(crate) map: &'a ReformulationMap,
}

#[derive(Debug, PartialEq, Eq)]
/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`crate::Model`].
pub enum ReformulationError {
	/// Error used when a conflict is found during the simplification process of
	/// the model.
	SimplificationConflict(<Model as ReasoningEngine>::Conflict),
	/// Error used when a conflict is found by the SAT oracle when translating
	/// the problem.
	TranslationConflict(Clause<RawLit>),
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
/// This type is primarily meant to resolve the order of creation issue when
/// dealing with aliased variables.
pub(crate) struct ReformulationMapBuilder {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<Option<BoolView>>,
	/// Set of integer decision for which the direct encoding should be created
	/// eagerly.
	pub(crate) int_eager_direct: FxHashSet<IntDecisionIndex>,
	/// The (default) maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub(crate) int_eager_limit: usize,
	/// Set of integer decision for which the order encoding should be created
	/// eagerly.
	pub(crate) int_eager_order: FxHashSet<IntDecisionIndex>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: IndexVec<IntDecisionIndex, Option<IntView>>,
}

impl<E> Constraint<E> for BoolFormula
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	BoolDecision: ModelBoolView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		let mut resolver = |bv: BoolDecision| {
			if let Some(b) = bv.val(ctx) {
				return Err(b);
			};
			Ok(bv)
		};
		let result = self.clone().simplify_with(&mut resolver);
		let mut f = match result {
			Ok(f) => f,
			Err(true) => return Ok(SimplificationStatus::Subsumed),
			Err(false) => return Err(ctx.declare_conflict([])),
		};

		let negate = |f: BoolFormula| match f {
			Formula::Atom(x) => Formula::Atom(!x),
			Formula::Not(x) if matches!(*x, Formula::Atom(_)) => {
				let Formula::Atom(x) = *x else { unreachable!() };
				Formula::Atom(x)
			}
			f => Formula::Not(Box::new(f)),
		};

		while let Formula::Not(neg_f) = f {
			f = match *neg_f {
				// Demorgan's Law transformation
				Formula::And(v) => Formula::Or(v.into_iter().map(negate).collect()),
				Formula::Atom(x) => Formula::Atom(!x),
				Formula::IfThenElse { cond, then, els } => Formula::IfThenElse {
					cond,
					then: Box::new(!*then),
					els: Box::new(!*els),
				},
				Formula::Implies(x, y) => {
					// Demorgan's Law transformation
					// ¬(x → y) ≡ ¬(¬x v y) ≡ x ∧ ¬y
					Formula::And(vec![*x, !*y])
				}
				// Double not elimination
				Formula::Not(f) => *f,
				// Demorgan's Law transformation
				Formula::Or(v) => Formula::And(v.into_iter().map(negate).collect()),
				Formula::Equiv(f) => Formula::And(vec![
					Formula::Or(f.iter().map(|f| !(f.clone())).collect()),
					Formula::Or(f),
				]),
				Formula::Xor(f) if f.len() < 2 => unreachable!(),
				Formula::Xor(f) if f.len() == 2 => Formula::Equiv(f),
				Formula::Xor(mut f) => {
					f[0] = negate(f[0].clone());
					Formula::Xor(f)
				}
			};
		}

		*self = match f {
			Formula::And(v) => {
				for f in v {
					match f {
						Formula::Atom(x) => {
							x.set(ctx, [])?;
						}
						Formula::Not(x) if matches!(*x, Formula::Atom(_)) => {
							let Formula::Atom(x) = *x else { unreachable!() };
							x.set_val(ctx, false, [])?;
						}
						f => {
							ctx.add_constraint(f);
						}
					}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			Formula::Atom(b) => {
				b.set(ctx, [])?;
				return Ok(SimplificationStatus::Subsumed);
			}
			Formula::Not(_) => unreachable!(),
			f => f,
		};
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let mut resolver = |bv: BoolDecision| {
			let inner = slv.solver_bool(bv);
			match inner.0 {
				BoolViewInner::Const(b) => Err(b),
				BoolViewInner::Lit(l) => Ok(l),
			}
		};
		let result: Result<Formula<RawLit>, _> = self.clone().simplify_with(&mut resolver);
		match result {
			Err(false) => Err(ReformulationError::TranslationConflict(vec![])),
			Err(true) => Ok(()),
			Ok(f) => slv.cnf_encode(&f, &TseitinEncoder),
		}
	}
}

impl<E> Propagator<E> for BoolFormula
where
	E: ReasoningEngine,
	BoolDecision: SolverBoolView<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.enqueue_now(true);
		match self {
			Formula::And(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::Atom(a) => a.enqueue_when_fixed(ctx),
			Formula::Equiv(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::IfThenElse { cond, then, els } => {
				cond.initialize(ctx);
				then.initialize(ctx);
				els.initialize(ctx);
			}
			Formula::Implies(f1, f2) => {
				f1.initialize(ctx);
				f2.initialize(ctx);
			}
			Formula::Not(f) => f.initialize(ctx),
			Formula::Or(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::Xor(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
		}
	}

	fn propagate(
		&mut self,
		_: &mut <E as ReasoningEngine>::PropagationCtx<'_>,
	) -> Result<(), <E as ReasoningEngine>::Conflict> {
		unreachable!()
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

	/// Get whether to enable asking for explanation clauses for all literals
	/// propagated on the level of a conflict.
	pub fn reason_eager(&self) -> bool {
		self.reason_eager
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

	/// Change whether to enable asking reason eagerly in the oracle solver.
	pub fn with_reason_eager(mut self, reason_eager: bool) -> Self {
		self.reason_eager = reason_eager;
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
}

impl IntDecisionDef {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSetVal) -> Self {
		Self {
			domain: Domain::Domain(dom),
			constraints: Default::default(),
		}
	}
}

impl<Oracle: ExternalPropagation> AddAssign<BoxedPropagator> for ReformulationContext<'_, Oracle> {
	fn add_assign(&mut self, propagator: BoxedPropagator) {
		*self.slv += propagator;
	}
}

impl<Oracle: ClauseDatabase> ClauseDatabase for ReformulationContext<'_, Oracle> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		self.slv.add_clause_from_slice(clause)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.slv.new_var_range(len)
	}
}

impl<Oracle: ExternalPropagation> ConstructionActions for ReformulationContext<'_, Oracle> {
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		ConstructionActions::new_trailed_int(self.slv, init)
	}
}

impl<Oracle> DecisionActions for ReformulationContext<'_, Oracle> {
	fn num_conflicts(&self) -> u64 {
		self.slv.engine.borrow().state.statistics.conflicts
	}
}

impl<Oracle: ClauseDatabase + ExternalPropagation> ReformulationActions
	for ReformulationContext<'_, Oracle>
{
	fn bool_val(&self, bv: RawLit) -> Option<bool> {
		bv.val(self.slv)
	}

	fn check_int_in_domain(&self, var: IntVarRef, val: IntVal) -> bool {
		var.in_domain(self.slv, val)
	}

	fn int_domain(&self, var: IntVarRef) -> IntSetVal {
		var.domain(self.slv)
	}

	fn int_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView {
		var.lit(self.slv, meaning)
	}

	fn int_lit_meaning(&self, var: IntVarRef, lit: BoolView) -> Option<IntLitMeaning> {
		var.lit_meaning(self.slv, lit)
	}

	fn int_lower_bound(&self, var: IntVarRef) -> IntVal {
		var.lower_bound(self.slv)
	}

	fn int_lower_bound_lit(&self, var: IntVarRef) -> BoolView {
		var.lower_bound_lit(self.slv)
	}

	fn int_upper_bound(&self, var: IntVarRef) -> IntVal {
		var.upper_bound(self.slv)
	}

	fn int_upper_bound_lit(&self, var: IntVarRef) -> BoolView {
		var.upper_bound_lit(self.slv)
	}

	fn new_bool_var(&mut self) -> BoolView {
		BoolView(BoolViewInner::Lit(self.slv.new_lit()))
	}
	fn solver_bool(&mut self, bv: BoolDecision) -> BoolView {
		self.map.get_bool(self.slv, bv)
	}

	fn solver_int(&mut self, iv: IntDecision) -> IntView {
		self.map.get_int(self.slv, iv)
	}

	fn try_int_lit(&self, var: IntVarRef, meaning: IntLitMeaning) -> Option<BoolView> {
		var.try_lit(self.slv, meaning)
	}
}

impl<Oracle> TrailingActions for ReformulationContext<'_, Oracle> {
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal {
		self.slv.set_trailed_int(i, v)
	}

	fn trailed_int(&self, i: TrailedInt) -> IntVal {
		self.slv.trailed_int(i)
	}
}

impl Display for ReformulationError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::SimplificationConflict(c) => {
				write!(f, "A conflict occurred during simplification: {c:?}")
			}
			Self::TranslationConflict(e) => {
				write!(f, "An error occurred during solver conversion: {e:?}")
			}
		}
	}
}

impl Error for ReformulationError {}

impl From<<Model as ReasoningEngine>::Conflict> for ReformulationError {
	fn from(value: <Model as ReasoningEngine>::Conflict) -> Self {
		Self::SimplificationConflict(value)
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
	pub fn get_bool<Oracle: ExternalPropagation>(
		&self,
		slv: &mut Solver<Oracle>,
		bv: BoolDecision,
	) -> BoolView {
		use BoolDecisionInner::*;

		let int_lit =
			|slv: &mut Solver<Oracle>, iv: IntDecisionIndex, lit_meaning: IntLitMeaning| {
				let iv = self.get_int(slv, IntDecision(IntDecisionInner::Linear(iv.into())));
				iv.lit(slv, lit_meaning)
			};

		match bv.0 {
			Lit(l) => {
				let idx = Into::<i32>::into(l.var()) as usize - 1;
				let bv: BoolView = self.bool_map[idx];
				if l.is_negated() { !bv } else { bv }
			}
			Const(c) => c.into(),
			IntEq(v, i) => int_lit(slv, v, IntLitMeaning::Eq(i)),
			IntGreaterEq(v, i) => int_lit(slv, v, IntLitMeaning::GreaterEq(i)),
			IntLess(v, i) => int_lit(slv, v, IntLitMeaning::Less(i)),
			IntNotEq(v, i) => int_lit(slv, v, IntLitMeaning::NotEq(i)),
		}
	}

	/// Lookup the solver [`IntView`] to which the given model [`int::IntView`]
	/// maps.
	pub fn get_int<Oracle: ExternalPropagation>(
		&self,
		slv: &mut Solver<Oracle>,
		iv: IntDecision,
	) -> IntView {
		use IntDecisionInner::*;

		match iv.0 {
			Const(c) => (c).into(),
			Linear(lin) => self.int_map[lin.var] * lin.scale + lin.offset,
			Bool(lin) => {
				let bv = self.get_bool(slv, lin.var);
				match bv.0 {
					BoolViewInner::Lit(lit) => IntView(IntViewInner::Bool(LinearBoolView::new(
						lin.scale, lin.offset, lit,
					))),
					BoolViewInner::Const(b) => lin.transform_val(b as IntVal).into(),
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
	/// Note that this method will function recursively (together with
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
				iv.lit(slv, IntLitMeaning::Eq(val))
			}
			IntGreaterEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::GreaterEq(val))
			}
			IntLess(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::Less(val))
			}
			IntNotEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::NotEq(val))
			}
		}
	}

	/// Get the representation of a Integer decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (together with
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
				Const(c) => c.into(),
				Linear(lin) => {
					let iv = self.get_or_create_int(model, slv, lin.var);
					iv * lin.scale + lin.offset
				}
				Bool(lin) => {
					let bv = self.get_or_create_bool(model, slv, lin.var);
					bv * lin.scale + lin.offset
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

#[cfg(test)]
mod tests {
	use pindakaas::propositional_logic::Formula;

	use crate::{
		BoolFormula, Model,
		actions::BoolInspectionActions,
		constraints::{Constraint, SimplificationStatus},
	};

	#[test]
	fn simplify_and_formula() {
		use Formula::*;

		// Test case for And with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = And(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for And with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = And(vec![Atom(x), Atom(false.into())]);
		assert!(<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb).is_err());
	}

	#[test]
	fn simplify_or_formula() {
		use Formula::*;

		// Test case for Or with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Or(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), None);

		// Test case for Or with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Or(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));
	}

	#[test]
	fn simplify_not_formula() {
		use Formula::*;

		// Test case for Not(Not(x))
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Not(Box::new(Atom(x)))));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for De Morgan's law with And
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(And(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Or(vec![Atom(!x), Atom(!y)]));

		// Test case for De Morgan's law with Or
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Or(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(Implies)
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Implies(Box::new(Atom(x)), Box::new(Atom(y)))));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(IfThenElse)
		let mut prb = Model::default();
		let c = prb.new_bool_var();
		let t = prb.new_bool_var();
		let e = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(IfThenElse {
			cond: Box::new(Atom(c)),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		}));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(
			f,
			IfThenElse {
				cond: Box::new(Atom(c)),
				then: Box::new(Not(Box::new(Atom(t)))),
				els: Box::new(Not(Box::new(Atom(e)))),
			}
		);

		// Test case for Not(Equiv(x,y))
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Equiv(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed) // rewritten to two clauses
		);
		assert_eq!(x.val(&prb), None);
		assert_eq!(y.val(&prb), None);

		// Test case for Not(Xor(x, y))
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Xor(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Equiv(vec![Atom(x), Atom(y)]));

		// Test case for Not(Xor(x, y, z))
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let y = prb.new_bool_var();
		let z = prb.new_bool_var();
		let mut f: BoolFormula = Not(Box::new(Xor(vec![Atom(x), Atom(y), Atom(z)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Xor(vec![Atom(!x), Atom(y), Atom(z)]));
	}

	#[test]
	fn simplify_implies_formula() {
		use Formula::*;

		// Test case for Implies(true, y) -> y
		let mut prb = Model::default();
		let y = prb.new_bool_var();
		let mut f: BoolFormula = Implies(Box::new(Atom(true.into())), Box::new(Atom(y)));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(y.val(&prb), Some(true));

		// Test case for Implies(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Implies(Box::new(Atom(x)), Box::new(Atom(false.into())));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}

	#[test]
	fn simplify_ifthenelse_formula() {
		use Formula::*;

		// Test case for IfThenElse(true, t, e) -> t
		let mut prb = Model::default();
		let t = prb.new_bool_var();
		let e = prb.new_bool_var();
		let mut f: BoolFormula = IfThenElse {
			cond: Box::new(Atom(true.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		};
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(t.val(&prb), Some(true));
		assert_eq!(e.val(&prb), None);

		// Test case for IfThenElse(false, t, e) -> e
		let mut prb = Model::default();
		let t = prb.new_bool_var();
		let e = prb.new_bool_var();
		let mut f: BoolFormula = IfThenElse {
			cond: Box::new(Atom(false.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		};
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(t.val(&prb), None);
		assert_eq!(e.val(&prb), Some(true));
	}

	#[test]
	fn simplify_equiv_formula() {
		use Formula::*;

		// Test case for Equiv(x, true) -> x
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Equiv(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Equiv(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Equiv(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}

	#[test]
	fn simplify_xor_formula() {
		use Formula::*;

		// Test case for Xor(x, false) -> x
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Xor(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Xor(x, true) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_var();
		let mut f: BoolFormula = Xor(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}
}
