//! Traits that encapsulate different sets of actions that can be performed at
//! different phases and by different objects in the solving process.

use std::{
	fmt,
	hash::Hash,
	ops::{AddAssign, Not},
};

use pindakaas::{AsDynClauseDatabase, ClauseDatabase, Lit as RawLit, Unsatisfiable};
use rangelist::IntervalIterator;

use crate::{
	BoolDecision, IntDecision, IntSetVal, IntVal,
	branchers::BoxedBrancher,
	constraints::{BoxedPropagator, Conflict, Constraint, LazyReason, ReasonBuilder},
	reformulate::ReformulationError,
	solver::{
		BoolView, BoolViewInner, IntLitMeaning, IntView, View, activation_list::IntPropCond,
		int_var::IntVarRef, queue::PriorityLevel, trail::TrailedInt,
	},
};

/// Actions available to [`Propagator`] implementations in
/// [`ReasoningEngine::PostingCtx`] for Boolean decision variables.
pub trait BoolInitActions<Context>: BoolInspectionActions<Context> {
	/// Advise the propagator when [`self`] is assigned, allowing the
	/// propagator to decide whether to enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// assignment, not just when it is not yet enqueued.
	///
	/// This will call [`Propagator::advise_of_bool_change`] on the propagator.
	fn advise_when_fixed(&self, ctx: &mut Context, data: u64);

	/// Enqueue the propagator when [`self`] is assigned.
	fn enqueue_when_fixed(&self, ctx: &mut Context);
}

/// Actions available to [`Propagator`] and [`Constraint`] implementations in
/// all contexts for Boolean decision variables.
pub trait BoolInspectionActions<Context: ?Sized>: BoolOperations {
	/// Get the current value of a Boolean decision variable, if it has been
	/// assigned.
	fn val(&self, ctx: &Context) -> Option<bool>;
}

/// Operations that are required to be possible to perform on types acting as
/// boolean decision variables.
pub trait BoolOperations: Clone + fmt::Debug + Eq + Hash + Not + 'static {}

/// Actions available to [`Propagator`] and [`Constraint`] implementations in
/// [`ReasoningEngine::PropagationCtx`] for Boolean decision variables.
pub trait BoolPropagationActions<Context>: BoolInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that the value of a Boolean decision variable is to be `true`,
	/// because of the given reason.
	fn set(
		&self,
		ctx: &mut Context,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict> {
		self.set_val(ctx, true, reason)
	}

	/// Enforce that the value of a Boolean decision variable is to be `val`,
	/// because of the given reason.
	fn set_val(
		&self,
		ctx: &mut Context,
		val: bool,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;
}

/// Actions available to [`Constraint`] implementations in
/// [`ReasoningEngine::PropagationCtx`] for Boolean decision variables.
///
/// Generally these actions are used in [`Constraint::simplify`].
pub trait BoolSimplificationActions<Context>:
	BoolPropagationActions<Context> + Into<BoolDecision>
where
	Context: ReasoningContext + ?Sized,
{
	/// Mark `self` as being equivalent to `other`, instructing the reasoning
	/// engine to use the same representation.
	fn unify(
		&self,
		ctx: &mut Context,
		other: impl Into<BoolDecision>,
	) -> Result<(), Context::Conflict>;
}

/// Actions that can be performed during the initialization of branchers.
pub trait BrancherInitActions: DecisionActions {
	/// Ensure that any relevant decision variable are marked internally as a
	/// decidable variable.
	fn ensure_decidable(&mut self, view: View);

	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;

	/// Push a new [`crate::branchers::Brancher`] to the end of the solving
	/// branching queue.
	fn push_brancher(&mut self, brancher: BoxedBrancher);
}

/// Actions that can be performed during the construction of [`Propagator]s and
/// [`Constraint`]s.
pub trait ConstructionActions {
	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
}

/// Actions that can be performed by a [`crate::branchers::Brancher`] when
/// making search decisions.
pub trait DecisionActions: TrailingActions {
	/// Returns the number of conflicts up to this point in the search process.
	fn num_conflicts(&self) -> u64;
}

/// Actions that can be performed when the propagator is posted.
pub trait InitActions {
	/// Advise a propagator when the solver backtracks.
	///
	/// This will call [`Propagator::advise_of_backtrack`] on the propagator.
	fn advise_on_backtrack(&mut self);

	/// Explicitly set whether the propagator should be enqueued immediately.
	fn enqueue_now(&mut self, option: bool);

	/// Set the priority level at which the propagator will be enqueued.
	fn set_priority(&mut self, priority: PriorityLevel);
}

/// Actions available to [`Brancher`] implementations for integer decision
/// variables.
///
/// These actions are also available to [`Propagator`] and [`Constraint`]
/// implementations in [`Reasoning::PropagationCtx`]
pub trait IntDecisionActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Get (or create) a literal for the given referenced integer variable with
	/// the given meaning.
	fn lit(&self, ctx: &mut Context, meaning: IntLitMeaning) -> Context::Atom;

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned.
	fn val_lit(&self, ctx: &mut Context) -> Option<Context::Atom> {
		let val = self.val(ctx)?;
		Some(self.lit(ctx, IntLitMeaning::Eq(val)))
	}
}

/// Actions available to [`Propagator`] implementations in
/// [`Reasoning::ExplanationCtx`] for integer decision variables.
pub trait IntExplanationActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, or a relaxation if the literal does not yet
	/// exist.
	fn lit_relaxed(&self, ctx: &Context, meaning: IntLitMeaning) -> (Context::Atom, IntLitMeaning);

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned or if the
	/// equality literal does not exist.
	fn try_val_lit(&self, ctx: &Context) -> Option<Context::Atom> {
		let val = self.val(ctx)?;
		self.try_lit(ctx, IntLitMeaning::Eq(val))
	}
}

/// Actions available to [`Propagator`] implementations in
/// [`ReasoningEngine::PostingCtx`] for Boolean decision variables.
pub trait IntInitActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Advise the propagator when [`self`] is changed according to the given
	/// propagation condition, allowing the propagator to decide whether to
	/// enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// integer change, not just when it is not yet enqueued.
	///
	/// This will call [`Propagator::advise_of_int_change`] on the propagator.
	fn advise_when(&self, ctx: &mut Context, condition: IntPropCond, data: u64);

	/// Enqueue the propagator when [`self`] is changed according to the given
	/// propagation condition.
	fn enqueue_when(&self, ctx: &mut Context, condition: IntPropCond);
}

/// Actions available to [`Propagator`] and [`Constraint`] implementations in
/// all contexts for integer decision variables.
pub trait IntInspectionActions<Context>: IntOperations
where
	Context: ReasoningContext + ?Sized,
{
	/// Convenience method to get both the lower and upper bounds of an integer
	/// view.
	fn bounds(&self, ctx: &Context) -> (IntVal, IntVal);
	/// Get the set of values from which the integer view is guaranteed to take
	/// a value (given the current search decisions).
	fn domain(&self, ctx: &Context) -> IntSetVal;

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn in_domain(&self, ctx: &Context, val: IntVal) -> bool;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn lit_meaning(&self, ctx: &Context, lit: Context::Atom) -> Option<IntLitMeaning>;

	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn lower_bound(&self, ctx: &Context) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn lower_bound_lit(&self, ctx: &Context) -> Context::Atom;

	/// Get a Boolean view that represents the given meaning on the integer
	/// view, if it already exists.
	fn try_lit(&self, ctx: &Context, meaning: IntLitMeaning) -> Option<Context::Atom>;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn upper_bound(&self, ctx: &Context) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn upper_bound_lit(&self, ctx: &Context) -> Context::Atom;

	/// Get the current value of an integer view, if it has been assigned (given
	/// the current search decisions).
	fn val(&self, ctx: &Context) -> Option<IntVal>;
}

/// Operations that are required to be possible to perform on types acting as
/// integer decision variables.
pub trait IntOperations: Clone + fmt::Debug + Eq + Hash + 'static {}

/// Actions available to [`Propagator`] and [`Constraint`] implementations in
/// [`ReasoningEngine::PropagationCtx`] for integer decision variables.
pub trait IntPropagationActions<Context>: IntDecisionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val` because of the given `reason`.
	fn set_lower_bound(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view cannot take a value `val` because of the
	/// given `reason`.
	fn set_not_eq(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val` because of the given `reason`.
	fn set_upper_bound(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view takes a value `val` because of the given
	/// `reason`.
	fn set_val(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;
}

/// Actions available to [`Constraint`] implementations in
/// [`ReasoningEngine::PropagationCtx`] for integer decision variables.
///
/// Generally these actions are used in [`Constraint::simplify`].
pub trait IntSimplificationActions<Context>: IntPropagationActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that the given integer expression takes a value in in the given
	/// set.
	fn set_domain(
		&self,
		ctx: &mut Context,
		domain: &IntSetVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a given integer expression cannot take any of the values in
	/// the given set.
	fn set_not_in_set(
		&self,
		ctx: &mut Context,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Mark two integer decisions as being equivalent, ensuring the two use the
	/// same internal representation.
	fn unify(&self, ctx: &mut Context, other: impl Into<Self>) -> Result<(), Context::Conflict>;
}

/// General actions that can be performed in [`ReasoningEngine::PropagationCtx`]
pub trait PropagationActions: DecisionActions + ReasoningContext {
	/// Declare that given reason (seen as a conjunction of atoms) is represents
	/// a conflict in the current state (requiring backtracking).
	///
	/// Note that it is generally recommended to use this method only when
	/// integer or Boolean propagation methods do not seem relevant.
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self>) -> Self::Conflict;

	/// Create a placeholder reason that will cause the solver to call the
	/// propagator's [`crate::constraints::Propagator::explain`] method when the
	/// reason is needed.
	fn deferred_reason(&self, data: u64) -> LazyReason;
}

/// The ReasoningContext trait names the fundamental reasoning types used by the
/// context objects used by the various Action traits.
pub trait ReasoningContext {
	/// Type used to represent an atom in an reason for propagation.
	type Atom: BoolOperations + Not<Output = Self::Atom>;
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;
}

/// Trait for environments that support constraint propagation and decision
/// variable pruning to simplify the current problem state.
pub trait ReasoningEngine {
	/// Type used to represent an atom in an reason for propagation.
	type Atom: BoolOperations;
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;

	/// The context given to the constraint propagator when they are asked to
	/// explain a reason for a change they made using
	/// [`PropagationActions::deferred_reason`].
	type ExplanationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ TrailingActions;
	/// The context given to constraint propagators to attach themselves to
	/// changes in the state of the reasoning engine or decision variables.
	type InitializationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ InitActions;
	/// The context given to constraint propagators when they are advised of a
	/// change in the state of the reasoning engine or decision variables.
	type NotificationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ TrailingActions;
	/// The context given to constraint propagators when they are asked to
	/// propagate changes based on the constraint they enforce.
	type PropagationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ PropagationActions<Atom = Self::Atom, Conflict = Self::Conflict>;
}

/// Actions that can be performed when reformulating a [`Model`] object into a
/// [`Solver`] object.
pub trait ReformulationActions:
	AddAssign<BoxedPropagator> + AsDynClauseDatabase + ClauseDatabase + ConstructionActions
{
	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn bool_val(&self, bv: RawLit) -> Option<bool>;

	/// Check whether a given integer view can take a given value
	fn check_int_in_domain(&self, var: IntVarRef, val: IntVal) -> bool;

	/// Get the set of values from which the integer view is guaranteed to take
	/// a value.
	fn int_domain(&self, var: IntVarRef) -> IntSetVal;

	/// Get (or create) a literal for the given integer view with the given
	/// meaning.
	fn int_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn int_lit_meaning(&self, var: IntVarRef, lit: BoolView) -> Option<IntLitMeaning>;

	/// Get the minimum value that an integer view is guaranteed to take.
	fn int_lower_bound(&self, var: IntVarRef) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn int_lower_bound_lit(&self, var: IntVarRef) -> BoolView;

	/// Get the maximum value that an integer view is guaranteed to take.
	fn int_upper_bound(&self, var: IntVarRef) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn int_upper_bound_lit(&self, var: IntVarRef) -> BoolView;

	/// Create a new Boolean decision variable to use in the encoding.
	fn new_bool_var(&mut self) -> BoolView;

	/// Lookup the solver [`BoolView`] to which the given model
	/// [`model::bool::BoolView`] maps.
	fn solver_bool(&mut self, bv: BoolDecision) -> BoolView;

	/// Lookup the solver [`IntExpr`] to which the given model
	/// [`model::int::IntView`] maps.
	fn solver_int(&mut self, iv: IntDecision) -> IntView;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn try_int_lit(&self, var: IntVarRef, meaning: IntLitMeaning) -> Option<BoolView>;
}

/// Internal wrapper for the [`ClauseDatabase`] implementation to provide a
/// [`ReformulationError`] if the solver returns [`Unsatisfiable`].
pub(crate) struct ReformulationClauseDatabaseWrapper<'a> {
	/// The wrapped dynamic [`ReformulationActions`] implementation.
	db: &'a mut (dyn ReformulationActions + 'a),
	/// Error that captures the clause that caused methods to return
	/// [`Unsatisfiable`].
	pub(crate) error: Option<ReformulationError>,
}

/// Actions that can be performed to simplify a Model considering a given
/// constraint.
pub trait SimplificationActions {
	/// The type of the reasoning engine that is used when adding new
	/// constraints.
	type Target: ReasoningEngine;

	/// Add a constraint to the model (to replace the current constraint).
	fn add_constraint<C: Constraint<Self::Target>>(&mut self, constraint: C);
}

/// Basic actions that can be performed when the trailing infrastructure is
/// available.
pub trait TrailingActions {
	/// Change the value of a [`TrailedInt`] in a way that can be undone if the
	/// solver backtracks to a previous state.
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;

	/// Get the current value of a [`TrailedInt`].
	fn trailed_int(&self, i: TrailedInt) -> IntVal;
}

impl<Ctx> IntDecisionActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		self.try_lit(ctx, meaning).unwrap()
	}
}

impl<Ctx> IntExplanationActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		(self.try_lit(ctx, meaning).unwrap(), meaning)
	}
}

impl<Ctx> IntInspectionActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn bounds(&self, _: &Ctx) -> (IntVal, IntVal) {
		(*self, *self)
	}

	fn domain(&self, _: &Ctx) -> IntSetVal {
		(*self..=*self).into()
	}

	fn in_domain(&self, _: &Ctx, val: IntVal) -> bool {
		*self == val
	}

	fn lit_meaning(&self, _: &Ctx, _: Ctx::Atom) -> Option<IntLitMeaning> {
		None
	}

	fn lower_bound(&self, _: &Ctx) -> IntVal {
		*self
	}

	fn lower_bound_lit(&self, _: &Ctx) -> Ctx::Atom {
		true.into()
	}

	fn try_lit(&self, _: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		Some(
			match meaning {
				IntLitMeaning::Eq(v) => *self == v,
				IntLitMeaning::NotEq(v) => *self != v,
				IntLitMeaning::GreaterEq(v) => *self >= v,
				IntLitMeaning::Less(v) => *self < v,
			}
			.into(),
		)
	}

	fn upper_bound(&self, _: &Ctx) -> IntVal {
		*self
	}

	fn upper_bound_lit(&self, _: &Ctx) -> Ctx::Atom {
		true.into()
	}

	fn val(&self, _: &Ctx) -> Option<IntVal> {
		Some(*self)
	}
}

impl<Ctx> IntPropagationActions<Ctx> for IntVal
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn set_lower_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val > *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn set_not_eq(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val == *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val < *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn set_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val != *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}
}

impl<Ctx> IntSimplificationActions<Ctx> for IntVal
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn set_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSetVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if !domain.contains(self) {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn set_not_in_set(
		&self,
		ctx: &mut Ctx,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if values.contains(self) {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn unify(&self, ctx: &mut Ctx, other: impl Into<Self>) -> Result<(), Ctx::Conflict> {
		if self == &other.into() {
			Ok(())
		} else {
			Err(ctx.declare_conflict([]))
		}
	}
}

impl IntDecisionActions<dyn ReformulationActions + '_> for IntVarRef {
	fn lit(&self, ctx: &mut (dyn ReformulationActions + '_), meaning: IntLitMeaning) -> BoolView {
		ctx.int_lit(*self, meaning)
	}
}

impl IntInspectionActions<dyn ReformulationActions + '_> for IntVarRef {
	fn bounds(&self, ctx: &dyn ReformulationActions) -> (IntVal, IntVal) {
		let lb = self.lower_bound(ctx);
		let ub = self.upper_bound(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &dyn ReformulationActions) -> IntSetVal {
		ctx.int_domain(*self)
	}

	fn in_domain(&self, ctx: &dyn ReformulationActions, val: IntVal) -> bool {
		ctx.check_int_in_domain(*self, val)
	}

	fn lit_meaning(&self, ctx: &dyn ReformulationActions, lit: BoolView) -> Option<IntLitMeaning> {
		ctx.int_lit_meaning(*self, lit)
	}

	fn lower_bound(&self, ctx: &dyn ReformulationActions) -> IntVal {
		ctx.int_lower_bound(*self)
	}

	fn lower_bound_lit(&self, ctx: &dyn ReformulationActions) -> BoolView {
		ctx.int_lower_bound_lit(*self)
	}

	fn try_lit(&self, ctx: &dyn ReformulationActions, meaning: IntLitMeaning) -> Option<BoolView> {
		ctx.try_int_lit(*self, meaning)
	}

	fn upper_bound(&self, ctx: &dyn ReformulationActions) -> IntVal {
		ctx.int_upper_bound(*self)
	}

	fn upper_bound_lit(&self, ctx: &dyn ReformulationActions) -> BoolView {
		ctx.int_upper_bound_lit(*self)
	}

	fn val(&self, ctx: &dyn ReformulationActions) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

impl BoolInspectionActions<dyn ReformulationActions + '_> for RawLit {
	fn val(&self, ctx: &dyn ReformulationActions) -> Option<bool> {
		ctx.bool_val(*self)
	}
}

impl ClauseDatabase for ReformulationClauseDatabaseWrapper<'_> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		match self.db.add_clause_from_slice(clause) {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => {
				self.error = Some(ReformulationError::TranslationConflict(clause.to_vec()));
				Err(Unsatisfiable)
			}
		}
	}
	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.db.new_var_range(len)
	}
}

impl<T> BoolOperations for T where T: Clone + fmt::Debug + Eq + Hash + Not + 'static {}
impl<T> IntOperations for T where T: Clone + fmt::Debug + Eq + Hash + 'static {}

impl<Ctx> BoolInspectionActions<Ctx> for bool {
	fn val(&self, _: &Ctx) -> Option<bool> {
		Some(*self)
	}
}

impl<Ctx> BoolPropagationActions<Ctx> for bool
where
	Ctx: ReasoningContext + PropagationActions,
{
	fn set_val(
		&self,
		ctx: &mut Ctx,
		val: bool,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		if *self != val {
			return Err(ctx.declare_conflict(reason));
		}
		Ok(())
	}
}

impl dyn ReformulationActions + '_ {
	/// Add a new clause to the resulting [`Solver`].
	pub fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = impl Into<BoolView>>,
	) -> Result<(), ReformulationError> {
		let clause: Result<Vec<_>, bool> = clause
			.into_iter()
			.filter_map(|lit| match lit.into().0 {
				BoolViewInner::Lit(lit) => Some(Ok(lit)),
				BoolViewInner::Const(true) => Some(Err(true)),
				BoolViewInner::Const(false) => None,
			})
			.collect();
		let clause = match clause {
			Err(false) => unreachable!(),
			Err(true) => return Ok(()),
			Ok(clause) if clause.is_empty() => {
				return Err(ReformulationError::TranslationConflict(vec![]));
			}
			Ok(clause) => clause,
		};
		match self.add_clause_from_slice(&clause) {
			Err(Unsatisfiable) => Err(ReformulationError::TranslationConflict(clause)),
			Ok(()) => Ok(()),
		}
	}

	/// Internal method used to wrap the [`ClauseDatabase`] implementation to
	/// provide a [`ReformulationError`] if the solver returns
	/// [`Unsatisfiable`].
	pub(crate) fn clause_database_wrapper(&mut self) -> ReformulationClauseDatabaseWrapper<'_> {
		ReformulationClauseDatabaseWrapper {
			db: self,
			error: None,
		}
	}

	/// Encode the given constraint into conjunctive normal form (CNF) using the
	/// given encoder, and add it to the resulting [`Solver`].
	pub fn cnf_encode<C, E>(
		&mut self,
		constraint: &C,
		encoder: &E,
	) -> Result<(), ReformulationError>
	where
		C: ?Sized,
		E: for<'a> pindakaas::Encoder<dyn ClauseDatabase + 'a, C> + ?Sized,
	{
		let mut wrapper = self.clause_database_wrapper();
		let res = pindakaas::Encoder::encode(encoder, &mut wrapper, constraint);
		match res {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => Err(wrapper.error.unwrap()),
		}
	}
}

impl ReasoningContext for dyn ReformulationActions + '_ {
	type Atom = BoolView;
	type Conflict = Conflict<RawLit>;
}
