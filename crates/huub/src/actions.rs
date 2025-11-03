//! Traits that encapsulate different sets of actions that can be performed at
//! different phases and by different objects in the solving process.

use std::{
	fmt,
	hash::Hash,
	ops::{AddAssign, Not},
};

use itertools::Itertools;
use pindakaas::{AsDynClauseDatabase, ClauseDatabase, Lit as RawLit, Unsatisfiable};

use crate::{
	branchers::BoxedBrancher,
	constraints::{BoxedPropagator, Constraint, LazyReason, ReasonBuilder},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, int_var::IntVarRef, queue::PriorityLevel, trail::TrailedInt,
		BoolView, IntLitMeaning, IntView, View,
	},
	BoolDecision, IntDecision, IntSetVal, IntVal,
};

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

/// Actions that can be performed by a [`crate::branchers::Brancher`] when
/// making search decisions.
pub trait DecisionActions: TrailingActions {
	/// Returns the number of conflicts up to this point in the search process.
	fn get_num_conflicts(&self) -> u64;
}

/// Operations that are required to be possible to perform on types acting as
/// boolean decision variables.
pub trait BoolOperations: Clone + fmt::Debug + Eq + Hash + Not<Output = Self> + 'static {}

pub trait BoolInspectionActions<Context: ?Sized>: BoolOperations {
	fn get_val(&self, ctx: &Context) -> Option<bool>;
}

pub trait BoolPropagationActions<Context>: BoolInspectionActions<Context> {
	type Conflict;
	type Atom: BoolOperations + From<Self>;

	fn set(
		&self,
		ctx: &mut Context,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		self.set_val(ctx, true, reason)
	}

	fn set_val(
		&self,
		ctx: &mut Context,
		val: bool,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;
}

pub trait BoolSimplificationActions<Context>:
	BoolPropagationActions<Context> + Into<BoolDecision>
{
	/// Mark two Boolean decisions as being equivalent, ensuring the two use the
	/// same internal representation.
	fn unify(
		&self,
		ctx: &mut Context,
		other: impl Into<BoolDecision>,
	) -> Result<(), Self::Conflict>;
}

pub trait BoolPostingActions<Context>: BoolInspectionActions<Context> {
	/// Enqueue a propagator to be enqueued when a [`BoolView`] is assigned.
	fn enqueue_when_fixed(&self, ctx: &mut Context);

	/// Advise a propagator when a [`BoolView`] is assigned, allowing the
	/// propagator to decide whether to enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// assignment, not just when it is not yet enqueued.
	///
	/// This will call [`Propagator::advise_of_bool_change`] on the propagator.
	fn advise_when_fixed(&self, ctx: &mut Context, data: u64);
}

/// Operations that are required to be possible to perform on types acting as
/// integer decision variables.
pub trait IntOperations: Clone + fmt::Debug + Eq + Hash + 'static {}

/// Actions that can generally be performed when the solver is (partially)
/// initialized.
pub trait IntInspectionActions<Context: ?Sized>: IntOperations {
	type Atom: BoolOperations;

	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_lower_bound(&self, ctx: &Context) -> IntVal;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_upper_bound(&self, ctx: &Context) -> IntVal;

	/// Convenience method to get both the lower and upper bounds of an integer
	/// view.
	fn get_bounds(&self, ctx: &Context) -> (IntVal, IntVal) {
		(self.get_lower_bound(ctx), self.get_upper_bound(ctx))
	}

	/// Get the current value of an integer view, if it has been assigned.
	fn get_val(&self, ctx: &Context) -> Option<IntVal> {
		let (lb, ub) = self.get_bounds(ctx);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn check_in_domain(&self, ctx: &Context, val: IntVal) -> bool;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn get_lit_meaning(&self, ctx: &Context, lit: Self::Atom) -> Option<IntLitMeaning>;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn get_lower_bound_lit(&self, ctx: &Context) -> Self::Atom;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn get_upper_bound_lit(&self, ctx: &Context) -> Self::Atom;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn try_lit(&self, ctx: &Context, meaning: IntLitMeaning) -> Option<Self::Atom>;
}

pub trait IntDecisionActions<Context: ?Sized>: IntInspectionActions<Context> {
	/// Get (or create) a literal for the given referenced integer variable with
	/// the given meaning.
	fn get_lit(&self, ctx: &mut Context, meaning: IntLitMeaning) -> Self::Atom;

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned.
	fn get_val_lit(&self, ctx: &mut Context) -> Option<Self::Atom> {
		let val = self.get_val(ctx)?;
		Some(self.get_lit(ctx, IntLitMeaning::Eq(val)))
	}
}

pub trait IntExplanationActions<Context: ?Sized>: IntInspectionActions<Context> {
	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, or a relaxation if the literal does not yet
	/// exist.
	fn get_lit_relaxed(&self, ctx: &Context, meaning: IntLitMeaning)
		-> (Self::Atom, IntLitMeaning);

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned or if the
	/// equality literal does not exist.
	fn try_val_lit(&self, ctx: &Context) -> Option<Self::Atom> {
		let val = self.get_val(ctx)?;
		self.try_lit(ctx, IntLitMeaning::Eq(val))
	}
}

pub trait IntPropagationActions<Context: ?Sized>: IntDecisionActions<Context> {
	type Conflict;

	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val` because of the given `reason`.
	fn set_lower_bound(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val` because of the given `reason`.
	fn set_upper_bound(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Enforce that a an integer view takes a value `val` because of the given
	/// `reason`.
	fn set_val(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Enforce that a an integer view cannot take a value `val` because of the
	/// given `reason`.
	fn set_not_eq(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;
}

pub trait IntSimplificationActions<Context: ?Sized>: IntPropagationActions<Context> {
	/// Get the domain from which an integer view is guaranteed to take a value.
	fn get_domain(&self, ctx: &Context) -> IntSetVal;

	/// Enforce that a given integer expression cannot take any of the values in
	/// the given set.
	fn set_not_in_set(
		&self,
		ctx: &mut Context,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Enforce that the given integer expression takes a value in in the given
	/// set.
	fn set_domain(
		&self,
		ctx: &mut Context,
		domain: &IntSetVal,
		reason: impl ReasonBuilder<Context, Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Mark two integer decisions as being equivalent, ensuring the two use the
	/// same internal representation.
	fn unify(&self, ctx: &mut Context, other: impl Into<Self>) -> Result<(), Self::Conflict>;
}

/// Actions that can be performed during propagation.
pub trait PropagationActions: DecisionActions {
	type Atom;
	type Conflict;

	/// Create a placeholder reason that will cause the solver to call the
	/// propagator's [`crate::constraints::Propagator::explain`] method when the
	/// reason is needed.
	fn deferred_reason(&self, data: u64) -> LazyReason;

	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self, Self::Atom>) -> Self::Conflict;
}

pub trait IntPostingActions<Context>: IntInspectionActions<Context> {
	/// Advise a propagator when an [`IntView`] is changed according to the
	/// given propagation condition, allowing the propagator to decide whether
	/// to enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// integer change, not just when it is not yet enqueued.
	///
	/// This will call [`Propagator::advise_of_int_change`] on the propagator.
	fn advise_when(&self, ctx: &mut Context, condition: IntPropCond, data: u64);

	/// Enqueue a propagator to be enqueued when an [`IntView`] is changed
	/// according to the given propagation condition.
	fn enqueue_when(&self, ctx: &mut Context, condition: IntPropCond);
}

/// Actions that can be performed when the propagator is posted.
pub trait PostingActions {
	/// Advise a propagator when the solver backtracks.
	///
	/// This will call [`Propagator::advise_of_backtrack`] on the propagator.
	fn advise_on_backtrack(&mut self);

	/// Explicitly set whether the propagator should be enqueued immediately.
	fn enqueue_now(&mut self, option: bool);

	/// Set the priority level at which the propagator will be enqueued.
	fn set_priority(&mut self, priority: PriorityLevel);
}

pub trait InitializationActions {
	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
}

pub trait ReasoningEngine {
	type PostingCtx<'a>: PostingActions;
	type NotificationCtx<'a>: TrailingActions;
	type PropagationCtx<'a>: PropagationActions<Atom = Self::Atom, Conflict = Self::Conflict>;
	type ExplanationCtx<'a>: TrailingActions;

	type Conflict;
	type Atom: BoolOperations;
}

/// Actions that can be performed when reformulating a [`Model`] object into a
/// [`Solver`] object.
pub trait ReformulationActions:
	AddAssign<BoxedPropagator> + AsDynClauseDatabase + ClauseDatabase + InitializationActions
{
	/// Lookup the solver [`BoolView`] to which the given model
	/// [`model::bool::BoolView`] maps.
	fn get_solver_bool(&mut self, bv: BoolDecision) -> BoolView;

	/// Lookup the solver [`IntExpr`] to which the given model
	/// [`model::int::IntView`] maps.
	fn get_solver_int(&mut self, iv: IntDecision) -> IntView;

	/// Create a new Boolean decision variable to use in the encoding.
	fn new_bool_var(&mut self) -> BoolView;

	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn get_bool_val(&self, bv: RawLit) -> Option<bool>;

	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_lower_bound(&self, var: IntVarRef) -> IntVal;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_upper_bound(&self, var: IntVarRef) -> IntVal;

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn check_int_in_domain(&self, var: IntVarRef, val: IntVal) -> bool;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn get_int_lit_meaning(&self, var: IntVarRef, lit: BoolView) -> Option<IntLitMeaning>;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn get_int_lower_bound_lit(&self, var: IntVarRef) -> BoolView;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn get_int_upper_bound_lit(&self, var: IntVarRef) -> BoolView;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn try_int_lit(&self, var: IntVarRef, meaning: IntLitMeaning) -> Option<BoolView>;

	/// Get (or create) a literal for the given integer view with the given
	/// meaning.
	fn get_int_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView;
}

/// Actions that can be performed to simplify a Model considering a given
/// constraint.
pub trait SimplificationActions {
	type Target: ReasoningEngine;

	/// Add a constraint to the model (to replace the current constraint).
	fn add_constraint<C: Constraint<Self::Target>>(&mut self, constraint: C);
}

/// Basic actions that can be performed when the trailing infrastructure is
/// available.
pub trait TrailingActions {
	/// Get the current value of a [`TrailedInt`].
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
	/// Change the value of a [`TrailedInt`] in a way that can be undone if the
	/// solver backtracks to a previous state.
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
}

impl<T> BoolOperations for T where T: Clone + fmt::Debug + Eq + Hash + Not<Output = Self> + 'static {}
impl<T> IntOperations for T where T: Clone + fmt::Debug + Eq + Hash + 'static {}

impl dyn ReformulationActions + '_ {
	pub fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = impl Into<BoolView>>,
	) -> Result<(), ReformulationError> {
		use pindakaas::ClauseDatabaseTools;

		let clause: Vec<_> = clause.into_iter().map_into().collect();
		match ClauseDatabaseTools::add_clause(self, clause.clone()) {
			Err(Unsatisfiable) => Err(ReformulationError::TranslationConflict(clause)),
			Ok(()) => Ok(()),
		}
	}

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

	pub(crate) fn clause_database_wrapper(&mut self) -> ReformulationClauseDatabaseWrapper<'_> {
		ReformulationClauseDatabaseWrapper {
			db: self,
			error: None,
		}
	}
}

pub(crate) struct ReformulationClauseDatabaseWrapper<'a> {
	db: &'a mut (dyn ReformulationActions + 'a),
	pub(crate) error: Option<ReformulationError>,
}

impl ClauseDatabase for ReformulationClauseDatabaseWrapper<'_> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		match self.db.add_clause(clause.into_iter().cloned()) {
			Ok(()) => Ok(()),
			Err(err) => {
				self.error = Some(err);
				Err(Unsatisfiable)
			}
		}
	}
	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.db.new_var_range(len)
	}
}

/// Encoder is the central trait implemented for all the encoding algorithms
pub trait MyEncoder<Db: ClauseDatabase + ?Sized, Constraint: ?Sized> {
	/// Encode the constraint into the given clausal database.
	fn encode(&self, db: &mut Db, con: &Constraint) -> Result<(), Unsatisfiable>;
}

impl BoolInspectionActions<dyn ReformulationActions + '_> for RawLit {
	fn get_val(&self, ctx: &dyn ReformulationActions) -> Option<bool> {
		ctx.get_bool_val(*self)
	}
}

impl IntInspectionActions<dyn ReformulationActions + '_> for IntVarRef {
	type Atom = BoolView;

	fn get_lower_bound(&self, ctx: &dyn ReformulationActions) -> IntVal {
		ctx.get_int_lower_bound(*self)
	}

	fn get_upper_bound(&self, ctx: &dyn ReformulationActions) -> IntVal {
		ctx.get_int_upper_bound(*self)
	}

	fn check_in_domain(&self, ctx: &dyn ReformulationActions, val: IntVal) -> bool {
		ctx.check_int_in_domain(*self, val)
	}

	fn get_lit_meaning(
		&self,
		ctx: &dyn ReformulationActions,
		lit: Self::Atom,
	) -> Option<IntLitMeaning> {
		ctx.get_int_lit_meaning(*self, lit)
	}

	fn get_lower_bound_lit(&self, ctx: &dyn ReformulationActions) -> Self::Atom {
		ctx.get_int_lower_bound_lit(*self)
	}

	fn get_upper_bound_lit(&self, ctx: &dyn ReformulationActions) -> Self::Atom {
		ctx.get_int_upper_bound_lit(*self)
	}

	fn try_lit(
		&self,
		ctx: &dyn ReformulationActions,
		meaning: IntLitMeaning,
	) -> Option<Self::Atom> {
		ctx.try_int_lit(*self, meaning)
	}
}

impl IntDecisionActions<dyn ReformulationActions + '_> for IntVarRef {
	fn get_lit(
		&self,
		ctx: &mut (dyn ReformulationActions + '_),
		meaning: IntLitMeaning,
	) -> Self::Atom {
		ctx.get_int_lit(*self, meaning)
	}
}

impl<C> BoolInspectionActions<C> for bool {
	fn get_val(&self, _: &C) -> Option<bool> {
		Some(*self)
	}
}
