//! Traits that encapsulate different sets of actions that can be performed at
//! different phases and by different objects in the solving process.

use std::ops::AddAssign;

use pindakaas::{AsDynClauseDatabase, ClauseDatabase};

use crate::{
	branchers::BoxedBrancher,
	constraints::{BoxedPropagator, Conflict, LazyReason, ReasonBuilder},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, engine::PropRef, int_var::IntVarRef, queue::PriorityLevel,
		trail::TrailedInt, BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner, View,
	},
	BoolDecision, IntDecision, IntSetVal, IntVal, Model,
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

/// Actions that can be performed when a constraint is initialized within a
/// model object.
pub trait ConstraintInitActions {
	/// Schedule the simplify method of the calling constraint when the given
	/// boolean expression changes.
	fn simplify_on_change_bool(&mut self, var: BoolDecision);

	/// Schedule the simplify method of the calling constraint when the given
	/// integer expression changes.
	fn simplify_on_change_int(&mut self, var: IntDecision);
}

/// Actions that can be performed by a [`crate::branchers::Brancher`] when
/// making search decisions.
pub trait DecisionActions: InspectionActions {
	/// Get (or create) a literal for the given integer view with the given meaning.
	fn get_int_lit(&mut self, var: IntView, mut meaning: IntLitMeaning) -> BoolView {
		{
			if let IntViewInner::Linear { transformer, .. }
			| IntViewInner::Bool { transformer, .. } = var.0
			{
				match transformer.rev_transform_lit(meaning) {
					Ok(m) => meaning = m,
					Err(v) => return BoolView(BoolViewInner::Const(v)),
				}
			}

			match var.0 {
				IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
					self.get_intref_lit(var, meaning)
				}
				IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match meaning {
					IntLitMeaning::Eq(i) => c == i,
					IntLitMeaning::NotEq(i) => c != i,
					IntLitMeaning::GreaterEq(i) => c >= i,
					IntLitMeaning::Less(i) => c < i,
				})),
				IntViewInner::Bool { lit, .. } => {
					let (meaning, negated) =
						if matches!(meaning, IntLitMeaning::NotEq(_) | IntLitMeaning::Less(_)) {
							(!meaning, true)
						} else {
							(meaning, false)
						};
					let bv = BoolView(match meaning {
						IntLitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
						IntLitMeaning::Eq(1) => BoolViewInner::Lit(lit),
						IntLitMeaning::Eq(_) => BoolViewInner::Const(false),
						IntLitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
						IntLitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
						IntLitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
						_ => unreachable!(),
					});
					if negated {
						!bv
					} else {
						bv
					}
				}
			}
		}
	}

	/// Get (or create) a literal for the given referenced integer variable with the given meaning.
	fn get_intref_lit(&mut self, var: IntVarRef, meaning: IntLitMeaning) -> BoolView;

	/// Returns the number of conflicts up to this point in the search process.
	fn get_num_conflicts(&self) -> u64;
}

/// Actions that can be performed when explaining a propagation that was
/// performed.
pub trait ExplanationActions: InspectionActions {
	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn try_int_lit(&self, var: IntView, meaning: IntLitMeaning) -> Option<BoolView>;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, or a relaxation if the literal does not yet
	/// exist.
	fn get_int_lit_relaxed(
		&mut self,
		var: IntView,
		meaning: IntLitMeaning,
	) -> (BoolView, IntLitMeaning);

	/// Get the Boolean view that represents the current assignment of the integer
	/// view, or `None` if the integer view is not assigned.
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView>;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
}

/// Actions that can generally be performed when the solver is (partially)
/// initialized.
pub trait InspectionActions: TrailingActions {
	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_lower_bound(&self, var: IntView) -> IntVal;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_upper_bound(&self, var: IntView) -> IntVal;

	/// Convenience method to get both the lower and upper bounds of an integer
	/// view.
	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		(self.get_int_lower_bound(var), self.get_int_upper_bound(var))
	}

	/// Get the current value of an integer view, if it has been assigned.
	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		let (lb, ub) = self.get_int_bounds(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
}

/// Actions that can be performed during propagation.
pub trait PropagationActions: ExplanationActions + DecisionActions {
	/// Enforce a boolean view to be `true` because of a given `reason`.
	///
	/// Note that it is possible to enforce that a boolean view is `false` by
	/// negating the view, i.e. `!bv`.
	fn set_bool(&mut self, bv: BoolView, reason: impl ReasonBuilder<Self>) -> Result<(), Conflict>;

	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val` because of the given `reason`.
	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val` because of the given `reason`.
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Enforce that a an integer view takes a value `val` because of the given
	/// `reason`.
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Enforce that a an integer view cannot take a value `val` because of the
	/// given `reason`.
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Create a placeholder reason that will cause the solver to call the
	/// propagator's [`crate::constraints::Propagator::explain`] method when the
	/// reason is needed.
	fn deferred_reason(&self, data: u64) -> LazyReason;
}

/// Actions that can be performed during the initialization of propagators.
pub trait PropagatorInitActions: AsDynClauseDatabase + ClauseDatabase + DecisionActions {
	/// Add a propagator to the solver.
	fn add_propagator(&mut self, propagator: BoxedPropagator, priority: PriorityLevel) -> PropRef;

	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;

	/// Enqueue a propagator to be activated at the root node.
	fn enqueue_now(&mut self, prop: PropRef);

	/// Enqueue a propagator to be enqueued when a boolean variable is assigned.
	fn enqueue_on_bool_change(&mut self, prop: PropRef, var: BoolView);

	/// Enqueue a propagator to be enqueued when an integer variable is changed
	/// according to the given propagation condition.
	fn enqueue_on_int_change(&mut self, prop: PropRef, var: IntView, condition: IntPropCond);
}

/// Actions that can be performed when reformulating a [`Model`] object into a
/// [`Solver`] object.
pub trait ReformulationActions: PropagatorInitActions {
	/// Lookup the solver [`BoolView`] to which the given model
	/// [`model::bool::BoolView`] maps.
	fn get_solver_bool(&mut self, bv: BoolDecision) -> BoolView;

	/// Lookup the solver [`IntExpr`] to which the given model
	/// [`model::int::IntView`] maps.
	fn get_solver_int(&mut self, iv: IntDecision) -> IntView;

	/// Create a new Boolean decision variable to use in the encoding.
	fn new_bool_var(&mut self) -> BoolView;
}

/// Actions that can be performed to simplify a Model considering a given
/// constraint.
pub trait SimplificationActions {
	/// Add a constraint to the model (to replace the current constraint).
	fn add_constraint<C>(&mut self, constraint: C)
	where
		Model: AddAssign<C>;

	/// Check whether a given integer view can take a given value.
	fn check_int_in_domain(&self, var: IntDecision, val: IntVal) -> bool;

	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn get_bool_val(&self, bv: BoolDecision) -> Option<bool>;

	/// Get the minimum value that an integer view is guaranteed to take.
	fn get_int_lower_bound(&self, var: IntDecision) -> IntVal;

	/// Get the maximum value that an integer view is guaranteed to take.
	fn get_int_upper_bound(&self, var: IntDecision) -> IntVal;

	/// Convenience method to get both the lower and upper bounds of an integer
	/// view.
	fn get_int_bounds(&self, var: IntDecision) -> (IntVal, IntVal) {
		(self.get_int_lower_bound(var), self.get_int_upper_bound(var))
	}

	/// Get the current value of an integer view, if it has been assigned.
	fn get_int_val(&self, var: IntDecision) -> Option<IntVal> {
		let (lb, ub) = self.get_int_bounds(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}

	/// Enforce a boolean view to be `true`.
	///
	/// Note that it is possible to enforce that a boolean view is `false` by
	/// negating the view, i.e. `!bv`.
	fn set_bool(&mut self, bv: BoolDecision) -> Result<(), ReformulationError>;

	/// Enforce that the given integer expression takes a value in in the given
	/// set.
	fn set_int_in_set(
		&mut self,
		var: IntDecision,
		values: &IntSetVal,
	) -> Result<(), ReformulationError>;

	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val`.
	fn set_int_lower_bound(
		&mut self,
		var: IntDecision,
		val: IntVal,
	) -> Result<(), ReformulationError>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val`.
	fn set_int_upper_bound(
		&mut self,
		var: IntDecision,
		val: IntVal,
	) -> Result<(), ReformulationError>;

	/// Enforce that a an integer view takes a value `val`.
	fn set_int_val(&mut self, var: IntDecision, val: IntVal) -> Result<(), ReformulationError>;

	/// Enforce that a an integer view cannot take a value `val`.
	fn set_int_not_eq(&mut self, var: IntDecision, val: IntVal) -> Result<(), ReformulationError>;

	/// Enforce that a given integer expression cannot take any of the values in
	/// the given set.
	fn set_int_not_in_set(
		&mut self,
		var: IntDecision,
		values: &IntSetVal,
	) -> Result<(), ReformulationError>;
}

/// Basic actions that can be performed when the trailing infrastructure is
/// available.
pub trait TrailingActions {
	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
	/// Get the current value of a [`TrailedInt`].
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
	/// Change the value of a [`TrailedInt`] in a way that can be undone if the
	/// solver backtracks to a previous state.
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
}
