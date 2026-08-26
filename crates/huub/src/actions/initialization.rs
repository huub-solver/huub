//! Actions available to [`Propagator`](crate::constraints::Propagator)
//! implementations during
//! [`Propagator::initialize`](crate::constraints::Propagator::initialize).

use crate::{
	actions::{
		ConstructionActions, DecisionActions, ReasoningContext,
		boolean::BoolInspectionActions,
		integer::{IntInspectionActions, IntPropCond},
	},
	solver::{DefaultView, View, branchers::BoxedBrancher, queue::PriorityLevel},
};

/// Actions available to [`Propagator`](crate::constraints::Propagator)
/// implementations in
/// [`ReasoningEngine::InitializationContext`](crate::actions::ReasoningEngine::InitializationContext)
/// for Boolean decision variables.
pub trait BoolInitActions<Context>: BoolInspectionActions<Context> {
	/// Advise the propagator when `self` is assigned, allowing the
	/// propagator to decide whether to enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// assignment, not just when it is not yet enqueued.
	///
	/// This will call
	/// [`Propagator::advise_of_bool_change`](crate::constraints::Propagator::advise_of_bool_change)
	/// on the propagator.
	fn advise_when_fixed(&self, ctx: &mut Context, data: u64);

	/// Remove the advisor that [`Self::advise_when_fixed`] registered with the
	/// given data, if it is still registered.
	///
	/// Note that the storage reserved for the advisor is not reclaimed.
	fn cancel_advise_when_fixed(&self, ctx: &mut Context, data: u64);

	/// Remove the subscription that [`Self::enqueue_when_fixed`] registered, if
	/// it is still registered.
	fn cancel_enqueue_when_fixed(&self, ctx: &mut Context);

	/// Enqueue the propagator when `self` is assigned.
	fn enqueue_when_fixed(&self, ctx: &mut Context);
}

/// Actions that can be performed during the initialization of branchers.
pub trait BrancherInitActions: ConstructionActions + DecisionActions {
	/// Ensure that any relevant decision variable are marked internally as a
	/// decidable variable.
	fn ensure_decidable<T: DefaultView>(&mut self, view: impl Into<View<T>>);

	/// Return the number of (propagator) subscriptions for the decision
	/// variable underlying the given view. Clauses in the SAT solver are
	/// included in the count.
	fn num_subscribers<T: DefaultView>(&self, view: View<T>) -> u32;

	/// Push a new [`Brancher`](crate::solver::branchers::Brancher) to the end
	/// of the solving branching queue.
	fn push_brancher(&mut self, brancher: BoxedBrancher);
}

/// Actions that can be performed when the propagator is posted.
pub trait InitActions {
	/// Advise a propagator when the solver backtracks.
	///
	/// This will call
	/// [`Propagator::advise_of_backtrack`](crate::constraints::Propagator::advise_of_backtrack)
	/// on the propagator.
	fn advise_on_backtrack(&mut self);

	/// Explicitly set whether the propagator should be enqueued immediately.
	fn enqueue_now(&mut self, enqueue: bool);

	/// Set the priority level at which the propagator will be enqueued.
	fn set_priority(&mut self, priority: PriorityLevel);
}

/// Actions available to [`Propagator`](crate::constraints::Propagator)
/// implementations in
/// [`ReasoningEngine::InitializationContext`](crate::actions::ReasoningEngine::InitializationContext)
/// for integer decision variables.
pub trait IntInitActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Advise the propagator when `self` is changed according to the given
	/// propagation condition, allowing the propagator to decide whether to
	/// enqueue itself.
	///
	/// Different from enqueueing, the propagator is always advised of the
	/// integer change, not just when it is not yet enqueued.
	///
	/// This will call
	/// [`Propagator::advise_of_int_change`](crate::constraints::Propagator::advise_of_int_change)
	/// on the propagator.
	fn advise_when(&self, ctx: &mut Context, condition: IntPropCond, data: u64);

	/// Remove the advisor that [`Self::advise_when`] registered for the given
	/// propagation condition and data, if it is still registered.
	///
	/// The propagation condition must be the one with which the advisor was
	/// registered, since an advisor is only found under its own condition.
	/// Note that the storage reserved for the advisor is not reclaimed.
	fn cancel_advise_when(&self, ctx: &mut Context, condition: IntPropCond, data: u64);

	/// Remove the subscription that [`Self::enqueue_when`] registered for the
	/// given propagation condition, if it is still registered.
	///
	/// The propagation condition must be the one with which the propagator
	/// subscribed, since a subscription is only found under its own condition.
	fn cancel_enqueue_when(&self, ctx: &mut Context, condition: IntPropCond);

	/// Enqueue the propagator when `self` is changed according to the given
	/// propagation condition.
	fn enqueue_when(&self, ctx: &mut Context, condition: IntPropCond);
}
