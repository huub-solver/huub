use crate::{
	actions::initialization::InitializationActions,
	propagator::Propagator,
	solver::engine::{propagation_context::PropagationContext, trail::Trail, State},
};

pub(crate) type BoxedPropagator = Box<dyn for<'a> Propagator<PropagationContext<'a>, State, Trail>>;

/// The trait used called to registering a propagator with the solver.
pub(crate) trait Poster {
	/// Register the propagator with the solver.
	///
	/// This method is expected to return the propagator to be registered and a
	/// boolean indicating whether the propagator should be placed in the
	/// propagation queue.
	///
	/// The post method is given access to the solver's initialization actions,
	/// which includes the ability to subscribe to variable events, creating
	/// trailed data structures, and inspecting the current state of varaibles.
	fn post<I: InitializationActions>(self, actions: &mut I) -> (BoxedPropagator, bool);
}
