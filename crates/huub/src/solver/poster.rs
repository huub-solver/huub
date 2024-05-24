use crate::{
	propagator::{int_event::IntEvent, Propagator},
	BoolView, IntView,
};

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
	fn post<I: InitializationActions>(self, actions: &mut I) -> (Box<dyn Propagator>, bool);
}

pub(crate) trait InitializationActions {
	fn subscribe_bool(&mut self, var: BoolView, data: u32);
	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32);
}
