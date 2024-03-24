pub(crate) mod all_different;
pub(crate) mod conflict;
pub(crate) mod init_action;
pub(crate) mod int_event;
pub(crate) mod propagation_action;
pub(crate) mod reason;

use std::fmt::Debug;

use pindakaas::Lit;

use crate::{
	propagator::{
		conflict::Conflict, init_action::InitializationActions,
		propagation_action::PropagationActions,
	},
	solver::engine::queue::PriorityLevel,
};

pub trait Propagator: Debug {
	/// The method called when registering a propagator with the solver. This
	/// method is generally used to register variable event subscriptions with the
	/// solver.
	fn initialize(&mut self, actions: &mut InitializationActions<'_>) {
		let _ = actions;
	}

	/// The method called by the solver to notify the propagator of a variable
	/// event to which it has subscribed. The propagator can choose a priority
	/// level if it wants to be placed in the propagation queue.
	///
	/// The [`data`] argument will contain the data that the propagater has set
	/// when subscribing to an event.
	fn notify_event(&mut self, data: u32) -> Option<PriorityLevel> {
		let _ = data;
		Some(PriorityLevel::Medium)
	}

	/// This method is called when the solver backtracks to a previous decision
	/// level.
	///
	/// Generally this method would be used to reset any values that depend on the
	/// previously made decisions.
	fn notify_backtrack(&mut self, new_level: usize) {
		let _ = new_level;
	}

	/// The propagate method is called during the search process to allow the
	/// propagator to enforce
	fn propagate(&mut self, actions: &mut PropagationActions<'_>) -> Result<(), Conflict> {
		let _ = actions;
		Ok(())
	}

	/// Explain a lazy reason that was emitted.
	///
	/// This method is called by the engine when a conflict is found involving a
	/// lazy explaination emitted by the propagator. The propagator must now
	/// produce the conjunction of literals that led to a literal being
	/// propagated.
	fn explain(&mut self, data: u64) -> Vec<Lit> {
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}
}
