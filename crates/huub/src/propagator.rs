pub(crate) mod all_different_int;
pub(crate) mod array_int_minimum;
pub(crate) mod array_var_int_element;
pub(crate) mod conflict;
pub(crate) mod int_event;
pub(crate) mod int_lin_le;
pub(crate) mod int_times;
pub(crate) mod reason;

use std::fmt::Debug;

use self::int_event::IntEvent;
use crate::{
	actions::{explanation::ExplanationActions, propagation::PropagationActions},
	propagator::conflict::Conflict,
	solver::engine::queue::PriorityLevel,
	Conjunction,
};

pub(crate) trait Propagator: Debug + DynPropClone {
	/// The method called by the solver to notify the propagator of a variable
	/// event to which it has subscribed. The method returns true if the
	/// propagator should be placed in the propagation queue.
	///
	/// The [`data`] argument will contain the data that the propagater has set
	/// when subscribing to an event.
	fn notify_event(&mut self, data: u32, event: &IntEvent) -> bool {
		let _ = data;
		let _ = event;
		false
	}

	/// The method called by the solver to request at what priority level the
	/// propagator should be placed in the propagation queue.œ
	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Medium
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
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		let _ = actions;
		Ok(())
	}

	/// Explain a lazy reason that was emitted.
	///
	/// This method is called by the engine when a conflict is found involving a
	/// lazy explaination emitted by the propagator. The propagator must now
	/// produce the conjunction of literals that led to a literal being
	/// propagated.
	fn explain(&mut self, actions: &mut dyn ExplanationActions, data: u64) -> Conjunction {
		let _ = actions;
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}
}

pub(crate) trait DynPropClone {
	fn clone_dyn_prop(&self) -> Box<dyn Propagator>;
}
impl<P: Propagator + Clone + 'static> DynPropClone for P {
	fn clone_dyn_prop(&self) -> Box<dyn Propagator> {
		Box::new(self.clone())
	}
}
impl Clone for Box<dyn Propagator> {
	fn clone(&self) -> Box<dyn Propagator> {
		self.clone_dyn_prop()
	}
}
