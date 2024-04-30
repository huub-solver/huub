pub(crate) mod all_different;
pub(crate) mod conflict;
pub(crate) mod int_event;
pub(crate) mod reason;

use std::fmt::Debug;

use crate::{
	propagator::conflict::Conflict, solver::engine::queue::PriorityLevel, BoolView, Conjunction,
	IntVal, IntView, LitMeaning,
};

use self::{int_event::IntEvent, reason::ReasonBuilder};

pub(crate) trait Propagator: Debug + DynPropClone {
	/// The method called when registering a propagator with the solver, the method
	/// returns true when the propagator needs to be enqued immediately.œ
	///
	/// This method is generally used to register variable event
	/// subscriptions with the solver.
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		let _ = actions;
		false
	}

	/// The method called by the solver to notify the propagator of a variable
	/// event to which it has subscribed. The method returns true if the
	/// propagator should be placed in the propagation queue.
	///
	/// The [`data`] argument will contain the data that the propagater has set
	/// when subscribing to an event.
	fn notify_event(&mut self, data: u32) -> bool {
		let _ = data;
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
	fn explain(&mut self, data: u64) -> Conjunction {
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}
}

pub(crate) trait PropagationActions {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool>;

	fn set_bool_val(
		&mut self,
		bv: BoolView,
		val: bool,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict>;

	fn get_int_lit(&mut self, var: IntView, bv: LitMeaning) -> BoolView;
	fn get_int_lower_bound(&self, var: IntView) -> IntVal;
	fn get_int_upper_bound(&self, var: IntView) -> IntVal;
	fn get_int_val(&self, var: IntView) -> Option<IntVal>;
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict>;
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict>;
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict>;
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict>;
}

pub(crate) trait InitializationActions {
	fn subscribe_bool(&mut self, var: BoolView, data: u32);
	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32);
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
