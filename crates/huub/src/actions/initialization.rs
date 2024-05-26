use crate::{
	actions::inspection::InspectionActions, propagator::int_event::IntEvent,
	solver::engine::trail::TrailedInt, BoolView, IntVal, IntView,
};

pub(crate) trait InitializationActions: InspectionActions {
	fn subscribe_bool(&mut self, var: BoolView, data: u32);
	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32);
	#[allow(dead_code)]
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
}
