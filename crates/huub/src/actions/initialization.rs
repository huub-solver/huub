use crate::{
	actions::decision::DecisionActions, propagator::int_event::IntEvent,
	solver::engine::trail::TrailedInt, BoolView, IntVal, IntView, ReformulationError,
};

pub(crate) trait InitializationActions: DecisionActions {
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), ReformulationError>;
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
	fn subscribe_bool(&mut self, var: BoolView, data: u32);
	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32);
}
