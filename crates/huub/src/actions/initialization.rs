use crate::{
	actions::decision::DecisionActions,
	solver::engine::{activation_list::IntPropCond, trail::TrailedInt},
	BoolView, IntVal, IntView, ReformulationError,
};

pub(crate) trait InitializationActions: DecisionActions {
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), ReformulationError>;
	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;
	/// Enqueue a propagator to be enqueued when a boolean variable is assigned.
	fn enqueue_on_bool_change(&mut self, var: BoolView);
	/// Enqueue a propagator to be enqueued when an integer variable is changed
	/// according to the given propagation condition.
	fn enqueue_on_int_change(&mut self, var: IntView, condition: IntPropCond);
}
