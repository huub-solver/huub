use crate::{solver::engine::trail::TrailedInt, BoolView, IntVal};

pub(crate) trait TrailingActions {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
}
