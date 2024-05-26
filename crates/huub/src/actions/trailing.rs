use crate::{solver::engine::trail::TrailedInt, IntVal};

pub(crate) trait TrailingActions {
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
}
