use crate::{solver::engine::TrailedInt, IntVal};

pub(crate) trait TrailingActions {
	fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal);
}
