use crate::{actions::trailing::TrailingActions, BoolView, IntVal, IntView};

pub(crate) trait InspectionActions: TrailingActions {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool>;

	fn get_int_lower_bound(&self, var: IntView) -> IntVal;
	fn get_int_upper_bound(&self, var: IntView) -> IntVal;
	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		(self.get_int_lower_bound(var), self.get_int_upper_bound(var))
	}
	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		let (lb, ub) = self.get_int_bounds(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}
	#[allow(dead_code)]
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
}
