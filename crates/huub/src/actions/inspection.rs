use crate::{actions::trailing::TrailingActions, IntVal, IntView};

pub(crate) trait InspectionActions: TrailingActions {
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
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
}
