use crate::{BoolView, IntView, LitMeaning};

use super::inspection::InspectionActions;

pub(crate) trait ExplanationActions: InspectionActions {
	fn get_int_lit(&self, var: IntView, meaning: LitMeaning) -> BoolView;
	#[allow(dead_code)]
	fn get_int_val_lit(&self, var: IntView) -> Option<BoolView> {
		self.get_int_val(var)
			.map(|v| self.get_int_lit(var, LitMeaning::Eq(v)))
	}
	fn get_int_lower_bound_lit(&self, var: IntView) -> BoolView {
		let lb = self.get_int_lower_bound(var);
		self.get_int_lit(var, LitMeaning::GreaterEq(lb))
	}
	fn get_int_upper_bound_lit(&self, var: IntView) -> BoolView {
		let ub = self.get_int_upper_bound(var);
		self.get_int_lit(var, LitMeaning::Less(ub + 1))
	}
}
