use crate::{actions::inspection::InspectionActions, BoolView, IntView, LitMeaning};

pub(crate) trait ExplanationActions: InspectionActions {
	fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
	/// Get a literal that represents the given meaning (that is currently `true`)
	/// or a relaxation if the literal does not yet exist.
	fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning);
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView>;
	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
}
