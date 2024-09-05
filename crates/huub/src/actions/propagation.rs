use crate::{
	actions::{decision::DecisionActions, explanation::ExplanationActions},
	propagator::{
		conflict::Conflict,
		reason::{LazyReason, ReasonBuilder},
	},
	BoolView, IntVal, IntView,
};

pub(crate) trait PropagationActions: ExplanationActions + DecisionActions {
	fn set_bool_val(
		&mut self,
		bv: BoolView,
		val: bool,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;
	#[expect(dead_code, reason = "TODO: no current use case in propagators")]
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	fn deferred_reason(&self, data: u64) -> LazyReason;
}
