//! Module for the [`True`] helper type.

use std::ops::Not;

use crate::{
	BoolDecision,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, PropagationActions,
		ReasoningContext,
	},
	constraints::ReasonBuilder,
	solver::BoolView,
};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
/// Type that represents compile time constant [`true`] value.
pub struct True;

impl From<True> for BoolDecision {
	fn from(_: True) -> Self {
		true.into()
	}
}

impl From<True> for BoolView {
	fn from(_: True) -> Self {
		true.into()
	}
}

impl<Ctx> BoolInitActions<Ctx> for True
where
	bool: BoolInitActions<Ctx>,
{
	fn advise_when_fixed(&self, ctx: &mut Ctx, data: u64) {
		true.advise_when_fixed(ctx, data);
	}

	fn enqueue_when_fixed(&self, ctx: &mut Ctx) {
		true.enqueue_when_fixed(ctx);
	}
}

impl<Ctx> BoolInspectionActions<Ctx> for True {
	fn val(&self, _: &Ctx) -> Option<bool> {
		Some(true)
	}
}

impl<Ctx> BoolPropagationActions<Ctx> for True
where
	Ctx: ReasoningContext + PropagationActions,
{
	fn set_val(
		&self,
		ctx: &mut Ctx,
		val: bool,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		if !val {
			return Err(ctx.declare_conflict(reason));
		}
		Ok(())
	}
}

impl Not for True {
	type Output = bool;

	fn not(self) -> Self::Output {
		false
	}
}
