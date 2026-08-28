//! Module for the [`True`] helper type.

use std::ops::Not;

use crate::{
	DeepClone,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, PropagationActions,
		PropagationContext, ReasoningContext,
	},
	model, solver,
};

/// Type that represents compile time constant [`true`] value.
#[derive(Clone, Copy, Debug, DeepClone, Default, Eq, Hash, PartialEq)]
pub struct True;

impl<Ctx> BoolInitActions<Ctx> for True
where
	bool: BoolInitActions<Ctx>,
{
	fn advise_when_fixed(&self, ctx: &mut Ctx, data: u64) {
		true.advise_when_fixed(ctx, data);
	}

	fn cancel_advise_when_fixed(&self, ctx: &mut Ctx, data: u64) {
		true.cancel_advise_when_fixed(ctx, data);
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut Ctx) {
		true.cancel_enqueue_when_fixed(ctx);
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
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: bool,
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
	) -> Result<(), <Ctx as PropagationContext>::Conflict> {
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

impl From<True> for model::View<bool> {
	fn from(_: True) -> Self {
		true.into()
	}
}

impl From<True> for solver::View<bool> {
	fn from(_: True) -> Self {
		true.into()
	}
}
