use std::{num::NonZero, ops::Neg};

use rangelist::RangeList;

use crate::{
	actions::{
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		ReasoningContext,
	},
	constraints::ReasonBuilder,
	solver::IntLitMeaning,
	views::linear_view::LinearView,
	IntSetVal, IntVal,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct OffsetView<Offset, Var> {
	pub(crate) offset: Offset,
	pub(crate) var: Var,
}

impl<Offset, Var> OffsetView<Offset, Var> {
	pub(crate) fn new(offset: Offset, var: Var) -> Self {
		Self { offset, var }
	}
}

impl<Var> OffsetView<IntVal, Var> {
	fn reverse_meaning(&self, meaning: IntLitMeaning) -> IntLitMeaning {
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(v - self.offset),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(v - self.offset),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(v - self.offset),
			IntLitMeaning::Less(v) => IntLitMeaning::Less(v - self.offset),
		}
	}
}

impl<Ctx, Var> IntInspectionActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntInspectionActions<Ctx>,
{
	fn domain(&self, ctx: &Ctx) -> IntSetVal {
		RangeList::from_sorted_ranges(
			self.var
				.domain(ctx)
				.into_iter()
				.map(|r| (r.start() + self.offset)..=(r.end() + self.offset)),
		)
	}

	fn in_domain(&self, ctx: &Ctx, val: IntVal) -> bool {
		self.var.in_domain(ctx, val - self.offset)
	}

	fn lit_meaning(&self, ctx: &Ctx, lit: Ctx::Atom) -> Option<IntLitMeaning> {
		match self.var.lit_meaning(ctx, lit)? {
			IntLitMeaning::Eq(v) => Some(IntLitMeaning::Eq(v + self.offset)),
			IntLitMeaning::NotEq(v) => Some(IntLitMeaning::NotEq(v + self.offset)),
			IntLitMeaning::GreaterEq(v) => Some(IntLitMeaning::GreaterEq(v + self.offset)),
			IntLitMeaning::Less(v) => Some(IntLitMeaning::Less(v + self.offset)),
		}
	}

	fn lower_bound(&self, ctx: &Ctx) -> IntVal {
		self.var.lower_bound(ctx) + self.offset
	}

	fn lower_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.var.lower_bound_lit(ctx)
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		self.var.try_lit(ctx, self.reverse_meaning(meaning))
	}

	fn upper_bound(&self, ctx: &Ctx) -> IntVal {
		self.var.upper_bound(ctx) + self.offset
	}

	fn upper_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.var.upper_bound_lit(ctx)
	}

	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (lb, ub) = self.var.bounds(ctx);
		(lb + self.offset, ub + self.offset)
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		self.var.val(ctx).map(|v| v + self.offset)
	}
}

impl<Ctx, Var> IntExplanationActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntExplanationActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		self.var.lit_relaxed(ctx, self.reverse_meaning(meaning))
	}
}

impl<Ctx, Var> IntDecisionActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntDecisionActions<Ctx>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		self.var.lit(ctx, self.reverse_meaning(meaning))
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntPropagationActions<Ctx>,
{
	fn set_lower_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		self.var.set_lower_bound(ctx, val - self.offset, reason)
	}

	fn set_not_eq(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		self.var.set_not_eq(ctx, val - self.offset, reason)
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		self.var.set_upper_bound(ctx, val - self.offset, reason)
	}

	fn set_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		self.var.set_val(ctx, val - self.offset, reason)
	}
}

impl<Val: Default, Var> From<Var> for OffsetView<Val, Var> {
	fn from(value: Var) -> Self {
		Self {
			offset: Val::default(),
			var: value,
		}
	}
}

impl<Var> Neg for OffsetView<IntVal, Var> {
	type Output = LinearView<NonZero<IntVal>, IntVal, Var>;

	fn neg(self) -> Self::Output {
		let lin: LinearView<NonZero<IntVal>, IntVal, Var> = self.into();
		-lin
	}
}
