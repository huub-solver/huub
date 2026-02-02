//! This module defines `OffsetView`, a lightweight wrapper that exposes a value
//! equal to an underlying integer variable plus a constant offset:
//!     y = x + offset

use std::{
	num::NonZero,
	ops::{Add, AddAssign, Neg},
};

use rangelist::RangeList;

use crate::{
	IntSet, IntVal,
	actions::{
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		ReasoningContext,
	},
	constraints::ReasonBuilder,
	solver::{
		IntLitMeaning,
		solution::{IntValuation, Solution},
	},
	views::linear_view::LinearView,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A view that applies a fixed additive offset to an underlying decision
/// variable.
///
/// OffsetView wraps a decision variable (or view) and exposes a value that is
/// shifted by a constant offset. Conceptually, if the underlying variable is
/// `x` and the offset is `c`, this view represents `x + c`.
///
/// Example:
/// ```ignore
/// // Suppose `x` is an integer view/variable and we want a view representing x + 5.
/// let x_plus_5 = OffsetView::new(5, x);
///
/// // Inspecting bounds applies the offset:
/// let lb = x_plus_5.lower_bound(ctx); // equals x.lower_bound(ctx) + 5
/// let ub = x_plus_5.upper_bound(ctx); // equals x.upper_bound(ctx) + 5
///
/// // Propagations are translated back:
/// x_plus_5.set_upper_bound(ctx, 12, reason)?; // sets x's upper bound to 12 - 5 = 7
///
/// // Literal meanings are consistently mapped:
/// let lit = x_plus_5.lit(ctx, IntLitMeaning::GreaterEq(10)); // internally uses x >= 5
/// ```
///
/// Note:
/// - For convenience, `From<Var>` is implemented when `Offset: Default`,
///   producing an offset view with zero offset.
/// - Negating an `OffsetView<IntVal, Var>` converts it into a `LinearView` and
///   applies negation.
///
/// See also:
/// - [`LinearView`] for general linear transformations of integer variables.
pub struct OffsetView<Offset, Var> {
	/// Offset applied to the decision variable.
	pub(crate) offset: Offset,
	/// Underlying decision variable.
	pub(crate) var: Var,
}

impl<Var> OffsetView<IntVal, Var> {
	/// Reverses the [`IntLitMeaning`] from its meaning on the view to the
	/// meaning of the variable.
	fn reverse_meaning(&self, meaning: IntLitMeaning) -> IntLitMeaning {
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(v - self.offset),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(v - self.offset),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(v - self.offset),
			IntLitMeaning::Less(v) => IntLitMeaning::Less(v - self.offset),
		}
	}
}

impl<Offset, Var> OffsetView<Offset, Var> {
	/// Creates a new offset view.
	pub fn new(offset: Offset, var: Var) -> Self {
		Self { offset, var }
	}
}

impl<Offset, Var> Add<Offset> for OffsetView<Offset, Var>
where
	Offset: AddAssign<Offset>,
{
	type Output = Self;

	fn add(mut self, rhs: Offset) -> Self::Output {
		self.offset += rhs;
		self
	}
}

impl<Offset, Var> AddAssign<Offset> for OffsetView<Offset, Var>
where
	Offset: AddAssign<Offset>,
{
	fn add_assign(&mut self, rhs: Offset) {
		self.offset += rhs;
	}
}

impl<Offset: Default, Var> From<Var> for OffsetView<Offset, Var> {
	fn from(value: Var) -> Self {
		Self {
			offset: Offset::default(),
			var: value,
		}
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

impl<Ctx, Var> IntExplanationActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntExplanationActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		self.var.lit_relaxed(ctx, self.reverse_meaning(meaning))
	}
}

impl<Ctx, Var> IntInspectionActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntInspectionActions<Ctx>,
{
	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (lb, ub) = self.var.bounds(ctx);
		(lb + self.offset, ub + self.offset)
	}

	fn domain(&self, ctx: &Ctx) -> IntSet {
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

	fn max(&self, ctx: &Ctx) -> IntVal {
		self.var.max(ctx) + self.offset
	}

	fn max_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.var.max_lit(ctx)
	}

	fn min(&self, ctx: &Ctx) -> IntVal {
		self.var.min(ctx) + self.offset
	}

	fn min_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.var.min_lit(ctx)
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		self.var.try_lit(ctx, self.reverse_meaning(meaning))
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		self.var.val(ctx).map(|v| v + self.offset)
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for OffsetView<IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntPropagationActions<Ctx>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var.fix(ctx, val - self.offset, reason)
	}

	fn remove_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var.remove_val(ctx, val - self.offset, reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var.tighten_max(ctx, val - self.offset, reason)
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var.tighten_min(ctx, val - self.offset, reason)
	}
}

impl<Var> IntValuation for OffsetView<IntVal, Var>
where
	Var: IntValuation,
{
	fn val(&self, sol: Solution<'_>) -> IntVal {
		self.var.val(sol) + self.offset
	}
}

impl<Var> Neg for OffsetView<IntVal, Var> {
	type Output = LinearView<NonZero<IntVal>, IntVal, Var>;

	fn neg(self) -> Self::Output {
		let lin: LinearView<NonZero<IntVal>, IntVal, Var> = self.into();
		-lin
	}
}
