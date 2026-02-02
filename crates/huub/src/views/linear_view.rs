//! This module defines `LinearView`, a lightweight wrapper that presents an
//! affine transformation of an underlying integer variable or view:
//!   y = scale * x + offset

use std::{
	fmt::Debug,
	hash::Hash,
	mem,
	num::NonZero,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use rangelist::RangeList;

use crate::{
	IntSet, IntVal,
	actions::{
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions, PropagationActions, ReasoningContext,
	},
	constraints::ReasonBuilder,
	helpers::{div_ceil, div_floor},
	solver::{
		IntLitMeaning,
		solution::{IntValuation, Solution},
	},
	views::offset_view::OffsetView,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A linear view over an decision variable: scale * x + offset
///
/// LinearView wraps a decision variable or view and presents an affine
/// transformation of it to the rest of the solver. All decisions, explanations,
/// inspections, and propagations are forwarded to the underlying variable while
/// translating values, bounds, and literals through the mapping y = scale * x +
/// offset
///
/// Examples
/// ```rust,ignore
/// use std::num::NonZero;
///
/// // Suppose `x` is an integer variable implementing the solver traits.
/// // Create y = 2*x + 3:
/// let mut y = LinearView::new(NonZero::new(2).unwrap(), 3, x);
///
/// // Adjust the view:
/// y += 5;                 // y = 2*x + 8
/// y *= NonZero::new(-1).unwrap(); // y = -2*x - 8
/// ```
pub struct LinearView<Scale, Offset, Var> {
	/// Scale applied to the decision variable.
	pub(crate) scale: Scale,
	/// Offset applied to the decision variable.
	pub(crate) offset: Offset,
	/// Underlying decision variable.
	pub(crate) var: Var,
}

impl<Var> LinearView<NonZero<IntVal>, IntVal, Var> {
	/// Reverses the transformation of an [`IntSetVal`].
	pub(crate) fn reverse_intset(&self, set: &IntSet) -> IntSet {
		if self.scale.is_positive() {
			RangeList::from_sorted_ranges(set.iter().map(|range| {
				let start = div_ceil(*range.start() - self.offset, self.scale);
				let end = div_floor(*range.end() - self.offset, self.scale);
				start..=end
			}))
		} else {
			RangeList::from_sorted_ranges(set.iter().rev().map(|range| {
				let start = div_ceil(range.end() - self.offset, self.scale);
				let end = div_floor(range.start() - self.offset, self.scale);
				start..=end
			}))
		}
	}

	/// Reverses the [`IntLitMeaning`] from its meaning on the view to the
	/// meaning of the variable.
	pub(crate) fn reverse_meaning(&self, meaning: IntLitMeaning) -> Result<IntLitMeaning, bool> {
		match meaning {
			IntLitMeaning::Eq(v) => self.try_reverse_val(v).map(IntLitMeaning::Eq).ok_or(false),
			IntLitMeaning::NotEq(v) => self
				.try_reverse_val(v)
				.map(IntLitMeaning::NotEq)
				.ok_or(true),
			// -a*x + b >= i === a*x - b <= -i === x < (-i + 1 + b) / a
			IntLitMeaning::GreaterEq(v) if self.scale.is_negative() => Ok(IntLitMeaning::Less(
				div_ceil(-v + 1 + self.offset, -self.scale),
			)),
			IntLitMeaning::GreaterEq(v) => Ok(IntLitMeaning::GreaterEq(div_ceil(
				v - self.offset,
				self.scale,
			))),
			// -a*x + b < i === a*x -b > -i === x >= (-i + 1 + b) / a
			IntLitMeaning::Less(v) if self.scale.is_negative() => Ok(IntLitMeaning::GreaterEq(
				div_ceil(-v + 1 + self.offset, -self.scale),
			)),
			IntLitMeaning::Less(v) => {
				Ok(IntLitMeaning::Less(div_ceil(v - self.offset, self.scale)))
			}
		}
	}

	/// Reverses the transformation of an [`IntVal`], rounding up.
	fn reverse_val_ceil(&self, val: IntVal) -> IntVal {
		div_ceil(val - self.offset, self.scale)
	}

	/// Reverses the transformation of an [`IntVal`], rounding down.
	fn reverse_val_floor(&self, val: IntVal) -> IntVal {
		div_floor(val - self.offset, self.scale)
	}

	/// Transform a [`IntLitMeaning`] from the variable given the view's scale
	/// and offset.
	pub(crate) fn transform_meaning(&self, meaning: IntLitMeaning) -> IntLitMeaning {
		let neg_transform_val = |v| (v * -self.scale.get()) - self.offset;
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(self.transform_val(v)),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(self.transform_val(v)),
			IntLitMeaning::GreaterEq(v) if self.scale.is_negative() => {
				IntLitMeaning::Less(neg_transform_val(-v + 1))
			}
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(self.transform_val(v)),
			IntLitMeaning::Less(v) if self.scale.is_negative() => {
				IntLitMeaning::GreaterEq(neg_transform_val(-v + 1))
			}
			IntLitMeaning::Less(v) => IntLitMeaning::Less(self.transform_val(v)),
		}
	}

	/// Transform a [`IntVal`] using the view's scale and offset.
	pub(crate) fn transform_val(&self, val: IntVal) -> IntVal {
		self.scale.get() * val + self.offset
	}

	/// Try to reverse the transformation of an [`IntVal`] without rounding.
	fn try_reverse_val(&self, val: IntVal) -> Option<IntVal> {
		let val = val - self.offset;
		if val % self.scale.get() == 0 {
			Some(val / self.scale.get())
		} else {
			None
		}
	}
}

impl<Scale, Offset, Var> LinearView<Scale, Offset, Var> {
	/// Create a new linear view with the given scale, offset, and variable.
	pub fn new(scale: Scale, offset: Offset, var: Var) -> Self {
		Self { scale, offset, var }
	}
}

impl<Var> Add<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self += rhs;
		self
	}
}

impl<Var> AddAssign<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn add_assign(&mut self, rhs: IntVal) {
		self.offset += rhs;
	}
}

impl<Var> From<OffsetView<IntVal, Var>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn from(view: OffsetView<IntVal, Var>) -> Self {
		Self::new(NonZero::new(1).unwrap(), view.offset, view.var)
	}
}

impl<Var> From<Var> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn from(var: Var) -> Self {
		Self::new(NonZero::new(1).unwrap(), 0, var)
	}
}

impl<Ctx, Var> IntDecisionActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntDecisionActions<Ctx>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		match self.reverse_meaning(meaning) {
			Ok(meaning) => self.var.lit(ctx, meaning),
			Err(b) => b.into(),
		}
	}
}

impl<Ctx, Var> IntExplanationActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntExplanationActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		match self.reverse_meaning(meaning) {
			Ok(meaning) => {
				let (atom, meaning) = self.var.lit_relaxed(ctx, meaning);
				(atom, self.transform_meaning(meaning))
			}
			Err(b) => (b.into(), meaning),
		}
	}
}

impl<Ctx, Var> IntInspectionActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntInspectionActions<Ctx>,
{
	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (mut lb, mut ub) = self.var.bounds(ctx);
		if self.scale.is_negative() {
			mem::swap(&mut lb, &mut ub);
		}
		(self.transform_val(lb), self.transform_val(ub))
	}

	fn domain(&self, ctx: &Ctx) -> IntSet {
		let dom = self.var.domain(ctx);
		if self.scale.get() == 1 {
			RangeList::from_sorted_ranges(
				dom.into_iter()
					.map(|r| (r.start() + self.offset)..=(r.end() + self.offset)),
			)
		} else if self.scale.get() == -1 {
			RangeList::from_sorted_ranges(
				dom.into_iter()
					.rev()
					.map(|r| -r.end() + self.offset..=-r.start() + self.offset),
			)
		} else if self.scale.is_positive() {
			RangeList::from_sorted_elements(
				dom.into_iter().flatten().map(|v| self.transform_val(v)),
			)
		} else {
			RangeList::from_sorted_elements(
				dom.into_iter()
					.flatten()
					.rev()
					.map(|v| self.transform_val(v)),
			)
		}
	}

	fn in_domain(&self, ctx: &Ctx, val: IntVal) -> bool {
		let Some(val) = self.try_reverse_val(val) else {
			return false;
		};
		self.var.in_domain(ctx, val)
	}

	fn lit_meaning(&self, ctx: &Ctx, lit: Ctx::Atom) -> Option<IntLitMeaning> {
		Some(self.transform_meaning(self.var.lit_meaning(ctx, lit)?))
	}

	fn max(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(if self.scale.get() >= 0 {
			self.var.max(ctx)
		} else {
			self.var.min(ctx)
		})
	}

	fn max_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.scale.get() >= 0 {
			self.var.max_lit(ctx)
		} else {
			self.var.min_lit(ctx)
		}
	}

	fn min(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(if self.scale.get() >= 0 {
			self.var.min(ctx)
		} else {
			self.var.max(ctx)
		})
	}

	fn min_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.scale.get() >= 0 {
			self.var.min_lit(ctx)
		} else {
			self.var.max_lit(ctx)
		}
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		match self.reverse_meaning(meaning) {
			Ok(meaning) => self.var.try_lit(ctx, meaning),
			Err(b) => Some(b.into()),
		}
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		Some(self.transform_val(self.var.val(ctx)?))
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntPropagationActions<Ctx>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let Some(val) = self.try_reverse_val(val) else {
			return Err(ctx.declare_conflict(reason));
		};
		self.var.fix(ctx, val, reason)
	}

	fn remove_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let Some(val) = self.try_reverse_val(val) else {
			return Ok(());
		};
		self.var.remove_val(ctx, val, reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if self.scale.get() >= 0 {
			self.var
				.tighten_max(ctx, self.reverse_val_floor(val), reason)
		} else {
			self.var
				.tighten_min(ctx, self.reverse_val_ceil(val), reason)
		}
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if self.scale.get() >= 0 {
			self.var
				.tighten_min(ctx, self.reverse_val_ceil(val), reason)
		} else {
			self.var
				.tighten_max(ctx, self.reverse_val_floor(val), reason)
		}
	}
}

impl<Ctx, Var> IntSimplificationActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntSimplificationActions<Ctx>,
{
	fn exclude(
		&self,
		ctx: &mut Ctx,
		values: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var.exclude(ctx, &self.reverse_intset(values), reason)
	}

	fn restrict_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.var
			.restrict_domain(ctx, &self.reverse_intset(domain), reason)
	}

	fn unify(
		&self,
		_ctx: &mut Ctx,
		_other: impl Into<Self>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		panic!("unify cannot be defined for any generic LinearView")
	}
}

impl<Var> IntValuation for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Var: IntValuation,
{
	fn val(&self, sol: Solution<'_>) -> IntVal {
		self.transform_val(self.var.val(sol))
	}
}

impl<Var> Mul<NonZero<IntVal>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}

impl<Var> MulAssign<NonZero<IntVal>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		self.scale = NonZero::new(self.scale.get() * rhs.get()).unwrap();
		self.offset *= rhs.get();
	}
}

impl<Var> Neg for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		self * NonZero::new(-1).unwrap()
	}
}

impl<Var> Sub<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn sub(mut self, rhs: IntVal) -> Self::Output {
		self -= rhs;
		self
	}
}

impl<Var> SubAssign<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.offset -= rhs;
	}
}
