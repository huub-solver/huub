//! This module defines `ScaledView`, a lightweight wrapper that presents a
//! scaled view of an underlying integer variable or view: `y = scale * x`.

use std::{
	fmt::Debug,
	hash::Hash,
	mem,
	num::NonZero,
	ops::{Mul, MulAssign, Neg},
};

use crate::{
	DeepClone, IntSet, IntVal,
	actions::{
		IntAnalyzeActions, IntDecisionActions, IntExplanationActions, IntInspectionActions,
		IntPropagationActions, IntSimplificationActions, PropagationActions, PropagationContext,
		ReasoningContext,
	},
	helpers::{div_ceil, div_floor},
	solver::{
		IntLitMeaning, Polarity,
		solution::{Solution, Valuation},
	},
};

/// A scaled view over a decision variable: `y = scale * x`.
///
/// Decisions, explanations, inspections, and propagations are forwarded to the
/// underlying variable, translating values, bounds, and literals through that
/// mapping. Unlike [`LinearView`](crate::views::LinearView) there is no offset,
/// so the family is closed under negation and scaling, and a caller that must
/// not carry an offset cannot accidentally acquire one.
#[derive(Clone, Copy, Debug, DeepClone, Eq, Hash, PartialEq)]
pub struct ScaledView<Scale, Var> {
	/// Scale applied to the decision variable.
	pub(crate) scale: Scale,
	/// Underlying decision variable.
	pub(crate) var: Var,
}

impl<Var> ScaledView<NonZero<IntVal>, Var> {
	/// Reverses the transformation of an [`IntSetVal`].
	pub(crate) fn reverse_intset(&self, set: &IntSet) -> IntSet {
		if self.scale.is_positive() {
			IntSet::from_sorted_ranges(set.iter().map(|range| {
				let start = div_ceil(*range.start(), self.scale);
				let end = div_floor(*range.end(), self.scale);
				start..=end
			}))
		} else {
			IntSet::from_sorted_ranges(set.iter().rev().map(|range| {
				let start = div_ceil(*range.end(), self.scale);
				let end = div_floor(*range.start(), self.scale);
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
			IntLitMeaning::GreaterEq(v) if self.scale.is_negative() => {
				Ok(IntLitMeaning::Less(div_ceil(-v + 1, -self.scale)))
			}
			IntLitMeaning::GreaterEq(v) => Ok(IntLitMeaning::GreaterEq(div_ceil(v, self.scale))),
			// -a*x + b < i === a*x -b > -i === x >= (-i + 1 + b) / a
			IntLitMeaning::Less(v) if self.scale.is_negative() => {
				Ok(IntLitMeaning::GreaterEq(div_ceil(-v + 1, -self.scale)))
			}
			IntLitMeaning::Less(v) => Ok(IntLitMeaning::Less(div_ceil(v, self.scale))),
		}
	}

	/// Reverses the transformation of an [`IntVal`], rounding up.
	pub(crate) fn reverse_val_ceil(&self, val: IntVal) -> IntVal {
		div_ceil(val, self.scale)
	}

	/// Reverses the transformation of an [`IntVal`], rounding down.
	pub(crate) fn reverse_val_floor(&self, val: IntVal) -> IntVal {
		div_floor(val, self.scale)
	}

	/// Transform an [`IntLitMeaning`] from the variable given the view's scale.
	pub(crate) fn transform_meaning(&self, meaning: IntLitMeaning) -> IntLitMeaning {
		let neg_transform_val = |v| v * -self.scale.get();
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

	/// Transform an [`IntVal`] using the view's scale.
	pub(crate) fn transform_val(&self, val: IntVal) -> IntVal {
		self.scale.get() * val
	}

	/// Try to reverse the transformation of an [`IntVal`] without rounding.
	pub(crate) fn try_reverse_val(&self, val: IntVal) -> Option<IntVal> {
		if val % self.scale.get() == 0 {
			Some(val / self.scale.get())
		} else {
			None
		}
	}
}

impl<Scale, Var> ScaledView<Scale, Var> {
	/// Create a new scaled view with the given scale and variable.
	pub fn new(scale: Scale, var: Var) -> Self {
		Self { scale, var }
	}
}

impl<Var> From<Var> for ScaledView<NonZero<IntVal>, Var> {
	fn from(var: Var) -> Self {
		Self::new(NonZero::new(1).unwrap(), var)
	}
}

impl<Ctx, Var> IntAnalyzeActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Var: IntAnalyzeActions<Ctx>,
{
	fn polarity(&self, ctx: &mut Ctx, polarity: Polarity) {
		// A negative scale flips the desired direction onto the variable.
		let polarity = if self.scale.is_negative() {
			!polarity
		} else {
			polarity
		};
		self.var.polarity(ctx, polarity);
	}

	fn request_direct_eager(&self, ctx: &mut Ctx) {
		self.var.request_direct_eager(ctx);
	}

	fn request_order_eager(&self, ctx: &mut Ctx) {
		self.var.request_order_eager(ctx);
	}
}

impl<Ctx, Var> IntDecisionActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
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

impl<Ctx, Var> IntExplanationActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
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

impl<Ctx, Var> IntInspectionActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
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
			dom
		} else if self.scale.get() == -1 {
			IntSet::from_sorted_ranges(dom.into_iter().rev().map(|r| -r.end()..=-r.start()))
		} else if self.scale.is_positive() {
			IntSet::from_sorted_elements(dom.into_iter().flatten().map(|v| self.transform_val(v)))
		} else {
			IntSet::from_sorted_elements(
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

impl<Ctx, Var> IntPropagationActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntPropagationActions<Ctx>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
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
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
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
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
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
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
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

impl<Ctx, Var> IntSimplificationActions<Ctx> for ScaledView<NonZero<IntVal>, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntSimplificationActions<Ctx>,
{
	fn exclude(
		&self,
		ctx: &mut Ctx,
		values: &IntSet,
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
	) -> Result<(), Ctx::Conflict> {
		self.var.exclude(ctx, &self.reverse_intset(values), reason)
	}

	fn restrict_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSet,
		reason: impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>),
	) -> Result<(), Ctx::Conflict> {
		self.var
			.restrict_domain(ctx, &self.reverse_intset(domain), reason)
	}

	fn unify(
		&self,
		_ctx: &mut Ctx,
		_other: impl Into<Self>,
	) -> Result<(), <Ctx as PropagationContext>::Conflict> {
		panic!("unify cannot be defined for any generic ScaledView")
	}
}

impl<Var> Mul<NonZero<IntVal>> for ScaledView<NonZero<IntVal>, Var> {
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}

impl<Var> MulAssign<NonZero<IntVal>> for ScaledView<NonZero<IntVal>, Var> {
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		self.scale = NonZero::new(self.scale.get() * rhs.get()).unwrap();
	}
}

impl<Var> Neg for ScaledView<NonZero<IntVal>, Var> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		self * NonZero::new(-1).unwrap()
	}
}

impl<Var> Valuation for ScaledView<NonZero<IntVal>, Var>
where
	Var: Valuation<Val = IntVal>,
{
	type Val = IntVal;

	fn val(&self, sol: Solution<'_>) -> IntVal {
		self.transform_val(self.var.val(sol))
	}
}
