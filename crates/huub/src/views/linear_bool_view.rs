//! with an affine transformation:
//!     value = scale * b + offset
//! where `b ∈ {0, 1}` corresponds to `{false, true}` respectively.
//! This module defines `LinearBoolView`, an integer view of a Boolean variable

use std::{
	fmt::Debug,
	hash::Hash,
	num::NonZero,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Not, Sub, SubAssign},
};

use rangelist::{IntervalIterator, RangeList};

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, BoolOperations, BoolPropagationActions, BoolSimplificationActions,
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions, PropagationActions, ReasoningContext,
	},
	constraints::ReasonBuilder,
	helpers::{div_ceil, div_floor},
	solver::{
		IntLitMeaning,
		solution::{BoolValuation, IntValuation, Solution},
	},
	views::offset_view::OffsetView,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// An (integer) linear view over a Boolean decision variable.
///
/// Conceptually, this view exposes a boolean `var ∈ {false, true}` as an
/// integer with an affine transformation:
///     value = scale * b + offset
/// where `b` is `0` for `false` and `1` for `true`.
///
/// This view represents an optimization over
/// [`LinearView`](crate::views::linear_view::LinearView) by ensuring that
/// the stored `scale` is strictly positive.
///
/// Examples:
/// ```rust,ignore
/// use std::num::NonZero;
/// // Suppose `v` is a boolean variable (implements BoolOperations).
/// let view = LinearBoolView::new(NonZero::new(2).unwrap(), 3, v.clone());
/// // value ∈ {3, 5}: false -> 3, true -> 5
///
/// // Negative scale is normalized automatically:
/// // false -> 7, true -> 5 is equivalent to true/false flipped:
/// let view_neg = LinearBoolView::new(NonZero::new(-2).unwrap(), 7, v.clone());
///
/// // Shifting and scaling:
/// let view2 = view + 10;       // Domain becomes {13, 15}
/// let view3 = view2 * NonZero::new(3).unwrap(); // {39, 45}, normalization if needed
///
/// // From a boolean variable directly (scale = 1, offset = 0):
/// let as_int = LinearBoolView::from(v.clone()); // Domain {0, 1}
/// ```
pub struct LinearBoolView<Scale, Offset, Var> {
	/// Scale applied to the decision variable.
	///
	/// Incumbent: scale is always positive.
	pub(crate) scale: Scale,
	/// Offset applied to the decision variable.
	pub(crate) offset: Offset,
	/// Underlying decision variable.
	pub(crate) var: Var,
}

impl<Var> LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Var: Not<Output = Var>,
{
	/// Create a new linear boolean view.
	pub fn new(scale: NonZero<IntVal>, offset: IntVal, var: Var) -> Self {
		if scale.get() <= 0 {
			Self {
				scale: -scale,
				offset: offset + scale.get(),
				var: !var,
			}
		} else {
			Self { scale, offset, var }
		}
	}
}

impl<Var> LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	/// Reverses the [`IntLitMeaning`] from its meaning on the view to the
	/// meaning of the variable.
	pub(crate) fn reverse_meaning(&self, meaning: IntLitMeaning) -> Result<IntLitMeaning, bool> {
		match meaning {
			IntLitMeaning::Eq(v) => self.try_reverse_val(v).map(IntLitMeaning::Eq).ok_or(false),
			IntLitMeaning::NotEq(v) => self
				.try_reverse_val(v)
				.map(IntLitMeaning::NotEq)
				.ok_or(true),
			IntLitMeaning::GreaterEq(v) => Ok(IntLitMeaning::GreaterEq(self.reverse_val_ceil(v))),
			IntLitMeaning::Less(v) => Ok(IntLitMeaning::Less(self.reverse_val_ceil(v))),
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
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(self.transform_val(v)),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(self.transform_val(v)),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(self.transform_val(v)),
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

impl<Var> Add<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self += rhs;
		self
	}
}

impl<Var> AddAssign<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn add_assign(&mut self, rhs: IntVal) {
		self.offset += rhs;
	}
}

impl<Var> From<OffsetView<IntVal, Var>> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn from(view: OffsetView<IntVal, Var>) -> Self {
		Self {
			scale: NonZero::new(1).unwrap(),
			offset: view.offset,
			var: view.var,
		}
	}
}

impl<Var> From<Var> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn from(var: Var) -> Self {
		Self {
			scale: NonZero::new(1).unwrap(),
			offset: 0,
			var,
		}
	}
}

impl<Ctx, Var> IntDecisionActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolInspectionActions<Ctx>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		self.try_lit(ctx, meaning).unwrap()
	}
}

impl<Ctx, Var> IntExplanationActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolInspectionActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		(self.try_lit(ctx, meaning).unwrap(), meaning)
	}
}

impl<Ctx, Var> IntInspectionActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolInspectionActions<Ctx>,
{
	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (lb, ub) = if let Some(val) = self.var.val(ctx) {
			(val as IntVal, val as IntVal)
		} else {
			(0, 1)
		};
		(self.transform_val(lb), self.transform_val(ub))
	}

	fn domain(&self, ctx: &Ctx) -> IntSet {
		if let Some(v) = self.var.val(ctx) {
			RangeList::from_sorted_elements([self.transform_val(v as IntVal)])
		} else {
			RangeList::from_sorted_elements([self.offset, self.scale.get() + self.offset])
		}
	}

	fn in_domain(&self, ctx: &Ctx, val: IntVal) -> bool {
		let Some(val) = self.try_reverse_val(val) else {
			return false;
		};
		if let Some(v) = self.var.val(ctx) {
			v as IntVal == val
		} else {
			val == 0 || val == 1
		}
	}

	fn lit_meaning(&self, _: &Ctx, lit: Ctx::Atom) -> Option<IntLitMeaning> {
		let atom: Ctx::Atom = self.var.clone().into();
		if atom == lit {
			Some(self.transform_meaning(IntLitMeaning::Eq(1)))
		} else if atom == !lit {
			Some(self.transform_meaning(IntLitMeaning::Eq(0)))
		} else {
			None
		}
	}

	fn max(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(self.var.val(ctx).unwrap_or(true) as IntVal)
	}

	fn max_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.var.val(ctx) == Some(false) {
			!Ctx::Atom::from(self.var.clone())
		} else {
			true.into()
		}
	}

	fn min(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(self.var.val(ctx).unwrap_or(false) as IntVal)
	}

	fn min_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.var.val(ctx) == Some(true) {
			self.var.clone().into()
		} else {
			true.into()
		}
	}

	fn try_lit(&self, _: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		Some(match self.reverse_meaning(meaning) {
			Ok(m) => match m {
				IntLitMeaning::Eq(1) | IntLitMeaning::NotEq(0) | IntLitMeaning::GreaterEq(1) => {
					self.var.clone().into()
				}
				IntLitMeaning::Eq(0) | IntLitMeaning::NotEq(1) | IntLitMeaning::Less(1) => {
					!Ctx::Atom::from(self.var.clone())
				}
				IntLitMeaning::Eq(_) => false.into(),
				IntLitMeaning::NotEq(_) => true.into(),
				IntLitMeaning::GreaterEq(v) if v <= 0 => true.into(),
				IntLitMeaning::GreaterEq(_) => false.into(),
				IntLitMeaning::Less(v) if v <= 0 => false.into(),
				IntLitMeaning::Less(_) => true.into(),
			},
			Err(b) => b.into(),
		})
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		Some(self.transform_val(self.var.val(ctx)? as IntVal))
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolPropagationActions<Ctx>,
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
		if (0..=1).contains(&val) {
			self.var.fix(ctx, val == 1, reason)
		} else {
			Err(ctx.declare_conflict(reason))
		}
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
		if (0..=1).contains(&val) {
			self.var.fix(ctx, val != 1, reason)
		} else {
			Ok(())
		}
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let val = self.reverse_val_floor(val);
		if val < 0 {
			Err(ctx.declare_conflict(reason))
		} else if val == 0 {
			self.var.fix(ctx, false, reason)
		} else {
			Ok(())
		}
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let val = self.reverse_val_ceil(val);
		if val > 1 {
			Err(ctx.declare_conflict(reason))
		} else if val == 1 {
			self.var.require(ctx, reason)
		} else {
			Ok(())
		}
	}
}

impl<Ctx, Var> IntSimplificationActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolSimplificationActions<Ctx>,
{
	fn exclude(
		&self,
		ctx: &mut Ctx,
		values: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let lb = values.contains(&self.offset);
		let ub = values.contains(&(self.offset + self.scale.get()));
		if lb && ub {
			Err(ctx.declare_conflict(reason))
		} else if ub {
			self.var.fix(ctx, false, reason)
		} else if lb {
			self.var.require(ctx, reason)
		} else {
			Ok(())
		}
	}

	fn restrict_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		let lb = domain.contains(&self.offset);
		let ub = domain.contains(&(self.offset + self.scale.get()));
		if lb && ub {
			Ok(())
		} else if ub {
			self.var.require(ctx, reason)
		} else if lb {
			self.var.fix(ctx, false, reason)
		} else {
			Err(ctx.declare_conflict(reason))
		}
	}

	fn unify(
		&self,
		ctx: &mut Ctx,
		other: impl Into<Self>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		let other = other.into();
		let (self_lb, self_ub) = self.bounds(ctx);
		let (other_lb, other_ub) = other.bounds(ctx);
		// self and other can only take two values each, given by their bounds.
		match (self_lb == other_lb, self_ub == other_ub) {
			(true, true) => self.var.unify(ctx, other.var),
			(true, false) => {
				self.var.fix(ctx, false, [])?;
				other.var.fix(ctx, false, [])
			}
			(false, true) => {
				self.var.fix(ctx, true, [])?;
				other.var.fix(ctx, true, [])
			}
			(false, false) if self_lb == other_ub => {
				self.var.fix(ctx, false, [])?;
				other.var.fix(ctx, true, [])
			}
			(false, false) if self_ub == other_lb => {
				self.var.fix(ctx, true, [])?;
				other.var.fix(ctx, false, [])
			}
			(false, false) => Err(ctx.declare_conflict([])),
		}
	}
}

impl<Var> IntValuation for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Var: BoolValuation,
{
	fn val(&self, sol: Solution<'_>) -> IntVal {
		let b = self.var.val(sol);
		self.transform_val(b as IntVal)
	}
}

impl<Var> Mul<NonZero<IntVal>> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Var: BoolOperations + Not<Output = Var>,
{
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}

impl<Var> MulAssign<NonZero<IntVal>> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Var: BoolOperations + Not<Output = Var>,
{
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		self.scale = NonZero::new(self.scale.get() * rhs.get()).unwrap();
		self.offset *= rhs.get();
		if self.scale.is_negative() {
			self.offset += self.scale.get();
			self.scale = -self.scale;
			self.var = !self.var.clone();
		}
	}
}

impl<Var> Neg for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Var: BoolOperations + Not<Output = Var>,
{
	type Output = Self;

	fn neg(self) -> Self::Output {
		self * NonZero::new(-1).unwrap()
	}
}

impl<Var> Sub<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn sub(mut self, rhs: IntVal) -> Self::Output {
		self -= rhs;
		self
	}
}

impl<Var> SubAssign<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.offset -= rhs;
	}
}
