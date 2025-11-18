use std::{
	fmt::Debug,
	hash::Hash,
	mem,
	num::NonZero,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use rangelist::RangeList;

use crate::{
	actions::{
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		PropagationActions, ReasoningContext,
	},
	constraints::ReasonBuilder,
	helpers::{div_ceil, div_floor},
	solver::IntLitMeaning,
	views::offset_view::OffsetView,
	IntSetVal, IntVal,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LinearView<Scale, Offset, Var> {
	pub(crate) scale: Scale,
	pub(crate) offset: Offset,
	pub(crate) var: Var,
}

impl<Scale, Offset, Var> LinearView<Scale, Offset, Var> {
	pub(crate) fn new(scale: Scale, offset: Offset, var: Var) -> Self {
		Self { scale, offset, var }
	}
}

impl<Var> LinearView<NonZero<IntVal>, IntVal, Var> {
	fn reverse_meaning(&self, meaning: IntLitMeaning) -> Result<IntLitMeaning, bool> {
		match meaning {
			IntLitMeaning::Eq(v) => self.try_reverse_val(v).map(IntLitMeaning::Eq).ok_or(false),
			IntLitMeaning::NotEq(v) => self
				.try_reverse_val(v)
				.map(IntLitMeaning::NotEq)
				.ok_or(true),
			// -a*x + b >= i === a*x - b <= -i === x < (-i + 1 + b) / a
			IntLitMeaning::GreaterEq(v) if self.scale.get() < 0 => Ok(IntLitMeaning::Less(
				div_ceil(-v + 1 + self.offset, -self.scale),
			)),
			IntLitMeaning::GreaterEq(v) => Ok(IntLitMeaning::GreaterEq(div_ceil(
				v - self.offset,
				self.scale,
			))),
			// -a*x + b < i === a*x -b > -i === x >= (-i + 1 + b) / a
			IntLitMeaning::Less(v) if self.scale.get() < 0 => Ok(IntLitMeaning::GreaterEq(
				div_ceil(-v + 1 + self.offset, -self.scale),
			)),
			IntLitMeaning::Less(v) => {
				Ok(IntLitMeaning::Less(div_ceil(v - self.offset, self.scale)))
			}
		}
	}

	fn reverse_val_ceil(&self, val: IntVal) -> IntVal {
		div_ceil(val - self.offset, self.scale)
	}

	fn reverse_val_floor(&self, val: IntVal) -> IntVal {
		div_floor(val - self.offset, self.scale)
	}

	fn try_reverse_val(&self, val: IntVal) -> Option<IntVal> {
		let val = val - self.offset;
		if val % self.scale.get() == 0 {
			Some(val / self.scale.get())
		} else {
			None
		}
	}

	pub(crate) fn transform_val(&self, val: IntVal) -> IntVal {
		self.scale.get() * val + self.offset
	}

	pub(crate) fn transform_meaning(&self, meaning: IntLitMeaning) -> IntLitMeaning {
		let neg_transform_val = |v| (v * -self.scale.get()) - self.offset;
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(self.transform_val(v)),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(self.transform_val(v)),
			IntLitMeaning::GreaterEq(v) if self.scale.get() < 0 => {
				IntLitMeaning::Less(neg_transform_val(-v + 1))
			}
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(self.transform_val(v)),
			IntLitMeaning::Less(v) if self.scale.get() < 0 => {
				IntLitMeaning::GreaterEq(neg_transform_val(-v + 1))
			}
			IntLitMeaning::Less(v) => IntLitMeaning::Less(self.transform_val(v)),
		}
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
				(atom.into(), self.transform_meaning(meaning))
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
	fn domain(&self, ctx: &Ctx) -> IntSetVal {
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
		} else if self.scale.get() >= 0 {
			RangeList::from_sorted_elements(
				dom.into_iter().flatten().map(|v| self.transform_val(v)),
			)
		} else {
			RangeList::from_sorted_elements(
				dom.into_iter()
					.rev()
					.flatten()
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

	fn lower_bound(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(if self.scale.get() >= 0 {
			self.var.lower_bound(ctx)
		} else {
			self.var.upper_bound(ctx)
		})
	}

	fn lower_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.scale.get() >= 0 {
			self.var.lower_bound_lit(ctx)
		} else {
			self.var.upper_bound_lit(ctx)
		}
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		match self.reverse_meaning(meaning) {
			Ok(meaning) => self.try_lit(ctx, meaning),
			Err(b) => Some(b.into()),
		}
	}

	fn upper_bound(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(if self.scale.get() >= 0 {
			self.var.upper_bound(ctx)
		} else {
			self.var.lower_bound(ctx)
		})
	}

	fn upper_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.scale.get() >= 0 {
			self.var.upper_bound_lit(ctx)
		} else {
			self.var.lower_bound_lit(ctx)
		}
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		Some(self.transform_val(self.var.val(ctx)?))
	}

	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (mut lb, mut ub) = self.var.bounds(ctx);
		if self.scale.get() < 0 {
			mem::swap(&mut lb, &mut ub);
		}
		(self.transform_val(lb), self.transform_val(ub))
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for LinearView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
	Var: IntPropagationActions<Ctx>,
{
	fn set_lower_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		if self.scale.get() >= 0 {
			self.var
				.set_lower_bound(ctx, self.reverse_val_ceil(val), reason)
		} else {
			self.var
				.set_upper_bound(ctx, self.reverse_val_floor(val), reason)
		}
	}

	fn set_not_eq(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		let Some(val) = self.try_reverse_val(val) else {
			return Ok(());
		};
		self.var.set_not_eq(ctx, val, reason)
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		if self.scale.get() >= 0 {
			self.var
				.set_upper_bound(ctx, self.reverse_val_floor(val), reason)
		} else {
			self.var
				.set_lower_bound(ctx, self.reverse_val_ceil(val), reason)
		}
	}

	fn set_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		let Some(val) = self.try_reverse_val(val) else {
			return Err(ctx.declare_conflict(reason));
		};
		self.var.set_val(ctx, val, reason)
	}
}

impl<Var> From<Var> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn from(var: Var) -> Self {
		Self::new(NonZero::new(1).unwrap(), 0, var)
	}
}

impl<Var> From<OffsetView<IntVal, Var>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn from(view: OffsetView<IntVal, Var>) -> Self {
		Self::new(NonZero::new(1).unwrap(), view.offset, view.var)
	}
}

impl<Var> Neg for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		self * NonZero::new(-1).unwrap()
	}
}

impl<Var> AddAssign<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn add_assign(&mut self, rhs: IntVal) {
		self.offset += rhs;
	}
}

impl<Var> Add<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self += rhs;
		self
	}
}

impl<Var> SubAssign<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.offset -= rhs;
	}
}

impl<Var> Sub<IntVal> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn sub(mut self, rhs: IntVal) -> Self::Output {
		self -= rhs;
		self
	}
}

impl<Var> MulAssign<NonZero<IntVal>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		self.scale = NonZero::new(self.scale.get() * rhs.get()).unwrap();
		self.offset *= rhs.get();
	}
}

impl<Var> Mul<NonZero<IntVal>> for LinearView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}
