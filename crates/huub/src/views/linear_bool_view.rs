use std::{
	fmt::Debug,
	hash::Hash,
	num::NonZero,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use rangelist::{IntervalIterator, RangeList};

use crate::{
	actions::{
		BoolInspectionActions, BoolOperations, BoolPropagationActions, BoolSimplificationActions,
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions, PropagationActions, ReasoningContext,
	},
	constraints::ReasonBuilder,
	helpers::{div_ceil, div_floor},
	solver::IntLitMeaning,
	views::offset_view::OffsetView,
	IntSetVal, IntVal,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct LinearBoolView<Scale, Offset, Var> {
	pub(crate) scale: Scale,
	pub(crate) offset: Offset,
	pub(crate) var: Var,
}

impl<Var> LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	pub(crate) fn new(scale: NonZero<IntVal>, offset: IntVal, var: Var) -> Self {
		assert!(
			scale.get() >= 0,
			"LinearPosView::new: scale must be positive"
		);
		Self { scale, offset, var }
	}
}

impl<Var> LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn reverse_meaning(&self, meaning: IntLitMeaning) -> Result<IntLitMeaning, bool> {
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
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(self.transform_val(v)),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(self.transform_val(v)),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(self.transform_val(v)),
			IntLitMeaning::Less(v) => IntLitMeaning::Less(self.transform_val(v)),
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
	fn domain(&self, ctx: &Ctx) -> IntSetVal {
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
		} else if !atom == lit {
			Some(self.transform_meaning(IntLitMeaning::Eq(0)))
		} else {
			None
		}
	}

	fn lower_bound(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(self.var.val(ctx).unwrap_or(false) as IntVal)
	}

	fn lower_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
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
					(!self.var.clone()).into()
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

	fn upper_bound(&self, ctx: &Ctx) -> IntVal {
		self.transform_val(self.var.val(ctx).unwrap_or(true) as IntVal)
	}

	fn upper_bound_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		if self.var.val(ctx) == Some(false) {
			(!self.var.clone()).into()
		} else {
			true.into()
		}
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		Some(self.transform_val(self.var.val(ctx)? as IntVal))
	}

	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (lb, ub) = if let Some(val) = self.var.val(ctx) {
			(val as IntVal, val as IntVal)
		} else {
			(0, 1)
		};
		(self.transform_val(lb), self.transform_val(ub))
	}
}

impl<Ctx, Var> IntPropagationActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolPropagationActions<Ctx>,
{
	fn set_lower_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		let val = self.reverse_val_ceil(val);
		if val > 1 {
			Err(ctx.declare_conflict(reason))
		} else if val == 1 {
			self.var.set(ctx, reason)
		} else {
			Ok(())
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
		if val < 0 || val > 1 {
			Ok(())
		} else {
			self.var.set_val(ctx, val != 1, reason)
		}
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx, Ctx::Atom>,
	) -> Result<(), Ctx::Conflict> {
		let val = self.reverse_val_floor(val);
		if val < 0 {
			Err(ctx.declare_conflict(reason))
		} else if val == 0 {
			self.var.set_val(ctx, false, reason)
		} else {
			Ok(())
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
		if val < 0 || val > 1 {
			Err(ctx.declare_conflict(reason))
		} else {
			self.var.set_val(ctx, val == 1, reason)
		}
	}
}

impl<Ctx, Var> IntSimplificationActions<Ctx> for LinearBoolView<NonZero<IntVal>, IntVal, Var>
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: BoolOperations + From<bool> + From<Var>,
	Var: BoolSimplificationActions<Ctx>,
{
	fn set_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSetVal,
		reason: impl ReasonBuilder<Ctx, <Ctx as ReasoningContext>::Atom>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		let lb = domain.contains(&self.offset);
		let ub = domain.contains(&(self.offset + self.scale.get()));
		if lb && ub {
			Ok(())
		} else if ub {
			self.var.set(ctx, reason)
		} else if lb {
			self.var.set_val(ctx, false, reason)
		} else {
			Err(ctx.declare_conflict(reason))
		}
	}

	fn set_not_in_set(
		&self,
		ctx: &mut Ctx,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Ctx, <Ctx as ReasoningContext>::Atom>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		let lb = values.contains(&self.offset);
		let ub = values.contains(&(self.offset + self.scale.get()));
		if lb && ub {
			Err(ctx.declare_conflict(reason))
		} else if ub {
			self.var.set_val(ctx, false, reason)
		} else if lb {
			self.var.set(ctx, reason)
		} else {
			Ok(())
		}
	}

	fn unify(
		&self,
		ctx: &mut Ctx,
		other: impl Into<Self>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		todo!()
	}
}

impl<Var> From<Var> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn from(var: Var) -> Self {
		Self::new(NonZero::new(1).unwrap(), 0, var)
	}
}

impl<Var> From<OffsetView<IntVal, Var>> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn from(view: OffsetView<IntVal, Var>) -> Self {
		Self::new(NonZero::new(1).unwrap(), view.offset, view.var)
	}
}

impl<Var> AddAssign<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn add_assign(&mut self, rhs: IntVal) {
		self.offset += rhs;
	}
}

impl<Var> Add<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self += rhs;
		self
	}
}

impl<Var> SubAssign<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.offset -= rhs;
	}
}

impl<Var> Sub<IntVal> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn sub(mut self, rhs: IntVal) -> Self::Output {
		self -= rhs;
		self
	}
}

impl<Var: BoolOperations> Neg for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		self * NonZero::new(-1).unwrap()
	}
}

impl<Var: BoolOperations> MulAssign<NonZero<IntVal>>
	for LinearBoolView<NonZero<IntVal>, IntVal, Var>
{
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		self.scale = NonZero::new(self.scale.get() * rhs.get()).unwrap();
		self.offset *= rhs.get();
		if self.scale.get() < 0 {
			self.offset += self.scale.get();
			self.scale = -self.scale;
			self.var = !self.var.clone();
		}
	}
}

impl<Var: BoolOperations> Mul<NonZero<IntVal>> for LinearBoolView<NonZero<IntVal>, IntVal, Var> {
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}
