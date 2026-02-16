//! [`Model`].

//! Definitions for the default integer decision variable view employed in

use std::{
	num::NonZero,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::{
	IntSet, IntVal,
	actions::{
		BoolPropagationActions, IntDecisionActions, IntExplanationActions, IntInspectionActions,
		IntPropagationActions, IntSimplificationActions, PropagationActions, ReasoningContext,
	},
	constraints::{Conflict, ReasonBuilder, int_linear::IntEq},
	model::{
		Decision, Model, View,
		decision::integer::Domain,
		expressions::linear::IntLinearExp,
		view::{DefaultView, boolean::BoolView, private},
	},
	solver::IntLitMeaning,
	views::{LinearBoolView, LinearView},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
/// The internal representation of [`IntDecision`].
///
/// Note that this representation is not meant to be exposed to the user.
pub enum IntView {
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear(LinearView<NonZero<IntVal>, IntVal, Decision<IntVal>>),
	/// Linear View of an Boolean Literal.
	Bool(LinearBoolView<NonZero<IntVal>, IntVal, View<bool>>),
}

impl DefaultView for IntVal {
	type View = IntView;
}
impl private::Sealed for IntVal {}

impl View<IntVal> {
	/// Create a view that represents the addition of a constant value to the
	/// integer decision, while ensuring that the domain of the resulting view
	/// does not overflow by tightening the domain of the view.
	pub fn bounding_add<Ctx>(
		self,
		ctx: &mut Ctx,
		rhs: IntVal,
	) -> Result<View<IntVal>, Ctx::Conflict>
	where
		Ctx: PropagationActions + ReasoningContext + ?Sized,
		View<IntVal>: IntPropagationActions<Ctx>,
	{
		if rhs.is_positive() {
			let ub = self.max(ctx);
			if ub.checked_add(rhs).is_none() {
				if let Some(ub) = ub.checked_sub(rhs) {
					self.tighten_max(ctx, ub, [])?;
				} else {
					return Err(ctx.declare_conflict(|ctx: &mut Ctx| {
						[self.lit(ctx, IntLitMeaning::Less(IntVal::MIN))]
					}));
				}
			}
		} else {
			let lb = self.min(ctx);
			if lb.checked_add(rhs).is_none() {
				if let Some(lb) = lb.checked_sub(rhs) {
					self.tighten_min(ctx, lb, [])?;
				} else {
					// Real conflict subject cannot be represented.
					return Err(ctx.declare_conflict([]));
				}
			}
		}
		Ok(self + rhs)
	}

	/// Create a view that represents the multiplication between a constant
	/// value and an integer decision, while ensuring that the domain of the
	/// resulting view does not overflow by tightening the domain of the view.
	pub fn bounding_mul<Ctx>(
		self,
		ctx: &mut Ctx,
		rhs: IntVal,
	) -> Result<View<IntVal>, Ctx::Conflict>
	where
		Ctx: PropagationActions + ReasoningContext + ?Sized,
		View<IntVal>: IntPropagationActions<Ctx>,
	{
		let (lb, ub) = self.bounds(ctx);
		let (min, max) = if rhs.is_positive() {
			(IntVal::MIN, IntVal::MAX)
		} else {
			(IntVal::MAX, IntVal::MIN)
		};
		if lb.checked_mul(rhs).is_none() {
			if let Some(lb) = min.checked_div(rhs) {
				self.tighten_min(ctx, lb, [])?;
			} else {
				// Real conflict subject cannot be represented.
				return Err(ctx.declare_conflict([]));
			}
		}
		if ub.checked_mul(rhs).is_none() {
			if let Some(ub) = max.checked_div(rhs) {
				self.tighten_max(ctx, ub, [])?;
			} else {
				return Err(ctx.declare_conflict(|ctx: &mut Ctx| {
					[self.lit(ctx, IntLitMeaning::Less(IntVal::MIN))]
				}));
			}
		}

		Ok(self * rhs)
	}

	/// Create a view that represents the negation of an integer decision, while
	/// ensuring that the domain of the resulting view does not overflow by
	/// tightening the domain of the view.
	pub fn bounding_neg<Ctx>(self, ctx: &mut Ctx) -> Result<View<IntVal>, Ctx::Conflict>
	where
		Ctx: ReasoningContext + ?Sized,
		View<IntVal>: IntPropagationActions<Ctx>,
	{
		if self.min(ctx) == IntVal::MIN {
			self.tighten_min(ctx, -IntVal::MAX, [])?;
		}
		Ok(-self)
	}

	/// Create a view that represents the subtraction of a constant value from
	/// the integer decision, while ensuring that the domain of the resulting
	/// view does not overflow by tightening the domain of the view.
	pub fn bounding_sub<Ctx>(
		self,
		ctx: &mut Ctx,
		rhs: IntVal,
	) -> Result<View<IntVal>, Ctx::Conflict>
	where
		Ctx: PropagationActions + ReasoningContext + ?Sized,
		View<IntVal>: IntPropagationActions<Ctx>,
	{
		self.bounding_add(ctx, rhs.saturating_neg())
	}

	/// Get a Boolean view that represent whether the integer view is equal to
	/// the given value.
	pub fn eq(&self, v: IntVal) -> View<bool> {
		use IntView::*;

		match self.0 {
			Const(c) => (c == v).into(),
			Linear(lin) => match lin.reverse_meaning(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(val)) => View(BoolView::IntEq(lin.var, val)),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					false.into()
				}
				_ => unreachable!(),
			},
			Bool(lin) => match lin.reverse_meaning(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(1))  => lin.var,
				Ok(IntLitMeaning::Eq(0))  => !lin.var,
				Ok(IntLitMeaning::Eq(_)) /* if val != 0 */ => false.into(),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					false.into()
				}
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is greater
	/// than or equal to the given value.
	pub fn geq(&self, v: IntVal) -> View<bool> {
		!self.lt(v)
	}

	/// Get a Boolean view that represent whether the integer view is greater
	/// than the given value.
	pub fn gt(&self, v: IntVal) -> View<bool> {
		self.geq(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// or equal to the given value.
	pub fn leq(&self, v: IntVal) -> View<bool> {
		self.lt(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// the given value.
	pub fn lt(&self, v: IntVal) -> View<bool> {
		use IntView::*;

		match self.0 {
			Const(c) => (c < v).into(),
			Linear(lin) => match lin.reverse_meaning(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(val)) => View(BoolView::IntGreaterEq(lin.var, val)),
				Ok(IntLitMeaning::Less(val)) => View(BoolView::IntLess(lin.var, val)),
				_ => unreachable!(),
			},
			Bool(lin) => match lin.reverse_meaning(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(1)) => lin.var,
				Ok(IntLitMeaning::GreaterEq(val)) if val > 1 => false.into(),
				Ok(IntLitMeaning::GreaterEq(_)) /* if val <= 0 */ => true.into(),
				Ok(IntLitMeaning::Less(1)) => !lin.var,
				Ok(IntLitMeaning::Less(val)) if val > 1 => true.into(),
				Ok(IntLitMeaning::Less(_)) /* if val <= 0 */ => false.into(),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is not equal
	/// to the given value.
	pub fn ne(&self, v: IntVal) -> View<bool> {
		!self.eq(v)
	}

	/// Resolve any aliasing in the IntDecision, ensuring the result is a
	/// IntDecision that if it is a `Var` or `Linear`, then the domain is not an
	/// alias.
	pub(crate) fn resolve_alias(self, model: &Model) -> Self {
		use IntView::*;

		let mut view = self;
		let mut scale = 1;
		let mut offset = 0;
		loop {
			match view.0 {
				Const(c) => {
					return (c * scale + offset).into();
				}
				_ if scale == 0 => {
					return offset.into();
				}
				Linear(lin) => match model.int_vars[lin.var.idx()].domain {
					Domain::Domain(_) => {
						return View(Linear(lin * NonZero::new(scale).unwrap() + offset));
					}
					Domain::Alias(alias) => {
						view = alias;
						offset += scale * lin.offset;
						scale *= lin.scale.get();
					}
				},
				Bool(lin) => {
					let var = lin.var.resolve_alias(model);
					if let BoolView::Const(b) = var.0 {
						return View(Const(lin.transform_val(b as IntVal) * scale + offset));
					}
					return View(Bool(lin * NonZero::new(scale).unwrap() + offset));
				}
			}
		}
	}
}

impl Add<IntVal> for View<IntVal> {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		use IntView::*;

		if rhs == 0 {
			return self;
		}
		View(match self.0 {
			Const(v) => Const(v + rhs),
			Linear(lin) => Linear(lin + rhs),
			Bool(lin) => Bool(lin + rhs),
		})
	}
}

impl Add<View<IntVal>> for View<IntVal> {
	type Output = IntLinearExp;

	fn add(self, rhs: View<IntVal>) -> Self::Output {
		IntLinearExp {
			terms: vec![self, rhs],
		}
	}
}

impl AddAssign<IntVal> for View<IntVal> {
	fn add_assign(&mut self, rhs: IntVal) {
		use IntView::*;

		if rhs == 0 {
			return;
		}
		match &mut self.0 {
			Const(v) => *v += rhs,
			Linear(lin) => *lin += rhs,
			Bool(lin) => *lin += rhs,
		};
	}
}

impl From<Decision<IntVal>> for View<IntVal> {
	fn from(decision: Decision<IntVal>) -> Self {
		View(IntView::Linear(decision.into()))
	}
}

impl From<View<bool>> for View<IntVal> {
	fn from(value: View<bool>) -> Self {
		match value.0 {
			BoolView::Const(b) => (b as IntVal).into(),
			_ => View(IntView::Bool(value.into())),
		}
	}
}

impl From<i64> for View<IntVal> {
	fn from(value: i64) -> Self {
		View(IntView::Const(value))
	}
}

impl IntDecisionActions<Model> for View<IntVal> {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> View<bool> {
		IntInspectionActions::try_lit(self, ctx, meaning).unwrap()
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<View<bool>> {
		let val = self.val(ctx)?;
		Some(Self::eq(self, val))
	}
}

impl IntExplanationActions<Model> for View<IntVal> {
	fn lit_relaxed(&self, ctx: &Model, meaning: IntLitMeaning) -> (View<bool>, IntLitMeaning) {
		(self.try_lit(ctx, meaning).unwrap(), meaning)
	}
}

impl IntInspectionActions<Model> for View<IntVal> {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => (v, v),
			IntView::Linear(lin) => lin.bounds(ctx),
			IntView::Bool(lin) => lin.bounds(ctx),
		}
	}

	fn domain(&self, ctx: &Model) -> IntSet {
		match self.resolve_alias(ctx).0 {
			IntView::Const(c) => (c..=c).into(),
			IntView::Linear(lin) => lin.domain(ctx),
			IntView::Bool(lin) => lin.domain(ctx),
		}
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v == val,
			IntView::Linear(lin) => lin.in_domain(ctx, val),
			IntView::Bool(lin) => lin.in_domain(ctx, val),
		}
	}

	fn lit_meaning(&self, ctx: &Model, lit: View<bool>) -> Option<IntLitMeaning> {
		match self.0 {
			IntView::Const(_) => None,
			IntView::Linear(lin) => lin.lit_meaning(ctx, lit),
			IntView::Bool(lin) => lin.lit_meaning(ctx, lit),
		}
	}

	fn max(&self, ctx: &Model) -> IntVal {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v,
			IntView::Linear(lin) => lin.max(ctx),
			IntView::Bool(lin) => lin.max(ctx),
		}
	}

	fn max_lit(&self, ctx: &Model) -> View<bool> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(_) => true.into(),
			IntView::Linear(lin) => lin.max_lit(ctx),
			IntView::Bool(lin) => lin.max_lit(ctx),
		}
	}

	fn min(&self, ctx: &Model) -> IntVal {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v,
			IntView::Linear(lin) => lin.min(ctx),
			IntView::Bool(lin) => lin.min(ctx),
		}
	}

	fn min_lit(&self, ctx: &Model) -> View<bool> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(_) => true.into(),
			IntView::Linear(lin) => lin.min_lit(ctx),
			IntView::Bool(lin) => lin.min_lit(ctx),
		}
	}

	fn try_lit(&self, _: &Model, meaning: IntLitMeaning) -> Option<View<bool>> {
		Some(match meaning {
			IntLitMeaning::Eq(v) => self.eq(v),
			IntLitMeaning::NotEq(v) => self.ne(v),
			IntLitMeaning::GreaterEq(v) => self.geq(v),
			IntLitMeaning::Less(v) => self.lt(v),
		})
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => Some(v),
			IntView::Linear(lin) => lin.val(ctx),
			IntView::Bool(lin) => lin.val(ctx),
		}
	}
}

impl IntPropagationActions<Model> for View<IntVal> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.fix(ctx, val, reason),
			IntView::Linear(lin) => lin.fix(ctx, val, reason),
			IntView::Bool(lin) => lin.fix(ctx, val, reason),
		}
	}

	fn remove_val(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.remove_val(ctx, val, reason),
			IntView::Linear(lin) => lin.remove_val(ctx, val, reason),
			IntView::Bool(lin) => lin.remove_val(ctx, val, reason),
		}
	}

	fn tighten_max(
		&self,
		ctx: &mut Model,
		ub: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.tighten_max(ctx, ub, reason),
			IntView::Linear(lin) => lin.tighten_max(ctx, ub, reason),
			IntView::Bool(lin) => lin.tighten_max(ctx, ub, reason),
		}
	}

	fn tighten_min(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.tighten_min(ctx, val, reason),
			IntView::Linear(lin) => lin.tighten_min(ctx, val, reason),
			IntView::Bool(lin) => lin.tighten_min(ctx, val, reason),
		}
	}
}

impl IntSimplificationActions<Model> for View<IntVal> {
	fn exclude(
		&self,
		ctx: &mut Model,
		values: &IntSet,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.exclude(ctx, values, reason),
			IntView::Linear(lin) => lin.exclude(ctx, values, reason),
			IntView::Bool(lin) => lin.exclude(ctx, values, reason),
		}
	}

	fn restrict_domain(
		&self,
		ctx: &mut Model,
		values: &IntSet,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		match self.resolve_alias(ctx).0 {
			IntView::Const(v) => v.restrict_domain(ctx, values, reason),
			IntView::Linear(lin) => lin.restrict_domain(ctx, values, reason),
			IntView::Bool(lin) => lin.restrict_domain(ctx, values, reason),
		}
	}

	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Conflict<View<bool>>> {
		use IntView::*;

		let x = self.resolve_alias(ctx);
		let y = other.into().resolve_alias(ctx);

		let (idx, target) = match (x.0, y.0) {
			(x, y) if x == y => return Ok(()),
			(Bool(x), Bool(y)) => return x.unify(ctx, y),
			(Const(x), Const(y)) if x != y => return Err(ctx.declare_conflict([])),
			(Const(y), x) | (x, Const(y)) => {
				let x = View::<IntVal>(x);
				return x.fix(ctx, y, []);
			}
			(Linear(lin_x), Linear(lin_y)) => {
				// Decide which variable to redefine based on the other.
				let can_define_x = lin_y.scale.get() % lin_x.scale.get() == 0
					&& (lin_y.offset - lin_x.offset) % lin_x.scale.get() == 0;
				let can_define_y = lin_x.scale.get() % lin_y.scale.get() == 0
					&& (lin_x.offset - lin_y.offset) % lin_y.scale.get() == 0;
				let (lin_x, lin_y) = if can_define_x && can_define_y && lin_x.var.0 > lin_y.var.0 {
					(lin_x, lin_y)
				} else if can_define_y {
					(lin_y, lin_x)
				} else if can_define_x {
					(lin_x, lin_y)
				} else {
					ctx.post_constraint(IntEq { vars: [x, y] });
					return Ok(());
				};

				// Perform the transformation and add the aliasing domain to x:
				// x_scale * x + x_scale = y_scale * y + y_offset
				// === x = (y_scale / x_scale) * y + ((y_offset - x_offset) / x_scale)
				let scale = NonZero::new(lin_y.scale.get() / lin_x.scale.get()).unwrap();
				let offset = (lin_y.offset - lin_x.offset) / lin_x.scale.get();
				let target = View(Linear(LinearView::new(scale, offset, lin_y.var)));
				(lin_x.var, target)
			}
			(Linear(lin), Bool(b)) | (Bool(b), Linear(lin)) => {
				let lb = b.transform_val(0);
				let ub = b.transform_val(1);

				let contains_lb = lin.in_domain(ctx, lb);
				let contains_ub = lin.in_domain(ctx, ub);

				match (contains_lb, contains_ub) {
					(false, false) => {
						return Err(ctx.declare_conflict(|ctx: &mut Model| {
							[
								lin.lit(ctx, IntLitMeaning::NotEq(lb)),
								lin.lit(ctx, IntLitMeaning::NotEq(ub)),
							]
						}));
					}
					(false, true) => {
						lin.fix(ctx, ub, [])?;
						return b.var.require(ctx, |ctx: &mut Model| {
							[lin.lit(ctx, IntLitMeaning::NotEq(lb))]
						});
					}
					(true, false) => {
						lin.fix(ctx, lb, [])?;
						return b.var.fix(ctx, false, |ctx: &mut Model| {
							[lin.lit(ctx, IntLitMeaning::NotEq(ub))]
						});
					}
					(true, true) => {
						let Ok(IntLitMeaning::Eq(i_lb)) =
							lin.reverse_meaning(IntLitMeaning::Eq(lb))
						else {
							unreachable!()
						};
						let Ok(IntLitMeaning::Eq(i_ub)) =
							lin.reverse_meaning(IntLitMeaning::Eq(ub))
						else {
							unreachable!()
						};
						let target = View(Bool(LinearBoolView::new(
							NonZero::new(i_ub - i_lb).unwrap(),
							i_lb,
							b.var,
						)));

						(lin.var, target)
					}
				}
			}
		};

		idx.unify_internal(ctx, target)
	}
}

impl Mul<IntVal> for View<IntVal> {
	type Output = Self;

	fn mul(mut self, rhs: IntVal) -> Self::Output {
		self *= rhs;
		self
	}
}

impl Mul<NonZero<IntVal>> for View<IntVal> {
	type Output = Self;

	fn mul(mut self, rhs: NonZero<IntVal>) -> Self::Output {
		self *= rhs;
		self
	}
}

impl MulAssign<IntVal> for View<IntVal> {
	fn mul_assign(&mut self, rhs: IntVal) {
		if let Some(rhs) = NonZero::new(rhs) {
			*self *= rhs;
		} else {
			*self = 0.into();
		}
	}
}

impl MulAssign<NonZero<IntVal>> for View<IntVal> {
	fn mul_assign(&mut self, rhs: NonZero<IntVal>) {
		use IntView::*;

		match &mut self.0 {
			Const(v) => *v *= rhs.get(),
			Linear(lin) => *lin *= rhs,
			Bool(lin) => *lin *= rhs,
		}
	}
}

impl Neg for View<IntVal> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		use IntView::*;

		View(match self.0 {
			Const(v) => Const(-v),
			Linear(lin) => Linear(-lin),
			Bool(lin) => Bool(-lin),
		})
	}
}

impl Sub<IntVal> for View<IntVal> {
	type Output = Self;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl Sub<View<IntVal>> for View<IntVal> {
	type Output = <Self as Add<View<IntVal>>>::Output;

	fn sub(self, rhs: View<IntVal>) -> Self::Output {
		self + -rhs
	}
}

impl SubAssign<IntVal> for View<IntVal> {
	fn sub_assign(&mut self, rhs: IntVal) {
		*self += -rhs;
	}
}
