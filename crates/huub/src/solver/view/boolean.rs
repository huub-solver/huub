//! Definitions for the default Boolean decision variable view employed in
//! [`Solver`].

use std::{
	num::NonZero,
	ops::{Add, Mul, Not},
};

use crate::{
	IntVal,
	actions::BoolInspectionActions,
	solver::{
		Decision,
		view::{DefaultView, View, private},
	},
	views::LinearBoolView,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`Lit` cannot be as small as `bool`"
)]
#[non_exhaustive]
/// The internal representation of a [`BoolView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub enum BoolView {
	/// A Boolean literal in the solver.
	Lit(Decision<bool>),
	/// A constant boolean value.
	Const(bool),
}

impl View<bool> {
	#[doc(hidden)]
	/// Return an integers that can used to identify the literal, if there is
	/// one.
	pub fn reverse_map_info(&self) -> Option<NonZero<i32>> {
		match self.0 {
			BoolView::Lit(v) => Some(v.0.into()),
			BoolView::Const(_) => None,
		}
	}
}

impl Add<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn add(self, rhs: IntVal) -> Self::Output {
		match self.0 {
			BoolView::Lit(lit) => (LinearBoolView::from(lit) + rhs).into(),
			BoolView::Const(b) => (b as IntVal + rhs).into(),
		}
	}
}

impl<Ctx> BoolInspectionActions<Ctx> for View<bool>
where
	Ctx: ?Sized,
	Decision<bool>: BoolInspectionActions<Ctx>,
{
	fn val(&self, ctx: &Ctx) -> Option<bool> {
		match self.0 {
			BoolView::Lit(lit) => lit.val(ctx),
			BoolView::Const(b) => Some(b),
		}
	}
}

impl From<Decision<bool>> for View<bool> {
	fn from(value: Decision<bool>) -> Self {
		View(BoolView::Lit(value))
	}
}

impl From<bool> for View<bool> {
	fn from(value: bool) -> Self {
		View(BoolView::Const(value))
	}
}

impl Mul<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			0.into()
		} else {
			self.mul(NonZero::new(rhs).unwrap())
		}
	}
}

impl Mul<NonZero<IntVal>> for View<bool> {
	type Output = View<IntVal>;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		match self.0 {
			BoolView::Lit(lit) => (LinearBoolView::from(lit) * rhs).into(),
			BoolView::Const(b) => (b as IntVal * rhs.get()).into(),
		}
	}
}

impl Not for View<bool> {
	type Output = Self;

	fn not(self) -> Self::Output {
		View(match self.0 {
			BoolView::Lit(l) => BoolView::Lit(!l),
			BoolView::Const(b) => BoolView::Const(!b),
		})
	}
}

impl DefaultView for bool {
	type View = BoolView;
}
impl private::Sealed for bool {}

impl From<View<bool>> for pindakaas::BoolVal {
	fn from(val: View<bool>) -> Self {
		match val.0 {
			BoolView::Lit(l) => l.0.into(),
			BoolView::Const(b) => b.into(),
		}
	}
}
