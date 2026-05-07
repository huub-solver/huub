//! Types and methods used to build integer linear constraints.

use std::{
	iter::Sum,
	mem,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use rustc_hash::FxHashMap;

use crate::{
	IntVal,
	model::{
		View,
		view::{boolean::BoolView, integer::IntView},
	},
};

/// Representation of a comparison operator.
pub(crate) enum Comparator {
	/// `<`, i.e. Less then
	Less,
	/// `<=`, i.e. Less than or equal to
	LessEqual,
	/// `==`, i.e. Equal to
	Equal,
	/// `>=`, i.e. Greater than or equal to
	GreaterEqual,
	/// `>`, i.e. Greater than
	Greater,
	/// `!=`, i.e. Not equal to
	NotEqual,
}

/// Object to help with the creation of integer linear constraints.
///
/// This object is generally created when [`View<IntVal>`] objects are added
/// together. Using the [`Model::linear`](crate::model::Model::linear) method,
/// these expressions can be used to create
/// [`IntLinear`](crate::constraints::int_linear::IntLinear) constraints and add
/// them to the [`Model`](crate::model::Model) .
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntLinearExp {
	/// The (linear transformation of) integer decision variables that are added
	/// together.
	pub(crate) terms: FxHashMap<View<IntVal>, IntVal>,
	/// Additional constant offset to add to the linear expression.
	pub(crate) offset: IntVal,
}

impl Add<IntLinearExp> for IntLinearExp {
	type Output = IntLinearExp;

	fn add(mut self, rhs: IntLinearExp) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<IntVal> for IntLinearExp {
	type Output = IntLinearExp;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<View<IntVal>> for IntLinearExp {
	type Output = IntLinearExp;

	fn add(mut self, rhs: View<IntVal>) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<View<bool>> for IntLinearExp {
	type Output = IntLinearExp;

	fn add(mut self, rhs: View<bool>) -> Self::Output {
		self += rhs;
		self
	}
}

impl AddAssign<IntLinearExp> for IntLinearExp {
	fn add_assign(&mut self, mut rhs: IntLinearExp) {
		if rhs.terms.len() > self.terms.len() {
			mem::swap(&mut self.terms, &mut rhs.terms);
		}
		for (var, scale) in rhs.terms {
			*self.terms.entry(var).or_default() += scale;
		}
		self.offset += rhs.offset;
	}
}

impl AddAssign<IntVal> for IntLinearExp {
	fn add_assign(&mut self, rhs: IntVal) {
		self.offset += rhs;
	}
}

impl AddAssign<View<IntVal>> for IntLinearExp {
	fn add_assign(&mut self, rhs: View<IntVal>) {
		match rhs.0 {
			IntView::Const(c) => self.offset += c,
			IntView::Linear(lin) => {
				let var_only: View<IntVal> = lin.var.into();
				let entry = self.terms.entry(var_only).or_default();
				*entry += lin.scale.get();
				self.offset += lin.offset;
			}
			IntView::Bool(lin) => {
				if let BoolView::Const(c) = lin.var.0 {
					self.offset += lin.transform_val(c as i64);
				} else {
					let (mut var, mut scale, mut offset) = (lin.var, lin.scale.get(), lin.offset);
					if matches!(var.0, BoolView::Decision(v) if v.is_negated())
						|| matches!(
							var.0,
							BoolView::IntNotEq(_, _) | BoolView::IntGreaterEq(_, _)
						) {
						var = !var;
						offset += scale;
						scale = -scale;
					}
					let entry = self.terms.entry(var.into()).or_default();
					*entry += scale;
					self.offset += offset;
				}
			}
		}
	}
}

impl AddAssign<View<bool>> for IntLinearExp {
	fn add_assign(&mut self, rhs: View<bool>) {
		let rhs: View<IntVal> = rhs.into();
		*self += rhs;
	}
}

impl From<IntVal> for IntLinearExp {
	fn from(offset: IntVal) -> Self {
		IntLinearExp {
			terms: FxHashMap::default(),
			offset,
		}
	}
}

impl From<View<IntVal>> for IntLinearExp {
	fn from(decision: View<IntVal>) -> Self {
		IntLinearExp::from(0) + decision
	}
}

impl Mul<IntVal> for IntLinearExp {
	type Output = IntLinearExp;

	fn mul(mut self, rhs: IntVal) -> Self::Output {
		self *= rhs;
		self
	}
}

impl MulAssign<IntVal> for IntLinearExp {
	fn mul_assign(&mut self, rhs: IntVal) {
		self.terms.iter_mut().for_each(|(_, mult)| *mult *= rhs);
		self.offset *= rhs;
	}
}

impl Neg for IntLinearExp {
	type Output = IntLinearExp;

	fn neg(mut self) -> Self::Output {
		self *= -1;
		self
	}
}

impl Sub<IntLinearExp> for IntLinearExp {
	type Output = IntLinearExp;

	fn sub(mut self, rhs: IntLinearExp) -> Self::Output {
		self -= rhs;
		self
	}
}

impl Sub<IntVal> for IntLinearExp {
	type Output = IntLinearExp;

	fn sub(mut self, rhs: IntVal) -> Self::Output {
		self -= rhs;
		self
	}
}

impl Sub<View<IntVal>> for IntLinearExp {
	type Output = IntLinearExp;

	fn sub(mut self, rhs: View<IntVal>) -> Self::Output {
		self -= rhs;
		self
	}
}

impl Sub<View<bool>> for IntLinearExp {
	type Output = IntLinearExp;

	fn sub(mut self, rhs: View<bool>) -> Self::Output {
		self -= rhs;
		self
	}
}

impl SubAssign<IntLinearExp> for IntLinearExp {
	fn sub_assign(&mut self, rhs: IntLinearExp) {
		self.add_assign(-rhs);
	}
}

impl SubAssign<IntVal> for IntLinearExp {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.offset -= rhs;
	}
}

impl SubAssign<View<IntVal>> for IntLinearExp {
	fn sub_assign(&mut self, rhs: View<IntVal>) {
		self.add_assign(-rhs);
	}
}

impl SubAssign<View<bool>> for IntLinearExp {
	fn sub_assign(&mut self, rhs: View<bool>) {
		self.add_assign(rhs * -1);
	}
}

impl Sum<IntLinearExp> for IntLinearExp {
	fn sum<I: Iterator<Item = IntLinearExp>>(iter: I) -> Self {
		let mut result = IntLinearExp::from(0);
		for item in iter {
			result += item;
		}
		result
	}
}

impl Sum<View<IntVal>> for IntLinearExp {
	fn sum<I: Iterator<Item = View<IntVal>>>(iter: I) -> Self {
		let mut result = IntLinearExp::from(0);
		for item in iter {
			result += item;
		}
		result
	}
}

impl Sum<View<bool>> for IntLinearExp {
	fn sum<I: Iterator<Item = View<bool>>>(iter: I) -> Self {
		let mut result = IntLinearExp::from(0);
		for item in iter {
			result += item;
		}
		result
	}
}
