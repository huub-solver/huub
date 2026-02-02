//! Types and methods used to build integer linear constraints.

use std::{
	iter::Sum,
	ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};

use crate::{IntVal, model::View};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Object to help with the creation of integer linear constraints.
///
/// This object is generally created when [`View<IntVal>`] objects are added
/// together. Using the [`Model::linear`](crate::model::Model::linear) method,
/// these expressions can be used to create
/// [`IntLinear`](crate::constraints::int_linear::IntLinear) constraints and add
/// them to the [`Model`](crate::model::Model) .
pub struct IntLinearExp {
	/// The (linear transformation of) integer decision variables that are added
	/// together.
	pub(crate) terms: Vec<View<IntVal>>,
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

impl AddAssign<IntVal> for IntLinearExp {
	fn add_assign(&mut self, rhs: IntVal) {
		self.terms[0] += rhs;
	}
}

impl AddAssign<View<IntVal>> for IntLinearExp {
	fn add_assign(&mut self, rhs: View<IntVal>) {
		self.terms.push(rhs);
	}
}

impl From<IntVal> for IntLinearExp {
	fn from(v: IntVal) -> Self {
		IntLinearExp {
			terms: vec![v.into()],
		}
	}
}

impl From<View<IntVal>> for IntLinearExp {
	fn from(decision: View<IntVal>) -> Self {
		IntLinearExp {
			terms: vec![decision],
		}
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
		self.terms.iter_mut().for_each(|x| *x *= rhs);
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

impl SubAssign<IntVal> for IntLinearExp {
	fn sub_assign(&mut self, rhs: IntVal) {
		self.terms[0] -= rhs;
	}
}

impl SubAssign<View<IntVal>> for IntLinearExp {
	fn sub_assign(&mut self, rhs: View<IntVal>) {
		self.terms.push(-rhs);
	}
}

impl Sum<View<IntVal>> for IntLinearExp {
	fn sum<I: Iterator<Item = View<IntVal>>>(iter: I) -> Self {
		IntLinearExp {
			terms: iter.collect(),
		}
	}
}
