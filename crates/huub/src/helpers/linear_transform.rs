//! Methods to perform linear transformations.

use std::{
	num::NonZero,
	ops::{Add, Mul, Neg, RangeInclusive, Sub},
};

use crate::{IntSetVal, IntVal, helpers::div_ceil, solver::IntLitMeaning};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// An integer linear transformation of a discrete value.
///
/// The transformation will take a discrete value `x` and transform it to `scale
/// * x + offset`. The transformation can also be reversed.
pub(crate) struct LinearTransform {
	/// The multiplicative scale.
	pub(crate) scale: NonZero<IntVal>,
	/// The additive offset.
	pub(crate) offset: IntVal,
}

impl LinearTransform {
	/// Check whether the linear transformation can be divided by a divisor
	/// without remainder.
	pub(crate) fn can_divide_by(&self, divisor: IntVal) -> bool {
		self.scale.get() % divisor == 0 && self.offset % divisor == 0
	}

	/// Check whether the linear transformation is an identity transformation.
	pub(crate) fn is_identity(&self) -> bool {
		self.scale.get() == 1 && self.offset == 0
	}

	/// Creates a new linear transformation with the given offset and no scale.
	pub(crate) fn offset(offset: IntVal) -> Self {
		Self {
			scale: NonZero::new(1).unwrap(),
			offset,
		}
	}

	/// Return whether the scale applied by the linear transformation is
	/// positive.
	pub(crate) fn positive_scale(&self) -> bool {
		self.scale.is_positive()
	}

	/// Returns whether a value remains an integer after reversing the
	/// transformation.
	pub(crate) fn rev_remains_integer(&self, val: IntVal) -> bool {
		(val - self.offset) % self.scale.get() == 0
	}

	/// Reverse the linear transformation on a set of integer values.
	pub(crate) fn rev_transform_int_set(&self, mask: &IntSetVal) -> IntSetVal {
		mask.iter().map(|r| self.rev_transform_range(r)).collect()
	}

	/// Perform the reverse linear transformation for a `LitMeaning`.
	///
	/// Note that this performs the correct rounding to maintain the meaning of
	/// the literal.
	///
	/// If equality literals are requested that cannot be correctly rounded,
	/// then a boolean `Err` is returned with wether the `LitMeaning`
	/// implicitly holds.
	pub(crate) fn rev_transform_lit(&self, mut lit: IntLitMeaning) -> Result<IntLitMeaning, bool> {
		let mut transformer = *self;
		if !self.positive_scale() {
			// Make positive by doing `*-1` on lit meaning and transformer
			(lit, transformer) = match lit {
				// -x >= i === x <= -i === x < -i + 1
				IntLitMeaning::GreaterEq(i) => (IntLitMeaning::Less(-i + 1), -transformer),
				// -x < i === x > -i === x >= -i + 1
				IntLitMeaning::Less(i) => (IntLitMeaning::GreaterEq(-i + 1), -transformer),
				_ => (lit, transformer),
			};
		}

		match lit {
			IntLitMeaning::Eq(i) => {
				if transformer.rev_remains_integer(i) {
					Ok(IntLitMeaning::Eq(
						(i - transformer.offset) / transformer.scale.get(),
					))
				} else {
					Err(false)
				}
			}
			IntLitMeaning::NotEq(i) => {
				if transformer.rev_remains_integer(i) {
					Ok(IntLitMeaning::NotEq(
						(i - transformer.offset) / transformer.scale.get(),
					))
				} else {
					Err(true)
				}
			}
			IntLitMeaning::GreaterEq(i) => Ok(IntLitMeaning::GreaterEq(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
			IntLitMeaning::Less(i) => Ok(IntLitMeaning::Less(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
		}
	}

	/// Reverse the linear transformation on a range of integer values.
	fn rev_transform_range(&self, range: RangeInclusive<IntVal>) -> RangeInclusive<IntVal> {
		use IntLitMeaning::*;
		if self.positive_scale() {
			let Ok(GreaterEq(start)) = self.rev_transform_lit(GreaterEq(*range.start())) else {
				unreachable!()
			};
			let Ok(Less(end)) = self.rev_transform_lit(Less(*range.end() + 1)) else {
				unreachable!()
			};
			start..=(end - 1)
		} else {
			let Ok(Less(end)) = self.rev_transform_lit(GreaterEq(*range.start())) else {
				unreachable!()
			};
			let Ok(GreaterEq(start)) = self.rev_transform_lit(Less(*range.end() + 1)) else {
				unreachable!()
			};
			start..=(end - 1)
		}
	}

	/// Creates a new linear transformation with the given scale and no offset.
	pub(crate) fn scaled(scale: NonZero<IntVal>) -> Self {
		Self { scale, offset: 0 }
	}

	/// Perform the linear transformation on a value.
	pub(crate) fn transform(&self, val: IntVal) -> IntVal {
		(val * self.scale.get()) + self.offset
	}

	/// Perform the linear transformation on a `LitMeaning`.
	pub(crate) fn transform_lit(&self, mut lit: IntLitMeaning) -> IntLitMeaning {
		let mut transformer = *self;
		if !self.positive_scale() {
			// Make positive by doing `*-1` on lit meaning and transformer
			(lit, transformer) = match lit {
				// -x >= i === x <= -i === x < -i + 1
				IntLitMeaning::GreaterEq(i) => (IntLitMeaning::Less(-i + 1), -transformer),
				// -x < i === x > -i === x >= -i + 1
				IntLitMeaning::Less(i) => (IntLitMeaning::GreaterEq(-i + 1), -transformer),
				_ => (lit, transformer),
			};
		}

		match lit {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(transformer.transform(v)),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(transformer.transform(v)),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::GreaterEq(transformer.transform(v)),
			IntLitMeaning::Less(v) => IntLitMeaning::Less(transformer.transform(v)),
		}
	}
}

impl Add<IntVal> for LinearTransform {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		LinearTransform {
			scale: self.scale,
			offset: self.offset + rhs,
		}
	}
}

impl Default for LinearTransform {
	fn default() -> Self {
		Self {
			scale: NonZero::new(1).unwrap(),
			offset: 0,
		}
	}
}

impl Mul<NonZero<IntVal>> for LinearTransform {
	type Output = Self;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		LinearTransform {
			scale: NonZero::new(self.scale.get() * rhs.get()).unwrap(),
			offset: self.offset * rhs.get(),
		}
	}
}

impl Neg for LinearTransform {
	type Output = Self;

	fn neg(self) -> Self::Output {
		Self {
			scale: NonZero::new(-self.scale.get()).unwrap(),
			offset: -self.offset,
		}
	}
}

impl Sub<IntVal> for LinearTransform {
	type Output = Self;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self.add(-rhs)
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use crate::{IntLitMeaning, IntSetVal, LinearTransform};

	#[test]
	fn test_add() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		let result = lt + 2;
		assert_eq!(result.scale.get(), 3);
		assert_eq!(result.offset, 8);
	}

	#[test]
	fn test_can_divide_by() {
		let lt = LinearTransform {
			scale: NonZero::new(6).unwrap(),
			offset: 12,
		};
		assert!(lt.can_divide_by(3));
		assert!(!lt.can_divide_by(5));
	}

	#[test]
	fn test_default() {
		let lt = LinearTransform::default();
		assert_eq!(lt.scale.get(), 1);
		assert_eq!(lt.offset, 0);
		assert!(lt.is_identity());
	}

	#[test]
	fn test_is_identity() {
		let lt = LinearTransform {
			scale: NonZero::new(1).unwrap(),
			offset: 0,
		};
		assert!(lt.is_identity());

		let lt = LinearTransform {
			scale: NonZero::new(2).unwrap(),
			offset: 0,
		};
		assert!(!lt.is_identity());
	}

	#[test]
	fn test_mul() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		let result = lt * NonZero::new(2).unwrap();
		assert_eq!(result.scale.get(), 6);
		assert_eq!(result.offset, 12);
	}

	#[test]
	fn test_neg() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		let result = -lt;
		assert_eq!(result.scale.get(), -3);
		assert_eq!(result.offset, -6);
	}

	#[test]
	fn test_offset() {
		let lt = LinearTransform::offset(5);
		assert_eq!(lt.scale.get(), 1);
		assert_eq!(lt.offset, 5);
	}

	#[test]
	fn test_positive_scale() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 0,
		};
		assert!(lt.positive_scale());

		let lt = LinearTransform {
			scale: NonZero::new(-3).unwrap(),
			offset: 0,
		};
		assert!(!lt.positive_scale());
	}

	#[test]
	fn test_rev_remains_integer() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		assert!(lt.rev_remains_integer(9));
		assert!(!lt.rev_remains_integer(10));
	}

	#[test]
	fn test_rev_transform_int_set() {
		let lt = LinearTransform {
			scale: NonZero::new(2).unwrap(),
			offset: 4,
		};
		let set = IntSetVal::from_iter([4..=8]);
		let result = IntSetVal::from_iter([0..=2]);
		assert_eq!(lt.rev_transform_int_set(&set), result);
	}

	#[test]
	fn test_rev_transform_lit() {
		let lt = LinearTransform {
			scale: NonZero::new(2).unwrap(),
			offset: 4,
		};
		assert_eq!(
			lt.rev_transform_lit(IntLitMeaning::Eq(6)),
			Ok(IntLitMeaning::Eq(1))
		);
		assert_eq!(
			lt.rev_transform_lit(IntLitMeaning::NotEq(6)),
			Ok(IntLitMeaning::NotEq(1))
		);
		assert_eq!(
			lt.rev_transform_lit(IntLitMeaning::GreaterEq(6)),
			Ok(IntLitMeaning::GreaterEq(1))
		);
		assert_eq!(
			lt.rev_transform_lit(IntLitMeaning::Less(6)),
			Ok(IntLitMeaning::Less(1))
		);
	}

	#[test]
	fn test_scaled() {
		let lt = LinearTransform::scaled(NonZero::new(3).unwrap());
		assert_eq!(lt.scale.get(), 3);
		assert_eq!(lt.offset, 0);
	}

	#[test]
	fn test_sub() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		let result = lt - 2;
		assert_eq!(result.scale.get(), 3);
		assert_eq!(result.offset, 4);
	}

	#[test]
	fn test_transform() {
		let lt = LinearTransform {
			scale: NonZero::new(3).unwrap(),
			offset: 6,
		};
		assert_eq!(lt.transform(2), 12);
	}

	#[test]
	fn test_transform_lit() {
		let lt = LinearTransform {
			scale: NonZero::new(2).unwrap(),
			offset: 4,
		};
		assert_eq!(lt.transform_lit(IntLitMeaning::Eq(1)), IntLitMeaning::Eq(6));
		assert_eq!(
			lt.transform_lit(IntLitMeaning::NotEq(1)),
			IntLitMeaning::NotEq(6)
		);
		assert_eq!(
			lt.transform_lit(IntLitMeaning::GreaterEq(1)),
			IntLitMeaning::GreaterEq(6)
		);
		assert_eq!(
			lt.transform_lit(IntLitMeaning::Less(1)),
			IntLitMeaning::Less(6)
		);
	}
}
