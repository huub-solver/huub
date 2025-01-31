//! Methods to perform linear transformations.

use std::ops::{Add, Mul, Neg};

use crate::{helpers::div_ceil, solver::IntLitMeaning, IntSetVal, IntVal, NonZeroIntVal};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// An integer linear transformation of a discrete value.
///
/// The transformation will take a discrete value `x` and transform it to `scale
/// * x + offset`. The transformation can also be reversed.
pub(crate) struct LinearTransform {
	/// The multiplicative scale.
	pub(crate) scale: NonZeroIntVal,
	/// The additive offset.
	pub(crate) offset: IntVal,
}

impl LinearTransform {
	/// Check whether the linear transformation is an identity transformation.
	pub(crate) fn is_identity(&self) -> bool {
		self.scale.get() == 1 && self.offset == 0
	}

	/// Creates a new linear transformation with the given offset and no scale.
	pub(crate) fn offset(offset: IntVal) -> Self {
		Self {
			scale: NonZeroIntVal::new(1).unwrap(),
			offset,
		}
	}

	/// Return whether the scale applied by the linear transformation is positive.
	pub(crate) fn positive_scale(&self) -> bool {
		self.scale.get() > 0
	}

	/// Returns whether a value remains an integer after reversing the transformation.
	pub(crate) fn rev_remains_integer(&self, val: IntVal) -> bool {
		(val - self.offset) % self.scale.get() == 0
	}

	/// Perform the reverse linear transformation on a value.
	pub(crate) fn rev_transform(&self, val: IntVal) -> IntVal {
		(val - self.offset) / self.scale.get()
	}

	/// Reverse the linear transformation on a set of integer values.
	pub(crate) fn rev_transform_int_set(&self, mask: &IntSetVal) -> IntSetVal {
		let get_val = |meaning| match meaning {
			IntLitMeaning::GreaterEq(i) => i,
			IntLitMeaning::Less(i) => i - 1,
			_ => unreachable!(),
		};

		mask.iter()
			.map(|r| {
				let a = get_val(
					self.rev_transform_lit(IntLitMeaning::GreaterEq(*r.start()))
						.unwrap(),
				);
				let b = get_val(
					self.rev_transform_lit(IntLitMeaning::Less(r.end() + 1))
						.unwrap(),
				);
				a.min(b)..=a.max(b)
			})
			.collect()
	}

	/// Perform the reverse linear tranformation for a `LitMeaning`.
	///
	/// Note that this performs the correct rounding to maintain the meaning of
	/// the literal.
	///
	/// If equality literals are requested that cannot be correctly rounded, then
	/// a boolean `Err` is returned with wether the `LitMeaning` implicitly holds.
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
					Ok(IntLitMeaning::Eq(transformer.rev_transform(i)))
				} else {
					Err(false)
				}
			}
			IntLitMeaning::NotEq(i) => {
				if transformer.rev_remains_integer(i) {
					Ok(IntLitMeaning::NotEq(transformer.rev_transform(i)))
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
	/// Creates a new linear transformation with the given scale and no offset.
	pub(crate) fn scaled(scale: NonZeroIntVal) -> Self {
		Self { scale, offset: 0 }
	}

	/// Perform the linear transformation on a value.
	pub(crate) fn transform(&self, val: IntVal) -> IntVal {
		(val * self.scale.get()) + self.offset
	}

	/// Perform the linear tranformation on a `LitMeaning`.
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
			scale: NonZeroIntVal::new(1).unwrap(),
			offset: 0,
		}
	}
}

impl Mul<NonZeroIntVal> for LinearTransform {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		LinearTransform {
			scale: NonZeroIntVal::new(self.scale.get() * rhs.get()).unwrap(),
			offset: self.offset * rhs.get(),
		}
	}
}

impl Neg for LinearTransform {
	type Output = Self;

	fn neg(self) -> Self::Output {
		Self {
			scale: NonZeroIntVal::new(-self.scale.get()).unwrap(),
			offset: -self.offset,
		}
	}
}
