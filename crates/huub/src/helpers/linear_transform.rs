use std::ops::{Add, Mul, Neg};

use crate::{helpers::div_ceil, IntVal, LitMeaning, NonZeroIntVal};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LinearTransform {
	pub(crate) scale: NonZeroIntVal,
	pub(crate) offset: IntVal,
}

impl LinearTransform {
	/// Creates a new linear transformation with the given scale and offset.
	pub fn new(scale: NonZeroIntVal, offset: IntVal) -> Self {
		Self { scale, offset }
	}
	/// Creates a new linear transformation with the given scale and no offset.
	pub fn scaled(scale: NonZeroIntVal) -> Self {
		Self { scale, offset: 0 }
	}
	/// Creates a new linear transformation with the given offset and no scale.
	pub fn offset(offset: IntVal) -> Self {
		Self {
			scale: NonZeroIntVal::new(1).unwrap(),
			offset,
		}
	}

	pub(crate) fn positive_scale(&self) -> bool {
		self.scale.get() > 0
	}

	/// Perform the linear transformation on a value.
	pub fn transform(&self, val: IntVal) -> IntVal {
		(val * self.scale.get()) + self.offset
	}

	/// Perform the linear tranformation for a `LitMeaning`.
	pub fn transform_lit(&self, mut lit: LitMeaning) -> LitMeaning {
		let mut transformer = *self;
		if !self.positive_scale() {
			// Make positive by doing `*-1` on lit meaning and transformer
			(lit, transformer) = match lit {
				// -x >= i === x <= -i === x < -i + 1
				LitMeaning::GreaterEq(i) => (LitMeaning::Less(-i + 1), -transformer),
				// -x < i === x > -i === x >= -i + 1
				LitMeaning::Less(i) => (LitMeaning::GreaterEq(-i + 1), -transformer),
				_ => (lit, transformer),
			};
		}

		match lit {
			LitMeaning::Eq(v) => LitMeaning::Eq(transformer.transform(v)),
			LitMeaning::NotEq(v) => LitMeaning::NotEq(transformer.transform(v)),
			LitMeaning::GreaterEq(v) => LitMeaning::GreaterEq(transformer.transform(v)),
			LitMeaning::Less(v) => LitMeaning::Less(transformer.transform(v)),
		}
	}

	/// Perform the reverse linear transformation on a value.
	pub fn rev_transform(&self, val: IntVal) -> IntVal {
		(val - self.offset) / self.scale.get()
	}

	/// Returns whether a value remains an integer after reversing the transformation.
	pub fn rev_remains_integer(&self, val: IntVal) -> bool {
		(val - self.offset) % self.scale.get() == 0
	}

	/// Perform the reverse linear tranformation for a `LitMeaning`.
	///
	/// Note that this performs the correct rounding to maintain the meaning of
	/// the literal.
	///
	/// If equality literals are requested that cannot be correctly rounded, then
	/// a boolean `Err` is returned with wether the `LitMeaning` implicitly holds.
	pub fn rev_transform_lit(&self, mut lit: LitMeaning) -> Result<LitMeaning, bool> {
		let mut transformer = *self;
		if !self.positive_scale() {
			// Make positive by doing `*-1` on lit meaning and transformer
			(lit, transformer) = match lit {
				// -x >= i === x <= -i === x < -i + 1
				LitMeaning::GreaterEq(i) => (LitMeaning::Less(-i + 1), -transformer),
				// -x < i === x > -i === x >= -i + 1
				LitMeaning::Less(i) => (LitMeaning::GreaterEq(-i + 1), -transformer),
				_ => (lit, transformer),
			};
		}

		match lit {
			LitMeaning::Eq(i) => {
				if transformer.rev_remains_integer(i) {
					Ok(LitMeaning::Eq(transformer.rev_transform(i)))
				} else {
					Err(false)
				}
			}
			LitMeaning::NotEq(i) => {
				if transformer.rev_remains_integer(i) {
					Ok(LitMeaning::NotEq(transformer.rev_transform(i)))
				} else {
					Err(true)
				}
			}
			LitMeaning::GreaterEq(i) => Ok(LitMeaning::GreaterEq(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
			LitMeaning::Less(i) => Ok(LitMeaning::Less(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
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

impl Neg for LinearTransform {
	type Output = Self;
	fn neg(self) -> Self::Output {
		Self {
			scale: NonZeroIntVal::new(-self.scale.get()).unwrap(),
			offset: -self.offset,
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

impl Mul<NonZeroIntVal> for LinearTransform {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		LinearTransform {
			scale: NonZeroIntVal::new(self.scale.get() * rhs.get()).unwrap(),
			offset: self.offset * rhs.get(),
		}
	}
}
