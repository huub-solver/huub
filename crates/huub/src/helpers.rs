//! Module containing general, e.g. purely numeric, structures or used in
//! multiple places in the library and are not exposed to the user.

pub(crate) mod bytes;
pub(crate) mod matrix;
pub mod overflow;
pub mod true_type;

use std::num::NonZero;

use crate::IntVal;

#[inline]
/// Integer division that rounds towards positive infinity.
pub(crate) fn div_ceil(a: IntVal, b: NonZero<IntVal>) -> IntVal {
	let d = a / b.get();
	let r = a % b.get();
	if (r > 0 && b.is_positive()) || (r < 0 && b.is_negative()) {
		d + 1
	} else {
		d
	}
}

/// Integer division that rounds towards negative infinity.
pub(crate) fn div_floor(a: IntVal, b: NonZero<IntVal>) -> IntVal {
	let d = a / b.get();
	let r = a % b.get();
	if (r > 0 && b.is_negative()) || (r < 0 && b.is_positive()) {
		d - 1
	} else {
		d
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use crate::helpers::{div_ceil, div_floor};

	#[test]
	fn test_div_ceil() {
		assert_eq!(div_ceil(8, NonZero::new(3).unwrap()), 3);
		assert_eq!(div_ceil(-8, NonZero::new(-3).unwrap()), 3);
		assert_eq!(div_ceil(8, NonZero::new(-3).unwrap()), -2);
		assert_eq!(div_ceil(-8, NonZero::new(3).unwrap()), -2);
	}

	#[test]
	fn test_div_floor() {
		assert_eq!(div_floor(8, NonZero::new(3).unwrap()), 2);
		assert_eq!(div_floor(-8, NonZero::new(-3).unwrap()), 2);
		assert_eq!(div_floor(8, NonZero::new(-3).unwrap()), -3);
		assert_eq!(div_floor(-8, NonZero::new(3).unwrap()), -3);
	}
}
