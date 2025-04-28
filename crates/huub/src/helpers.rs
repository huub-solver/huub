//! Module containing general, e.g. purely numeric, structures or used in
//! multiple places in the library and are not exposed to the user.

pub(crate) mod linear_transform;
pub(crate) mod opt_field;
pub(crate) mod trailed_list;
pub(crate) mod trailed_skip_list;

use std::mem;

use pindakaas::Var as RawVar;

use crate::{IntVal, NonZeroIntVal};

#[inline]
/// Helper function to deal with [`RawVar`] in data structure that have to
/// represent them as plain bytes.
pub(crate) fn var_from_u32(raw: u32) -> RawVar {
	// SAFETY: This is safe because RawVar uses the same representation as i32
	unsafe { mem::transmute::<u32, RawVar>(raw) }
}

#[inline]
/// Integer division that rounds towards positive infinity.
pub(crate) fn div_ceil(a: IntVal, b: NonZeroIntVal) -> IntVal {
	let d = a / b.get();
	let r = a % b.get();
	if (r > 0 && b.get() > 0) || (r < 0 && b.get() < 0) {
		d + 1
	} else {
		d
	}
}

/// Integer division that rounds towards negative infinity.
pub(crate) fn div_floor(a: IntVal, b: NonZeroIntVal) -> IntVal {
	let d = a / b.get();
	let r = a % b.get();
	if (r > 0 && b.get() < 0) || (r < 0 && b.get() > 0) {
		d - 1
	} else {
		d
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		helpers::{div_ceil, div_floor},
		NonZeroIntVal,
	};

	#[test]
	fn test_div_ceil() {
		assert_eq!(div_ceil(8, NonZeroIntVal::new(3).unwrap()), 3);
		assert_eq!(div_ceil(-8, NonZeroIntVal::new(-3).unwrap()), 3);
		assert_eq!(div_ceil(8, NonZeroIntVal::new(-3).unwrap()), -2);
		assert_eq!(div_ceil(-8, NonZeroIntVal::new(3).unwrap()), -2);
	}

	#[test]
	fn test_div_floor() {
		assert_eq!(div_floor(8, NonZeroIntVal::new(3).unwrap()), 2);
		assert_eq!(div_floor(-8, NonZeroIntVal::new(-3).unwrap()), 2);
		assert_eq!(div_floor(8, NonZeroIntVal::new(-3).unwrap()), -3);
		assert_eq!(div_floor(-8, NonZeroIntVal::new(3).unwrap()), -3);
	}
}
