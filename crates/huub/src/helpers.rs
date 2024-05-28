pub(crate) mod linear_transform;
pub(crate) mod opt_field;
pub(crate) mod range_list;

use crate::{IntVal, NonZeroIntVal};

#[inline]
pub(crate) fn div_ceil(a: IntVal, b: NonZeroIntVal) -> IntVal {
	a / b.get() + (0 != a % b.get()) as IntVal
}

pub(crate) fn div_floor(a: IntVal, b: NonZeroIntVal) -> IntVal {
	a / b.get()
}
