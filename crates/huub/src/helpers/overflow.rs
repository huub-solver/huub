//! Module that contains helpers for handling overflow in arithmetic operations.

use std::{
	fmt,
	iter::Sum,
	ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

use crate::{IntVal, helpers::private::Sealed};

/// Type alias for a integer value that has double the bit width of [`IntVal`].
pub(crate) type DoubleIntVal = i128;

#[expect(
	private_bounds,
	reason = "OverflowPossible and OverflowImpossible are the only allowed implementations"
)]
/// Helper trait that defines the capabilities of [`OverflowPossible`] and
/// [`OverflowImpossible`] that can be used in [`Propagator`] implementations.
pub trait OverflowMode: Sealed + Clone + fmt::Debug + 'static {
	/// Constant indicating whether overflow should be handled.
	const HANDLE_OVERFLOW: bool;

	/// Type used for accumulating values
	type Accumulator: Add<Output = Self::Accumulator>
		+ AddAssign
		+ Copy
		+ Clone
		+ fmt::Debug
		+ fmt::Display
		+ From<IntVal>
		+ Into<DoubleIntVal>
		+ Neg<Output = Self::Accumulator>
		+ Ord
		+ Sub<Output = Self::Accumulator>
		+ SubAssign
		+ Sum
		+ TryInto<IntVal>;
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
/// Marker type indicating that overflow might be possible, and should be
/// handled by the [`Propagator`].
pub struct OverflowPossible;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
/// Marker type indicating that overflow is impossible, and does not need to be
/// handled by the [`Propagator`].
pub struct OverflowImpossible;

impl OverflowMode for OverflowPossible {
	const HANDLE_OVERFLOW: bool = true;
	type Accumulator = DoubleIntVal;
}

impl OverflowMode for OverflowImpossible {
	const HANDLE_OVERFLOW: bool = false;
	type Accumulator = IntVal;
}

#[cfg(test)]
mod tests {

	use crate::{
		IntVal,
		helpers::overflow::{DoubleIntVal, OverflowImpossible, OverflowMode, OverflowPossible},
	};

	#[test]
	fn double_intval_size() {
		assert_eq!(size_of::<DoubleIntVal>(), size_of::<IntVal>() * 2);
	}

	#[test]
	fn test_overflow_possible() {
		const { assert!(OverflowPossible::HANDLE_OVERFLOW) };
		assert!(
			<OverflowPossible as OverflowMode>::Accumulator::from(IntVal::MAX)
				.checked_add(1)
				.is_some()
		);
	}

	#[test]
	fn test_overflow_impossible() {
		const { assert!(!OverflowImpossible::HANDLE_OVERFLOW) };
		assert!(
			<OverflowImpossible as OverflowMode>::Accumulator::from(IntVal::MAX)
				.checked_add(1)
				.is_none()
		);
	}
}
