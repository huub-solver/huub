//! Module that contains helpers for handling overflow in arithmetic operations.

use std::{
	fmt,
	iter::Sum,
	ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

use crate::IntVal;

/// Type alias for a integer value that has double the bit width of [`IntVal`].
pub(crate) type DoubleIntVal = i128;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
/// Marker type indicating that overflow is impossible, and does not need to be
/// handled by the [`Propagator`](crate::constraints::Propagator).
pub struct OverflowImpossible;

/// Helper trait that defines the capabilities of [`OverflowPossible`] and
/// [`OverflowImpossible`] that can be used in
/// [`Propagator`](crate::constraints::Propagator) implementations.
pub trait OverflowMode: private::Sealed + Clone + fmt::Debug + 'static {
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
/// handled by the [`Propagator`](crate::constraints::Propagator).
pub struct OverflowPossible;

impl OverflowMode for OverflowImpossible {
	const HANDLE_OVERFLOW: bool = false;

	type Accumulator = IntVal;
}

impl private::Sealed for OverflowImpossible {}

impl OverflowMode for OverflowPossible {
	const HANDLE_OVERFLOW: bool = true;

	type Accumulator = DoubleIntVal;
}

impl private::Sealed for OverflowPossible {}

/// Sealing helpers for `OverflowMode`.
mod private {
	/// Helper trait that ensures that the [`OverflowMode`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
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
	fn test_overflow_impossible() {
		const { assert!(!OverflowImpossible::HANDLE_OVERFLOW) };
		assert!(
			<OverflowImpossible as OverflowMode>::Accumulator::from(IntVal::MAX)
				.checked_add(1)
				.is_none()
		);
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
}
