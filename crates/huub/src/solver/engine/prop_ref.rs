//! Propagator reference type used by the propagation engine.

/// Identifies an propagator in a [`crate::solver::Solver`]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PropRef(u32);

impl PropRef {
	/// Invalid propagator reference to be used as a placeholder.
	pub(crate) const INVALID: PropRef = PropRef(i32::MAX as u32);

	/// Recreate the propagator reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the propagator vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new propagator reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index <= i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the propagator reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}
