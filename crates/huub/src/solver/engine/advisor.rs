//! Advisor types used by the propagation engine.

use crate::solver::engine::PropRef;

/// Identifies an advisor in the [`super::State`]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AdvRef(u32);

/// Definition of an advisor giving the information about the
/// [`crate::solver::view::View`] subscribed to and the way in which to advise
/// the propagator.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AdvisorDef {
	/// Whether the advice is on a [`crate::solver::view::boolean::BoolView`]
	/// being used as an integer view.
	pub(crate) bool2int: bool,
	/// 64 bits of data communicated when advising propagator.
	pub(crate) data: u64,
	/// Whether the advice is on an integer view with a negative coefficient.
	pub(crate) negated: bool,
	/// The propagator being advised.
	pub(crate) propagator: PropRef,
}

impl AdvRef {
	/// Recreate the advisor reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the advisor vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new advisor reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index <= i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the advisor reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}
