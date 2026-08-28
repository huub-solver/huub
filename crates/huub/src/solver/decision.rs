//! Decision variable types and helpers for [`Solver`].

pub(crate) mod boolean;
pub(crate) mod integer;

use crate::DeepClone;

/// A typed handle to a decision variable in the solver.
#[derive(Clone, Copy, Debug, DeepClone, Eq, Hash, PartialEq)]
#[deepclone(bound = "T: DecisionReference, T::Ref: Clone")]
pub struct Decision<T: DecisionReference>(#[deepclone(clone)] pub(crate) T::Ref);

/// Marker trait for types that can be used as solver decision references.
pub trait DecisionReference: private::Sealed + 'static {
	/// The underlying reference type stored in [`Decision`].
	type Ref;
}

/// Sealing helpers for solver decision reference traits.
mod private {
	/// Helper trait that ensures that the [`DecisionStorage`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
}
