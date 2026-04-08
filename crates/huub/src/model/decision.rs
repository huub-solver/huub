//! Decision variable types and helpers for [`Model`].

pub(crate) mod boolean;
pub(crate) mod integer;

/// A typed handle to a decision variable in a model.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Decision<T: DecisionReference>(pub(crate) T::Ref);

/// Marker trait for types that can be used as model decision references.
pub trait DecisionReference: private::Sealed + 'static {
	/// The underlying reference type stored in [`Decision`].
	type Ref;
}

/// Sealing helpers for model decision reference traits.
mod private {
	/// Helper trait that ensures that the [`DecisionStorage`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
}
