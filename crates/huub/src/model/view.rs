//! Standard [`Model`] decision variable views.

pub(crate) mod boolean;
pub(crate) mod integer;

/// Trait implemented by types that provide a default model view.
pub trait DefaultView: private::Sealed + 'static {
	/// The view type associated with this default view.
	type View;
}

/// A typed view over a decision variable or constant in the model.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct View<T: DefaultView>(pub(crate) T::View);

/// Sealing helpers for model view traits.
mod private {
	/// Helper trait that ensures that the [`DefaultView`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
}
