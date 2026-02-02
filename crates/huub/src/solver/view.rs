//! Standard [`Solver`] decision variable views.

pub(crate) mod boolean;
pub(crate) mod integer;

/// Trait implemented by types that provide a default solver view.
pub trait DefaultView: private::Sealed + 'static {
	/// The view type associated with this default view.
	type View;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A typed view over a decision variable or constant in the solver.
pub struct View<T: DefaultView>(pub(crate) T::View);

/// Sealing helpers for solver view traits.
mod private {
	/// Helper trait that ensures that the [`DefaultView`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
}
