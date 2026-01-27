//! Module containing the [`Sealed`] private trait that prevents public traits
//! from being implemented outside of this crate.

use crate::helpers::overflow::{OverflowImpossible, OverflowPossible};

/// Helper trait that ensures that a trait cannot be implemented outside of this
/// crate.
pub(crate) trait Sealed {}

impl Sealed for OverflowPossible {}
impl Sealed for OverflowImpossible {}
