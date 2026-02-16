//! Module containing generic views for decision variables.
//!
//! Depending on the actions implemented by the decision variables, views on the
//! generic variable will automatically implement the appropriate action traits
//! for all [`ReasoningEngine`](crate::actions::ReasoningEngine)s that support
//! them.

mod linear_bool_view;
mod linear_view;
mod offset_view;

pub use linear_bool_view::LinearBoolView;
pub use linear_view::LinearView;
pub use offset_view::OffsetView;
