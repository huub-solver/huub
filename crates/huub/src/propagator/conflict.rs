use std::{error::Error, fmt};

use super::reason::{Reason, ReasonBuilder};
use crate::solver::engine::PropRef;

/// Conflict is an error type returned when a variable is assigned two
/// inconsistent values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Conflict {
	/// The reason for the conflict
	/// This reason must result a conjunction that implies false
	pub(crate) reason: Reason,
}

impl Conflict {
	/// Create a new conflict with the given reason
	pub(crate) fn new(reason: &ReasonBuilder, prop: PropRef) -> Self {
		match Reason::build_reason(reason, prop) {
			Ok(reason) => Self { reason },
			Err(true) => panic!("constructing empty conflict"),
			Err(false) => unreachable!("invalid reason"),
		}
	}
}
impl Error for Conflict {}
impl fmt::Display for Conflict {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Conflict detected: nogood {:?}", self.reason)
	}
}
