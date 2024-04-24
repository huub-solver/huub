use std::{error::Error, fmt};

/// Conflict is an error type returned when a variable is assigned two
/// inconsistent values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub(crate) struct Conflict;
impl Error for Conflict {}
impl fmt::Display for Conflict {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Conflict detected: unsatisfiable assignment")
	}
}
