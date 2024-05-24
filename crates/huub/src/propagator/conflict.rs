use std::{error::Error, fmt};

use pindakaas::Lit as RawLit;

use crate::{
	propagator::reason::{Reason, ReasonBuilder},
	solver::engine::PropRef,
};

/// Conflict is an error type returned when a variable is assigned two
/// inconsistent values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Conflict {
	/// The subject of the conflict (i.e., the literal that couldn't be propagated).
	///
	/// If `None`, the conflict is a root conflict.
	pub(crate) subject: Option<RawLit>,
	/// The reason for the conflict
	/// This reason must result a conjunction that implies false
	pub(crate) reason: Reason,
}

impl Conflict {
	/// Create a new conflict with the given reason
	pub(crate) fn new(subject: Option<RawLit>, reason: &ReasonBuilder, prop: PropRef) -> Self {
		match Reason::build_reason(reason, prop) {
			Ok(reason) => Self { subject, reason },
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
