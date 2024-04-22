use pindakaas::Lit;

use crate::solver::engine::PropRef;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data
	Lazy(PropRef, u64),
	#[allow(dead_code)] // TODO
	/// A conjunction of literals forming the causation of the change
	Eager(Box<[Lit]>),
	Simple(Lit),
}
