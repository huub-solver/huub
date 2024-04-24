use pindakaas::Lit;

use crate::{
	solver::{engine::PropRef, view::BoolViewInner},
	BoolView,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data
	Lazy(PropRef, u64),
	/// A conjunction of literals forming the causation of the change
	Eager(Box<[Lit]>),
	Simple(Lit),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReasonBuilder {
	Lazy(PropRef, u64),
	#[allow(dead_code)] // TODO
	Eager(Vec<BoolView>),
	Simple(BoolView),
}

impl TryFrom<ReasonBuilder> for Reason {
	type Error = bool;

	fn try_from(value: ReasonBuilder) -> Result<Self, Self::Error> {
		match value {
			ReasonBuilder::Lazy(prop, data) => Ok(Reason::Lazy(prop, data)),
			ReasonBuilder::Eager(views) => {
				let mut lits = Vec::with_capacity(views.len());
				for view in views {
					match view.0 {
						BoolViewInner::Lit(lit) => lits.push(lit),
						BoolViewInner::Const(b) => {
							if !b {
								return Err(false);
							}
						}
					}
				}
				if lits.is_empty() {
					Err(true)
				} else {
					Ok(Reason::Eager(lits.into_boxed_slice()))
				}
			}
			ReasonBuilder::Simple(view) => match view.0 {
				BoolViewInner::Lit(lit) => Ok(Reason::Simple(lit)),
				BoolViewInner::Const(b) => Err(b),
			},
		}
	}
}
