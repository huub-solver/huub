use pindakaas::Lit as RawLit;

use crate::{
	solver::{engine::PropRef, view::BoolViewInner},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data
	Lazy(PropRef, u64),
	/// A conjunction of literals forming the causation of the change
	Eager(Box<[RawLit]>),
	Simple(RawLit),
}

impl Reason {
	pub(crate) fn build_reason(builder: &ReasonBuilder, prop: PropRef) -> Result<Self, bool> {
		match builder {
			ReasonBuilder::Lazy(data) => Ok(Self::Lazy(prop, *data)),
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
					Ok(Self::Eager(lits.into_boxed_slice()))
				}
			}
			ReasonBuilder::Simple(view) => match view.0 {
				BoolViewInner::Lit(lit) => Ok(Self::Simple(lit)),
				BoolViewInner::Const(b) => Err(b),
			},
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ReasonBuilder {
	#[allow(dead_code)] // TODOs
	Lazy(u64),
	#[allow(dead_code)] // TODO
	Eager(Conjunction<BoolView>),
	Simple(BoolView),
}
