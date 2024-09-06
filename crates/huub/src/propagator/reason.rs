use std::{iter::once, marker::PhantomData, mem};

use index_vec::IndexVec;
use pindakaas::Lit as RawLit;

use crate::{
	actions::explanation::ExplanationActions,
	solver::{
		engine::{PropRef, State},
		poster::BoxedPropagator,
		view::BoolViewInner,
	},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A `ReasonBuilder` whose result is cached so it can be used multiple times
pub(crate) enum CachedReason<A: ExplanationActions, R: ReasonBuilder<A>> {
	/// A evaluated reason that can be reused
	Cached(Result<Reason, bool>),
	/// A reason that has not yet been evaluated
	Builder((R, PhantomData<A>)),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LazyReason(pub(crate) PropRef, pub(crate) u64);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A conjunction of literals that implies a change in the state
pub(crate) enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data
	Lazy(PropRef, u64),
	/// A conjunction of literals forming the causation of the change
	Eager(Box<[RawLit]>),
	Simple(RawLit),
}

/// A trait for types that can be used to construct a `Reason`
pub(crate) trait ReasonBuilder<A: ExplanationActions + ?Sized> {
	/// Construct a `Reason`, or return a Boolean indicating that the reason is trivial
	fn build_reason(self, actions: &mut A) -> Result<Reason, bool>;
}

impl<A: ExplanationActions, R: ReasonBuilder<A>> CachedReason<A, R> {
	pub(crate) fn new(builder: R) -> Self {
		CachedReason::Builder((builder, PhantomData))
	}
}

impl Reason {
	pub(crate) fn to_clause<Clause: FromIterator<RawLit>>(
		&self,
		props: &mut IndexVec<PropRef, BoxedPropagator>,
		actions: &mut State,
	) -> Clause {
		match self {
			Reason::Lazy(prop, data) => {
				let reason = props[*prop].explain(actions, *data);
				reason.iter().map(|l| !l).collect()
			}
			Reason::Eager(v) => v.iter().map(|l| !l).collect(),
			Reason::Simple(l) => once(!l).collect(),
		}
	}

	pub(crate) fn from_iter<I: IntoIterator<Item = BoolView>>(iter: I) -> Result<Self, bool> {
		let lits = Result::<Vec<_>, _>::from_iter(iter.into_iter().filter_map(|v| match v.0 {
			BoolViewInner::Lit(lit) => Some(Ok(lit)),
			BoolViewInner::Const(false) => Some(Err(false)),
			BoolViewInner::Const(true) => None,
		}))?;
		match lits.len() {
			0 => Err(true),
			1 => Ok(Reason::Simple(lits[0])),
			_ => Ok(Reason::Eager(lits.into_boxed_slice())),
		}
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for BoolView {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		match self.0 {
			BoolViewInner::Lit(lit) => Ok(Reason::Simple(lit)),
			BoolViewInner::Const(b) => Err(b),
		}
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for &[BoolView] {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		Reason::from_iter(self.iter().cloned())
	}
}

impl<A: ExplanationActions, R: ReasonBuilder<A>> ReasonBuilder<A> for &mut CachedReason<A, R> {
	fn build_reason(self, actions: &mut A) -> Result<Reason, bool> {
		match self {
			CachedReason::Cached(reason) => reason.clone(),
			CachedReason::Builder(_) => {
				let tmp = mem::replace(self, CachedReason::Cached(Err(false)));
				let CachedReason::Builder((builder, _)) = tmp else {
					unreachable!()
				};
				let reason = builder.build_reason(actions);
				*self = CachedReason::Cached(reason.clone());
				reason
			}
		}
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for Conjunction<BoolView> {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		Reason::from_iter(self)
	}
}

impl<A, F, I> ReasonBuilder<A> for F
where
	A: ExplanationActions,
	F: FnOnce(&mut A) -> I,
	I: IntoIterator<Item = BoolView>,
{
	fn build_reason(self, a: &mut A) -> Result<Reason, bool> {
		Reason::from_iter(self(a))
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for LazyReason {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		Ok(Reason::Lazy(self.0, self.1))
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for Reason {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		Ok(self)
	}
}

impl<A: ExplanationActions> ReasonBuilder<A> for Result<Reason, bool> {
	fn build_reason(self, _: &mut A) -> Result<Reason, bool> {
		self
	}
}
