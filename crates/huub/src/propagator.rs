//! Module containing the definitions for propagators and their implementations.

pub(crate) mod all_different_int;
pub(crate) mod array_int_minimum;
pub(crate) mod array_var_int_element;
pub(crate) mod disjunctive_strict;
pub(crate) mod int_abs;
pub(crate) mod int_div;
pub(crate) mod int_lin_le;
pub(crate) mod int_lin_ne;
pub(crate) mod int_pow;
pub(crate) mod int_times;
pub(crate) mod table_int;
pub(crate) mod all_different_bounds;

use std::{
	error::Error,
	fmt::{self, Debug},
	iter::once,
	marker::PhantomData,
	mem,
};

use index_vec::IndexVec;
use pindakaas::Lit as RawLit;

use crate::{
	actions::{ExplanationActions, PropagationActions},
	solver::{
		engine::{solving_context::SolvingContext, PropRef, State},
		poster::BoxedPropagator,
		view::BoolViewInner,
	},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A `ReasonBuilder` whose result is cached so it can be used multiple times,
/// and is only evaluated once used.
pub(crate) enum CachedReason<A: ExplanationActions, R: ReasonBuilder<A>> {
	/// A evaluated reason that can be reused
	Cached(Result<Reason, bool>),
	/// A reason that has not yet been evaluated
	Builder((R, PhantomData<A>)),
}

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

/// A trait to allow the cloning of boxed propagators.
///
/// This trait allows us to implement [`Clone`] for [`BoxedPropagator`].
pub(crate) trait DynPropClone {
	/// Clone the object and store it as a boxed trait object.
	fn clone_dyn_prop(&self) -> BoxedPropagator;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A note that the mentioned propagator will compute the `Reason` if requested.
pub(crate) struct LazyReason(pub(crate) PropRef, pub(crate) u64);

/// A trait for a propagator that is called during the search process to filter
/// the domains of decision variables, and detect inconsistencies.
///
/// Implementations of the propagator trait must be able to explain changes to
/// domains of decision variables as a conjunction of literals that imply the
/// change. If these explanations are too expensive to compute during
/// propagation, then the propagator can delay giving the explanation using
/// [`PropagationActions::deferred_reason`]. If the explanation is needed, then
/// the propagation engine will revert the state of the solver and call
/// [`Propagator::explain`] to receive the explanation.
pub(crate) trait Propagator<P: PropagationActions, E: ExplanationActions>:
	Debug + DynPropClone
{
	/// The propagate method is called during the search process to allow the
	/// propagator to enforce
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let _ = actions;
		Ok(())
	}

	/// Explain a lazy reason that was emitted.
	///
	/// This method is called by the engine when a conflict is found involving a
	/// lazy explaination emitted by the propagator. The propagator must now
	/// produce the conjunction of literals that led to a literal being
	/// propagated.
	///
	/// The method is called with the data that was passed to the
	/// [`PropagationActions::deferred_reason`] method, and the literal that was
	/// propagated. If the `lit` argument is `None`, then the reason was used to
	/// explain `false`.
	///
	/// The state of the solver is reverted to the state before the propagation of
	/// the `lit` to be explained.
	fn explain(&mut self, actions: &mut E, lit: Option<RawLit>, data: u64) -> Conjunction {
		let _ = actions;
		let _ = lit;
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A conjunction of literals that implies a change in the state
pub(crate) enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data.
	Lazy(PropRef, u64),
	/// A conjunction of literals forming the causation of the change.
	Eager(Box<[RawLit]>),
	/// A single literal that is the causation of the change.
	Simple(RawLit),
}

/// A trait for types that can be used to construct a `Reason`
pub(crate) trait ReasonBuilder<A: ExplanationActions + ?Sized> {
	/// Construct a `Reason`, or return a Boolean indicating that the reason is
	/// trivial.
	fn build_reason(self, actions: &mut A) -> Result<Reason, bool>;
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

impl Clone for BoxedPropagator {
	fn clone(&self) -> BoxedPropagator {
		self.clone_dyn_prop()
	}
}

impl<A: ExplanationActions, R: ReasonBuilder<A>> CachedReason<A, R> {
	/// Create a new [`CachedReason`] from a [`ReasonBuilder`].
	pub(crate) fn new(builder: R) -> Self {
		CachedReason::Builder((builder, PhantomData))
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

impl Conflict {
	/// Create a new conflict with the given reason
	pub(crate) fn new<A: ExplanationActions>(
		actions: &mut A,
		subject: Option<RawLit>,
		reason: impl ReasonBuilder<A>,
	) -> Self {
		match reason.build_reason(actions) {
			Ok(reason) => Self { subject, reason },
			Err(true) => {
				if let Some(subject) = subject {
					Self {
						subject: None,
						reason: Reason::Simple(!subject),
					}
				} else {
					panic!("constructing empty conflict")
				}
			}
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

impl<P: for<'a> Propagator<SolvingContext<'a>, State> + Clone + 'static> DynPropClone for P {
	fn clone_dyn_prop(&self) -> BoxedPropagator {
		Box::new(self.clone())
	}
}

impl Reason {
	/// Make the reason produce an explanation of the `lit`.
	///
	/// Expalanation is in terms of a clause that can be added to the solver.
	/// When the `lit` argument is `None`, the reason is explaining `false`.
	pub(crate) fn explain<Clause: FromIterator<RawLit>>(
		&self,
		props: &mut IndexVec<PropRef, BoxedPropagator>,
		actions: &mut State,
		lit: Option<RawLit>,
	) -> Clause {
		match self {
			Reason::Lazy(prop, data) => {
				let reason = props[*prop].explain(actions, lit, *data);
				reason.into_iter().map(|l| !l).chain(lit).collect()
			}
			Reason::Eager(v) => v.iter().map(|l| !l).chain(lit).collect(),
			Reason::Simple(reason) => once(!reason).chain(lit).collect(),
		}
	}

	/// Collect a conjunction of `BoolView` from an iterator into a `Reason`.
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
