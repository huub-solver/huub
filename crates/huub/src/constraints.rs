//! Module containing the definitions for propagators and their implementations.

// pub mod bool_array_element;
// pub mod cumulative;
// pub mod disjunctive_strict;
pub mod int_abs;
// pub mod int_all_different;
// pub mod int_array_element;
// pub mod int_array_minimum;
// pub mod int_div;
// pub mod int_in_set;
// pub mod int_linear;
// pub mod int_pow;
// pub mod int_table;
// pub mod int_times;
// pub mod int_value_precede;

use std::{
	error::Error,
	fmt::{self, Debug},
	iter::once,
	marker::PhantomData,
	mem,
};

use dyn_clone::DynClone;
use index_vec::IndexVec;
use pindakaas::Lit as RawLit;
use tracing::warn;

use crate::{
	actions::{DecisionActions, ReasoningEngine, ReformulationActions},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntEvent,
		engine::{Engine, PropRef, State},
		BoolView, BoolViewInner, IntView,
	},
	Conjunction, Model,
};

/// Type alias to represent a user [`Constraint`], stored in a [`Box`], that is
/// used by [`Model`].
pub(crate) type BoxedConstraint = Box<dyn Constraint<Model>>;

/// Type alias to represent [`Propagator`] contained in a [`Box`], that is used
/// by [`Engine`].
pub(crate) type BoxedPropagator = Box<dyn Propagator<Engine>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A `ReasonBuilder` whose result is cached so it can be used multiple times,
/// and is only evaluated once used.
pub(crate) enum CachedReason<B, Atom> {
	/// A evaluated reason that can be reused
	Cached(Vec<Atom>),
	/// A reason that has not yet been evaluated
	Builder(B),
}

/// Conflict is an error type returned when a variable is assigned two
/// inconsistent values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict {
	/// The subject of the conflict (i.e., the literal that couldn't be
	/// propagated).
	///
	/// If `None`, the conflict is a root conflict.
	pub(crate) subject: Option<RawLit>,
	/// The reason for the conflict
	/// This reason must result a conjunction that implies false
	pub(crate) reason: Reason,
}

/// A trait for constraints that can be placed in a [`Model`] object.
///
/// Constraints specified in the library implement this trait, but are using
/// their explicit type in an enumerated type to allow for global model
/// analysis.
pub trait Constraint<E: ReasoningEngine>: Debug + DynClone + Propagator<E> {
	/// Simplify the [`Model`] given the current constraint.
	///
	/// This method is expected to reduce the domains of decision variables,
	/// rewrite the constraint to a simpler form, or detect when the constraint
	/// is already subsumed by the current state of the model.
	fn simplify(
		&mut self,
		context: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(context)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	/// Encode the constraint using [`Propagator`] objects or clauses for a
	/// [`Solver`] object.
	///
	/// This method is should place all required propagators and/or clauses in a
	/// [`Solver`] object to ensure the constraint will not be violated.
	fn to_solver(&self, context: &mut dyn ReformulationActions) -> Result<(), ReformulationError>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A note that the mentioned propagator will compute the `Reason` if requested.
pub struct LazyReason(pub(crate) PropRef, pub(crate) u64);

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
pub trait Propagator<E: ReasoningEngine>: Debug + DynClone + 'static {
	/// Advises the propagator that the solver is backtracking.
	fn advise_of_backtrack(&mut self, context: &mut E::NotificationCtx<'_>) {
		let _ = context;
		unreachable!("propagator did not provide a backtrack advisor implementation")
	}

	/// Advises the propagator that a [`BoolView`] is assigned with the
	/// associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_bool_change(
		&mut self,
		context: &mut E::NotificationCtx<'_>,
		view: BoolView,
		data: u64,
	) -> bool {
		let _ = context;
		let _ = view;
		let _ = data;
		unreachable!("propagator did not provide a Boolean advisor implementation")
	}

	/// Advises the propagator that a [`IntView`] has changed with the
	/// associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_int_change(
		&mut self,
		context: &mut E::NotificationCtx<'_>,
		view: IntView,
		event: IntEvent,
		data: u64,
	) -> bool {
		let _ = context;
		let _ = view;
		let _ = event;
		let _ = data;
		unreachable!("propagator did not provide an integer advisor implementation")
	}

	/// Explain a lazy reason that was emitted.
	///
	/// This method is called by the engine when a conflict is found involving a
	/// lazy explanation emitted by the propagator. The propagator must now
	/// produce the conjunction of literals that led to a literal being
	/// propagated.
	///
	/// The method is called with the data that was passed to the
	/// [`PropagationActions::deferred_reason`] method, and the literal that was
	/// propagated. If the `lit` argument is `None`, then the reason was used to
	/// explain `false`.
	///
	/// The state of the solver is reverted to the state before the propagation
	/// of the `lit` to be explained.
	fn explain(
		&mut self,
		context: &mut E::ExplanationCtx<'_>,
		lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let _ = context;
		let _ = lit;
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}

	/// This method is called when the propagator is posted to the solver to
	/// allow the propagator to subscribe to events.œ
	fn post(&mut self, context: &mut E::PostingCtx<'_>) {
		let _ = context;
	}

	/// The propagate method is called during the search process to allow the
	/// propagator to enforce
	fn propagate(&mut self, context: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let _ = context;
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A conjunction of literals that implies a change in the state
pub enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data.
	Lazy(LazyReason),
	/// A conjunction of literals forming the causation of the change.
	Eager(Box<[RawLit]>),
	/// A single literal that is the causation of the change.
	Simple(RawLit),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Status returned by the [`SimplificationActions::simplify`] method,
/// indicating whether the constraint has been subsumed (such that it can be
/// removed from the [`Model`]) or not.
pub enum SimplificationStatus {
	/// The constraint has been simplified as much as possible, but should be
	/// kept in the [`Model`]. Simplification can be triggered again if any of
	/// the decision variables the constraint depends on change (even by its
	/// own changes).
	NoFixpoint,
	/// The constraint has been simplified to the point where it is subsumed.
	/// The constraint can be removed from the [`Model`].
	Subsumed,
}

impl Clone for BoxedConstraint {
	fn clone(&self) -> BoxedConstraint {
		dyn_clone::clone_box(&**self)
	}
}

impl Clone for BoxedPropagator {
	fn clone(&self) -> BoxedPropagator {
		dyn_clone::clone_box(&**self)
	}
}

impl Conflict {
	/// Create a new conflict with the given reason
	pub(crate) fn new<Context>(
		actions: &mut Context,
		subject: Option<RawLit>,
		reason: impl ReasonBuilder<Context, BoolView>,
	) -> Self {
		match Reason::from_iter(reason.build_reason(actions)) {
			Ok(reason) => Self { subject, reason },
			Err(true) => match subject {
				Some(subject) => Self {
					subject: None,
					reason: Reason::Simple(!subject),
				},
				None => {
					warn!("Empty conflict detected. This suggests additional reasoning might be possible during Model simplification.");
					Self {
						subject: None,
						reason: Reason::Eager(Box::new([])),
					}
				}
			},
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

impl Reason {
	/// Make the reason produce an explanation of the `lit`.
	///
	/// Explanation is in terms of a clause that can be added to the solver.
	/// When the `lit` argument is `None`, the reason is explaining `false`.
	pub(crate) fn explain<Clause: FromIterator<RawLit>>(
		&self,
		props: &mut IndexVec<PropRef, BoxedPropagator>,
		actions: &mut State,
		lit: Option<RawLit>,
	) -> Clause {
		match self {
			Reason::Lazy(LazyReason(prop, data)) => {
				let reason = props[*prop].explain(
					actions,
					lit.map(|lit| BoolView(BoolViewInner::Lit(lit)))
						.unwrap_or(true.into()),
					*data,
				);
				match Reason::collect_vec(reason) {
					Ok(v) => v,
					Err(false) => panic!("invalid lazy reason"), // TODO: Better message,
					Err(true) => Vec::new(),
				}
				.into_iter()
				.map(|l| !l)
				.chain(lit)
				.collect()
			}
			Reason::Eager(v) => v.iter().map(|&l| !l).chain(lit).collect(),
			&Reason::Simple(reason) => once(!reason).chain(lit).collect(),
		}
	}

	pub(crate) fn collect_vec(
		iter: impl IntoIterator<Item = BoolView>,
	) -> Result<Vec<RawLit>, bool> {
		Result::<Vec<_>, _>::from_iter(iter.into_iter().filter_map(|v| match v.0 {
			BoolViewInner::Lit(lit) => Some(Ok(lit)),
			BoolViewInner::Const(false) => Some(Err(false)),
			BoolViewInner::Const(true) => None,
		}))
	}

	/// Collect a conjunction of `BoolView` from an iterator into a `Reason`.
	pub(crate) fn from_iter<I: IntoIterator<Item = BoolView>>(iter: I) -> Result<Self, bool> {
		let lits = Self::collect_vec(iter)?;
		match lits.len() {
			0 => Err(true),
			1 => Ok(Reason::Simple(lits[0])),
			_ => Ok(Reason::Eager(lits.into_boxed_slice())),
		}
	}
}

pub trait ReasonBuilder<Context: ?Sized, Atom> {
	fn build_reason(self, ctx: &mut Context) -> impl IntoIterator<Item = Atom>;
}

impl<C, A, F, I> ReasonBuilder<C, A> for F
where
	F: FnOnce(&mut C) -> I,
	I: IntoIterator<Item = A>,
{
	fn build_reason(self, ctx: &mut C) -> impl IntoIterator<Item = A> {
		self(ctx)
	}
}

impl<C, A> ReasonBuilder<C, A> for Vec<A> {
	fn build_reason(self, _: &mut C) -> impl IntoIterator<Item = A> {
		self
	}
}

impl<C, A, const N: usize> ReasonBuilder<C, A> for [A; N] {
	fn build_reason(self, _: &mut C) -> impl IntoIterator<Item = A> {
		self
	}
}

impl<A, B, C> ReasonBuilder<C, A> for &'_ mut CachedReason<B, A>
where
	A: Clone,
	B: ReasonBuilder<C, A>,
{
	fn build_reason(self, ctx: &mut C) -> impl IntoIterator<Item = A> {
		match self {
			CachedReason::Cached(items) => items.clone(),
			CachedReason::Builder(_) => {
				let CachedReason::Builder(builder) =
					mem::replace(self, CachedReason::Cached(Vec::new()))
				else {
					unreachable!()
				};
				let reason: Vec<A> = builder.build_reason(ctx).into_iter().collect();
				*self = CachedReason::Cached(reason.clone());
				reason
			}
		}
	}
}
