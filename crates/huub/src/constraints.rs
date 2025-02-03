//! Module containing the definitions for propagators and their implementations.

pub mod bool_array_element;
pub mod disjunctive_strict;
pub mod int_abs;
pub mod int_all_different;
pub mod int_array_element;
pub mod int_array_minimum;
pub mod int_div;
pub mod int_in_set;
pub mod int_linear;
pub mod int_pow;
pub mod int_table;
pub mod int_times;

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
	actions::{
		ConstraintInitActions, ExplanationActions, PropagationActions, ReformulationActions,
		SimplificationActions,
	},
	reformulate::ReformulationError,
	solver::{
		engine::{PropRef, State},
		solving_context::SolvingContext,
		BoolView, BoolViewInner,
	},
	Conjunction, Model,
};

/// Type alias to represent a user [`Constraint`], stored in a [`Box`], that is
/// used by [`Model`].
pub(crate) type BoxedConstraint = Box<dyn Constraint<Model>>;

/// Type alias to represent [`Propagator`] contained in a [`Box`], that is used
/// by [`Engine`].
pub(crate) type BoxedPropagator = Box<dyn for<'a> Propagator<SolvingContext<'a>, State>>;

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
pub struct Conflict {
	/// The subject of the conflict (i.e., the literal that couldn't be propagated).
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
pub trait Constraint<S: SimplificationActions>: Debug + DynConstraintClone {
	/// Method called when a constraint is added to the model, allowing the
	/// constraint to request addtional calls to its [`Constraint::simplify`]
	/// method when decision variables change.
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		let _ = actions;
		// Default implementation does nothing
	}

	/// Simplify the [`Model`] given the current constraint.
	///
	/// This method is expected to reduce the domains of decision variables,
	/// rewrite the constraint to a simpler form, or detect when the constraint is
	/// already subsumed by the current state of the model.
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let _ = actions;
		Ok(SimplificationStatus::Fixpoint)
	}

	/// Encode the constraint using [`Propagator`] objects or clauses for a
	/// [`Solver`] object.
	///
	/// This method is should place all required propagators and/or clauses in a
	/// [`Solver`] object to ensure the constraint will not be violated.
	fn to_solver(&self, actions: &mut dyn ReformulationActions) -> Result<(), ReformulationError>;
}

/// A trait to allow the cloning of user boxed constraint.
///
/// This trait allows us to implement [`Clone`] for [`BoxedConstraint`].
pub trait DynConstraintClone {
	/// Clone the object and store it as a boxed trait object.
	fn clone_dyn_constraint(&self) -> BoxedConstraint;
}

/// A trait to allow the cloning of boxed propagators.
///
/// This trait allows us to implement [`Clone`] for [`BoxedPropagator`].
pub trait DynPropagatorClone {
	/// Clone the object and store it as a boxed trait object.
	fn clone_dyn_propagator(&self) -> BoxedPropagator;
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
pub trait Propagator<P, E>: Debug + DynPropagatorClone
where
	P: PropagationActions,
	E: ExplanationActions,
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
pub enum Reason {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data.
	Lazy(LazyReason),
	/// A conjunction of literals forming the causation of the change.
	Eager(Box<[RawLit]>),
	/// A single literal that is the causation of the change.
	Simple(RawLit),
}

/// A trait for types that can be used to construct a `Reason`
pub trait ReasonBuilder<A: ExplanationActions + ?Sized> {
	/// Construct a `Reason`, or return a Boolean indicating that the reason is
	/// trivial.
	fn build_reason(self, actions: &mut A) -> Result<Reason, bool>;
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Status returned by the [`SimplificationActions::simplify`] method,
/// indicating whether the constraint has been subsumed (such that it can be
/// removed from the [`Model`]) or not.
pub enum SimplificationStatus {
	/// The constraint has been simplified as much as possible, but should be kept
	/// in the [`Model`].
	///
	/// Simplification can be triggered again if any of the decision variables the
	/// constraint depends on change.
	Fixpoint,
	/// The constraint has been simplified to the point where it is subsumed. The
	/// constraint can be removed from the [`Model`].
	Subsumed,
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

impl Clone for BoxedConstraint {
	fn clone(&self) -> BoxedConstraint {
		self.clone_dyn_constraint()
	}
}

impl Clone for BoxedPropagator {
	fn clone(&self) -> BoxedPropagator {
		self.clone_dyn_propagator()
	}
}

impl<C: Constraint<Model> + Clone + 'static> DynConstraintClone for C {
	fn clone_dyn_constraint(&self) -> BoxedConstraint {
		Box::new(self.clone())
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
		Ok(Reason::Lazy(self))
	}
}

impl<P: for<'a> Propagator<SolvingContext<'a>, State> + Clone + 'static> DynPropagatorClone for P {
	fn clone_dyn_propagator(&self) -> BoxedPropagator {
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
			Reason::Lazy(LazyReason(prop, data)) => {
				let reason = props[*prop].explain(actions, lit, *data);
				reason.into_iter().map(|l| !l).chain(lit).collect()
			}
			Reason::Eager(v) => v.iter().map(|&l| !l).chain(lit).collect(),
			&Reason::Simple(reason) => once(!reason).chain(lit).collect(),
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
