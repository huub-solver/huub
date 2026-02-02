//! Module containing the definitions for propagators and their implementations.

pub mod bool_array_element;
pub mod cumulative;
pub mod disjunctive;
pub mod int_abs;
pub mod int_array_element;
pub mod int_array_minimum;
pub mod int_div;
pub mod int_linear;
pub mod int_mul;
pub mod int_no_overlap;
pub mod int_pow;
pub mod int_set_contains;
pub mod int_table;
pub mod int_unique;
pub mod int_value_precede;

use std::{
	any::Any,
	error::Error,
	fmt::{self, Debug},
	iter::once,
	mem,
};

use dyn_clone::DynClone;
use itertools::Itertools;
use pindakaas::Lit as RawLit;
use tracing::warn;

use crate::{
	Conjunction, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions,
		IntExplanationActions, IntInitActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions, ReasoningContext, ReasoningEngine,
	},
	lower::{LoweringContext, LoweringError},
	model::{self, Model},
	solver::{
		self,
		activation_list::IntEvent,
		engine::{Engine, State},
		view::boolean::BoolView,
	},
};

/// Helper trait to simplify trait bounds for [`Constraint`] implementations.
pub trait BoolModelActions<E>
where
	E: ReasoningEngine,
	Self: BoolSolverActions<E>
		+ for<'a> BoolSimplificationActions<E::PropagationCtx<'a>>
		+ Into<model::View<bool>>,
{
}

/// Helper trait to simplify trait bounds for [`Propagator`] implementations.
pub trait BoolSolverActions<E>
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> BoolInitActions<E::InitializationCtx<'a>>
		+ for<'a> BoolInspectionActions<E::ExplanationCtx<'a>>
		+ for<'a> BoolInspectionActions<E::NotificationCtx<'a>>
		+ for<'a> BoolPropagationActions<E::PropagationCtx<'a>>
		+ Into<E::Atom>,
{
}

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
	Cached(Result<Reason<Atom>, bool>),
	/// A reason that has not yet been evaluated
	Builder(B),
}

/// Conflict is an error type returned when a variable is assigned two
/// inconsistent values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict<Atom> {
	/// The subject of the conflict (i.e., the literal that couldn't be
	/// propagated).
	///
	/// If `None`, the conflict is a root conflict.
	pub(crate) subject: Option<Atom>,
	/// The reason for the conflict
	/// This reason must result a conjunction that implies false
	pub(crate) reason: Reason<Atom>,
}

/// A trait for constraints that can be placed in a [`Model`] object.
///
/// Constraints specified in the library implement this trait, but are using
/// their explicit type in an enumerated type to allow for global model
/// analysis.
pub trait Constraint<E: ReasoningEngine + ?Sized>: Any + Debug + DynClone + Propagator<E> {
	/// Simplify the [`Model`] given the current constraint.
	///
	/// This method is expected to reduce the domains of decision variables,
	/// rewrite the constraint to a simpler form, or detect when the constraint
	/// is already subsumed by the current state of the model.
	fn simplify(
		&mut self,
		context: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict>;

	/// Encode the constraint using [`Propagator`] objects or clauses for a
	/// [`Solver`](solver::Solver) object.
	///
	/// This method is should place all required propagators and/or clauses in a
	/// [`Solver`](solver::Solver) object to ensure the constraint will not be
	/// violated.
	fn to_solver(&self, context: &mut LoweringContext<'_>) -> Result<(), LoweringError>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A note that the mentioned propagator will compute the `Reason` if requested.
pub struct DeferredReason {
	/// Reference to the propagator that will compute the reason.
	pub(crate) propagator: u32,
	/// Data to be given to the propagator to compute the reason.
	pub(crate) data: u64,
}

/// Helper trait to simplify trait bounds for [`Constraint`] implementations.
pub trait IntModelActions<E>
where
	E: ReasoningEngine,
	Self: IntSolverActions<E>
		+ for<'a> IntSimplificationActions<E::PropagationCtx<'a>>
		+ Into<model::View<IntVal>>,
{
}

/// Helper trait to simplify trait bounds for [`Propagator`] implementations.
pub trait IntSolverActions<E>
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> IntInitActions<E::InitializationCtx<'a>>
		+ for<'a> IntExplanationActions<E::ExplanationCtx<'a>>
		+ for<'a> IntInspectionActions<E::NotificationCtx<'a>>
		+ for<'a> IntPropagationActions<E::PropagationCtx<'a>>,
{
}

/// A trait for a propagator that is called during the search process to filter
/// the domains of decision variables, and detect inconsistencies.
///
/// Implementations of the propagator trait must be able to explain changes to
/// domains of decision variables as a conjunction of literals that imply the
/// change. If these explanations are too expensive to compute during
/// propagation, then the propagator can delay giving the explanation using
/// [`PropagationActions::deferred_reason`](crate::actions::PropagationActions::deferred_reason).
/// If the explanation is needed, then the propagation engine will revert the
/// state of the solver and call [`Propagator::explain`] to receive the
/// explanation.
pub trait Propagator<E: ReasoningEngine + ?Sized>: Debug + DynClone + 'static {
	/// Advises the propagator that the solver is backtracking.
	fn advise_of_backtrack(&mut self, context: &mut E::NotificationCtx<'_>) {
		let _ = context;
		unreachable!("propagator did not provide a backtrack advisor implementation")
	}

	/// Advises the propagator that a Boolean decision (view) is assigned with
	/// the associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_bool_change(&mut self, context: &mut E::NotificationCtx<'_>, data: u64) -> bool {
		let _ = context;
		let _ = data;
		unreachable!("propagator did not provide a Boolean advisor implementation")
	}

	/// Advises the propagator that a integer decision (view) has changed with
	/// the associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_int_change(
		&mut self,
		context: &mut E::NotificationCtx<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		let _ = context;
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
	/// [`PropagationActions::deferred_reason`](crate::actions::PropagationActions::deferred_reason)
	/// method, and the literal that was propagated. If the `lit` argument is
	/// `None`, then the reason was used to explain `false`.
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
	fn initialize(&mut self, context: &mut E::InitializationCtx<'_>);

	/// The propagate method is called during the search process to allow the
	/// propagator to enforce
	fn propagate(&mut self, context: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A conjunction of literals that implies a change in the state
pub enum Reason<Atom> {
	/// A promise that a given propagator will compute a causation of the change
	/// when given the attached data.
	Lazy(DeferredReason),
	/// A conjunction of literals forming the causation of the change.
	Eager(Box<[Atom]>),
	/// A single literal that is the causation of the change.
	Simple(Atom),
}

/// A trait for types that can be used to construct a reason for the propagation
/// in the `Context` from `Atom`s.
pub trait ReasonBuilder<Context: ReasoningContext + ?Sized> {
	/// Construct a `Reason`, or return a Boolean indicating that the reason is
	/// trivial.
	fn build_reason(self, ctx: &mut Context) -> Result<Reason<Context::Atom>, bool>;
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Status returned by the [`Constraint::simplify`] method,
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

impl<E, B> BoolModelActions<E> for B
where
	E: ReasoningEngine,
	B: BoolSolverActions<E>
		+ for<'a> BoolSimplificationActions<E::PropagationCtx<'a>>
		+ Into<model::View<bool>>,
{
}

impl<E, B> BoolSolverActions<E> for B
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> BoolInitActions<E::InitializationCtx<'a>>
		+ for<'a> BoolInspectionActions<E::ExplanationCtx<'a>>
		+ for<'a> BoolInspectionActions<E::NotificationCtx<'a>>
		+ for<'a> BoolPropagationActions<E::PropagationCtx<'a>>
		+ Into<E::Atom>,
{
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

impl<C> ReasonBuilder<C> for &[C::Atom]
where
	C: ReasoningContext + ?Sized,
{
	fn build_reason(self, _: &mut C) -> Result<Reason<C::Atom>, bool> {
		Reason::from_iter(self.iter().cloned())
	}
}

impl<C, const N: usize> ReasonBuilder<C> for &[C::Atom; N]
where
	C: ReasoningContext + ?Sized,
{
	fn build_reason(self, ctx: &mut C) -> Result<Reason<C::Atom>, bool> {
		self[..].build_reason(ctx)
	}
}

impl<C, const N: usize> ReasonBuilder<C> for [C::Atom; N]
where
	C: ReasoningContext + ?Sized,
{
	fn build_reason(self, _: &mut C) -> Result<Reason<C::Atom>, bool> {
		Reason::from_iter(self)
	}
}

impl<A, B> CachedReason<B, A> {
	/// Create a new [`CachedReason`] from a [`ReasonBuilder`].
	pub(crate) fn new(builder: B) -> Self {
		CachedReason::Builder(builder)
	}
}

impl<B, C> ReasonBuilder<C> for &'_ mut CachedReason<B, C::Atom>
where
	C: ReasoningContext + ?Sized,
	B: ReasonBuilder<C>,
{
	fn build_reason(self, ctx: &mut C) -> Result<Reason<C::Atom>, bool> {
		match self {
			CachedReason::Cached(items) => items.clone(),
			CachedReason::Builder(_) => {
				let CachedReason::Builder(builder) =
					mem::replace(self, CachedReason::Cached(Err(false)))
				else {
					unreachable!()
				};
				let reason = builder.build_reason(ctx);
				*self = CachedReason::Cached(reason.clone());
				reason
			}
		}
	}
}

impl Conflict<solver::Decision<bool>> {
	/// Create a new conflict with the given reason
	pub(crate) fn new<Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized>(
		ctx: &mut Ctx,
		subject: Option<solver::Decision<bool>>,
		reason: impl ReasonBuilder<Ctx>,
	) -> Self {
		match Reason::from_view(reason.build_reason(ctx)) {
			Ok(reason) => Self { subject, reason },
			Err(true) => match subject {
				Some(subject) => Self {
					subject: None,
					reason: Reason::Simple(!subject),
				},
				None => {
					warn!(
						"Empty conflict detected. This suggests additional reasoning might be possible during Model simplification."
					);
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

impl<Atom: Debug> Error for Conflict<Atom> {}

impl<Atom: Debug> fmt::Display for Conflict<Atom> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Conflict detected: nogood {:?}", self.reason)
	}
}

impl<C> ReasonBuilder<C> for DeferredReason
where
	C: ReasoningContext + ?Sized,
{
	fn build_reason(self, _: &mut C) -> Result<Reason<C::Atom>, bool> {
		Ok(Reason::Lazy(self))
	}
}

impl<C, F, I> ReasonBuilder<C> for F
where
	C: ReasoningContext + ?Sized,
	F: FnOnce(&mut C) -> I,
	I: IntoIterator<Item = C::Atom>,
{
	fn build_reason(self, ctx: &mut C) -> Result<Reason<C::Atom>, bool> {
		Reason::from_iter(self(ctx))
	}
}

impl<E, I> IntModelActions<E> for I
where
	E: ReasoningEngine,
	I: IntSolverActions<E>
		+ for<'a> IntSimplificationActions<E::PropagationCtx<'a>>
		+ Into<model::View<IntVal>>,
{
}

impl<E, I> IntSolverActions<E> for I
where
	E: ReasoningEngine + ?Sized,
	I: for<'a> IntInitActions<E::InitializationCtx<'a>>
		+ for<'a> IntExplanationActions<E::ExplanationCtx<'a>>
		+ for<'a> IntInspectionActions<E::NotificationCtx<'a>>
		+ for<'a> IntPropagationActions<E::PropagationCtx<'a>>,
{
}

impl<A> Reason<A> {
	/// Collect a conjunction of `BoolView` from an iterator into a `Reason`.
	pub(crate) fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Result<Self, bool> {
		let mut lits: Vec<_> = iter.into_iter().collect();
		match lits.len() {
			0 => Err(true),
			1 => Ok(Reason::Simple(lits.remove(0))),
			_ => Ok(Reason::Eager(lits.into_boxed_slice())),
		}
	}
}

impl Reason<solver::Decision<bool>> {
	/// Make the reason produce an explanation of the `lit`.
	///
	/// Explanation is in terms of a clause that can be added to the solver.
	/// When the `lit` argument is `None`, the reason is explaining `false`.
	pub(crate) fn explain<Clause: FromIterator<RawLit>>(
		&self,
		props: &mut [BoxedPropagator],
		actions: &mut State,
		lit: Option<solver::Decision<bool>>,
	) -> Clause {
		match self {
			&Reason::Lazy(DeferredReason {
				propagator: prop,
				data,
			}) => {
				let reason = props[prop as usize].explain(
					actions,
					lit.map(|lit| lit.into()).unwrap_or(true.into()),
					data,
				);
				let v: Result<Vec<_>, _> = reason
					.into_iter()
					.filter_map(|v| match v.0 {
						BoolView::Lit(lit) => Some(Ok(lit)),
						BoolView::Const(false) => Some(Err(false)),
						BoolView::Const(true) => None,
					})
					.collect();
				match v {
					Ok(v) => v,
					Err(false) => panic!("invalid lazy reason"), // TODO: Better message,
					Err(true) => Vec::new(),
				}
				.into_iter()
				.map(|l| !l.0)
				.chain(lit.map(|lit| lit.0))
				.collect()
			}
			Reason::Eager(v) => v
				.iter()
				.map(|&l| !l.0)
				.chain(lit.map(|lit| lit.0))
				.collect(),
			&Reason::Simple(reason) => once(!reason.0).chain(lit.map(|lit| lit.0)).collect(),
		}
	}

	/// Internal function used to tighten a [`Reason`] with [`BoolView`] atoms
	/// to a [`Reason`] with [`RawLit`] atoms.
	pub(crate) fn from_view(
		reason: Result<Reason<solver::View<bool>>, bool>,
	) -> Result<Self, bool> {
		let v = match reason? {
			Reason::Lazy(lazy) => return Ok(Self::Lazy(lazy)),
			Reason::Eager(items) => items.into_vec(),
			Reason::Simple(lit) => vec![lit],
		};
		let mut v: Vec<_> = v
			.into_iter()
			.filter_map(|v| match v.0 {
				BoolView::Lit(lit) => Some(Ok(lit)),
				BoolView::Const(false) => Some(Err(false)),
				BoolView::Const(true) => None,
			})
			.try_collect()?;
		match v.len() {
			0 => Err(true),
			1 => Ok(Reason::Simple(v.remove(0))),
			_ => Ok(Reason::Eager(v.into_boxed_slice())),
		}
	}
}

impl<C> ReasonBuilder<C> for Vec<C::Atom>
where
	C: ReasoningContext + ?Sized,
{
	fn build_reason(self, _: &mut C) -> Result<Reason<C::Atom>, bool> {
		Reason::from_iter(self)
	}
}
