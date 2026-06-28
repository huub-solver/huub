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
	slice,
};

use dyn_clone::DynClone;
use pindakaas::solver::propagation::ClauseBuilder;

use crate::{
	IntVal,
	actions::{
		BoolAnalyzeActions, BoolInitActions, BoolInspectionActions, BoolPropagationActions,
		BoolSimplificationActions, IntAnalyzeActions, IntEvent, IntExplanationActions,
		IntInitActions, IntInspectionActions, IntPropagationActions, IntSimplificationActions,
		PropagationContext, ReasoningEngine,
	},
	lower::{LoweringContext, LoweringError},
	model::{self, Model},
	solver::{
		self,
		engine::{Engine, EngineReasonSink, State},
		view::boolean::BoolView,
	},
};

/// Helper trait to simplify trait bounds for [`Constraint`] implementations.
pub trait BoolModelActions<E>
where
	E: ReasoningEngine,
	Self: BoolSolverActions<E>
		+ for<'a> BoolAnalyzeActions<E::InitializationContext<'a>>
		+ for<'a> BoolSimplificationActions<E::PropagationContext<'a>>
		+ Into<model::View<bool>>,
{
}

/// Helper trait to simplify trait bounds for [`Propagator`] implementations.
pub trait BoolSolverActions<E>
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> BoolInitActions<E::InitializationContext<'a>>
		+ for<'a> BoolInspectionActions<E::ExplanationContext<'a>>
		+ for<'a> BoolInspectionActions<E::NotificationContext<'a>>
		+ for<'a> BoolPropagationActions<E::PropagationContext<'a>>
		+ Into<E::Atom>,
{
}

/// Type alias to represent a user [`Constraint`], stored in a [`Box`], that is
/// used by [`Model`].
pub(crate) type BoxedConstraint = Box<dyn Constraint<Model>>;

/// Type alias to represent [`Propagator`] contained in a [`Box`], that is used
/// by [`Engine`].
pub(crate) type BoxedPropagator = Box<dyn Propagator<Engine>>;

/// A conflict raised during propagation: the nogood clause the current state
/// falsifies, possibly still deferred to a propagator.
///
/// This is the propagation-internal conflict type. It appears in the
/// propagation API as `E::Conflict`, but it is **opaque to the user**: its only
/// field is private, so it cannot be constructed or inspected outside the
/// crate. Before a conflict is handed back to the user it is always resolved
/// into a [`Nogood`]; the user-facing `Model`/`Solver`/[`LoweringError`]
/// boundaries only ever expose a [`Nogood`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Conflict<Atom>(pub(crate) ConflictInner<Atom>);

/// The internal representation of a [`Conflict`]: a ready clause, or a reason
/// deferred to a propagator that holds it (which may be unresolved inside the
/// propagation loop).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConflictInner<Atom> {
	/// A conflict clause, holding the literals of the nogood directly.
	Clause(Box<[Atom]>),
	/// A conflict whose clause is computed on demand by a propagator (see
	/// [`DeferReasonActions::defer`](crate::actions::DeferReasonActions::defer)).
	Deferred {
		/// The literal whose (failed) assignment the propagator explains as the
		/// head of the clause, or `None` for a root conflict.
		subject: Option<Atom>,
		/// Reference to the propagator that computes the conflict clause.
		propagator: u32,
		/// Data to be given to the propagator to compute the reason.
		data: u64,
	},
}

/// A trait for constraints that can be placed in a [`Model`] object.
///
/// Constraints specified in the library implement this trait, but are using
/// their explicit type in an enumerated type to allow for global model
/// analysis.
pub trait Constraint<E: ReasoningEngine + ?Sized>: Any + Debug + DynClone + Propagator<E> {
	/// Analyze the constraint to declare the literal encoding it requires, and
	/// to contribute polarity evidence for the decision variables it involves.
	///
	/// This stage runs once on the [`Model`] before lowering. The default
	/// implementation contributes nothing.
	fn analyze(&self, context: &mut E::InitializationContext<'_>) {
		let _ = context;
	}

	/// Simplify the [`Model`] given the current constraint.
	///
	/// This method is expected to reduce the domains of decision variables,
	/// rewrite the constraint to a simpler form, or detect when the constraint
	/// is already subsumed by the current state of the model.
	fn simplify(
		&mut self,
		context: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict>;

	/// Encode the constraint using [`Propagator`] objects or clauses for a
	/// [`Solver`](solver::Solver) object.
	///
	/// This method should place all required propagators and/or clauses in a
	/// [`Solver`](solver::Solver) object to ensure the constraint will not be
	/// violated.
	fn to_solver(&self, context: &mut LoweringContext<'_>) -> Result<(), LoweringError>;
}

/// Helper trait to simplify trait bounds for [`Constraint`] implementations.
pub trait IntModelActions<E>
where
	E: ReasoningEngine,
	Self: IntSolverActions<E>
		+ for<'a> IntAnalyzeActions<E::InitializationContext<'a>>
		+ for<'a> IntSimplificationActions<E::PropagationContext<'a>>
		+ Into<model::View<IntVal>>,
{
}

/// Helper trait to simplify trait bounds for [`Propagator`] implementations.
pub trait IntSolverActions<E>
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> IntInitActions<E::InitializationContext<'a>>
		+ for<'a> IntExplanationActions<E::ExplanationContext<'a>>
		+ for<'a> IntInspectionActions<E::NotificationContext<'a>>
		+ for<'a> IntPropagationActions<E::PropagationContext<'a>>,
{
}

/// A resolved conflict clause (nogood) reported to the user.
///
/// This is the form a [`Conflict`] takes once it leaves the propagation loop;
/// unlike [`Conflict`] it never holds a deferred reason.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Nogood<Atom>(pub(crate) Box<[Atom]>);

/// A trait for a propagator that is called during the search process to filter
/// the domains of decision variables, and detect inconsistencies.
///
/// Implementations of the propagator trait must be able to explain changes to
/// domains of decision variables as a conjunction of literals that imply the
/// change. If these explanations are too expensive to compute during
/// propagation, then the propagator can delay giving the explanation using
/// [`DeferReasonActions::defer`](crate::actions::DeferReasonActions::defer).
/// If the explanation is needed, then the propagation engine will revert the
/// state of the solver and call [`Propagator::explain`] to receive the
/// explanation.
pub trait Propagator<E: ReasoningEngine + ?Sized>: Debug + DynClone + 'static {
	/// Advises the propagator that the solver is backtracking.
	fn advise_of_backtrack(&mut self, context: &mut E::NotificationContext<'_>) {
		let _ = context;
		unreachable!("propagator did not provide a backtrack advisor implementation")
	}

	/// Advises the propagator that a Boolean decision (view) is assigned with
	/// the associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_bool_change(
		&mut self,
		context: &mut E::NotificationContext<'_>,
		data: u64,
	) -> bool {
		let _ = context;
		let _ = data;
		unreachable!("propagator did not provide a Boolean advisor implementation")
	}

	/// Advises the propagator that an integer decision view has changed with
	/// the associated data given when registering the advisor. If the advisor
	/// returns `true`, then the propagator will be enqueued.
	fn advise_of_int_change(
		&mut self,
		context: &mut E::NotificationContext<'_>,
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
	/// lazy explanation emitted by the propagator. The propagator must now push
	/// the (conjunction of) literals into `reason` that led to a literal being
	/// propagated.
	///
	/// The method is called with the data that was passed to the
	/// [`DeferReasonActions::defer`](crate::actions::DeferReasonActions::defer)
	/// method, and the literal that was propagated. If the `lit` argument is
	/// `None`, then the reason was used to explain `false`.
	///
	/// The state of the solver is reverted to the state before the propagation
	/// of the `lit` to be explained.
	fn explain(
		&mut self,
		context: &mut E::ExplanationContext<'_>,
		lit: E::Atom,
		data: u64,
		reason: &mut E::ReasonSink<'_>,
	) {
		let _ = context;
		let _ = lit;
		let _ = data;
		let _ = reason;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}

	/// This method is called when the propagator is posted to the solver to
	/// allow the propagator to subscribe to events.
	fn initialize(&mut self, context: &mut E::InitializationContext<'_>);

	/// The propagate method is called during the search process to allow the
	/// propagator to enforce its constraint.
	fn propagate(&mut self, context: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict>;
}

/// Status returned by the [`Constraint::simplify`] method,
/// indicating whether the constraint has been subsumed (such that it can be
/// removed from the [`Model`]) or not.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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

/// A reason closure that pushes no conditions: the propagation or conflict it
/// justifies holds *unconditionally*.
///
/// The deliberately alarming, `UPPER_CASE` name marks this as dangerous: using
/// an empty reason for a fact that is not genuinely unconditional produces an
/// unsound explanation. Pass it in place of a reason closure, e.g.
/// `ctx.declare_conflict(NO_REASON)`.
#[expect(
	non_snake_case,
	reason = "an UPPER_CASE marker makes an empty (dangerous) reason stand out at call sites"
)]
pub(crate) fn NO_REASON<Ctx: PropagationContext + ?Sized>(
	_ctx: &mut Ctx,
	_reason: &mut Ctx::ReasonSink<'_>,
) {
}

/// Pin the argument types of a reason closure to a given
/// [`PropagationContext`], returning the closure unchanged.
///
/// Passing the closure through this function supplies `Ctx` explicitly via the
/// turbofish; the `FnOnce` bound then drives inference of both parameters,
/// keeping the closure arguments type annotation-free:
///
/// ```ignore
/// let reason = reason_ty::<E::PropagationContext<'_>, _>(|ctx, reason| {
///     reason.push(self.x.min_lit(ctx));
/// });
/// self.y.tighten_min(ctx, bound, reason)?;
/// self.y.tighten_max(ctx, other, reason)?;
/// ```
pub(crate) fn reason_ty<Ctx: PropagationContext, F: FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>)>(
	f: F,
) -> F {
	f
}

impl<E, B> BoolModelActions<E> for B
where
	E: ReasoningEngine,
	B: BoolSolverActions<E>
		+ for<'a> BoolAnalyzeActions<E::InitializationContext<'a>>
		+ for<'a> BoolSimplificationActions<E::PropagationContext<'a>>
		+ Into<model::View<bool>>,
{
}

impl<E, B> BoolSolverActions<E> for B
where
	E: ReasoningEngine + ?Sized,
	Self: for<'a> BoolInitActions<E::InitializationContext<'a>>
		+ for<'a> BoolInspectionActions<E::ExplanationContext<'a>>
		+ for<'a> BoolInspectionActions<E::NotificationContext<'a>>
		+ for<'a> BoolPropagationActions<E::PropagationContext<'a>>
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

impl<Atom> Conflict<Atom> {
	/// Resolve the conflict into its [`Nogood`] clause.
	///
	/// A conflict is only ever handed to the user after the propagation loop
	/// has resolved any deferred reason (the engine in
	/// [`SolvingContext`](crate::solver::solving_context::SolvingContext), the
	/// model in `Model::propagate_single`), so it must be a ready clause by
	/// this point.
	pub(crate) fn into_nogood(self) -> Nogood<Atom> {
		match self.0 {
			ConflictInner::Clause(lits) => Nogood(lits),
			ConflictInner::Deferred { .. } => {
				unreachable!("a deferred conflict must be resolved before reaching the user")
			}
		}
	}
}

impl Conflict<solver::Decision<bool>> {
	/// Write the conflict's nogood clause into `clause`.
	///
	/// A ready clause already holds the nogood in clausal form, so its literals
	/// are copied straight in; a deferred conflict pushes its `subject` as the
	/// head and asks the propagator to compute the reason, which it negates
	/// through the [`EngineReasonSink`] sink.
	pub(crate) fn explain(
		&self,
		props: &mut [BoxedPropagator],
		actions: &mut State,
		mut clause: ClauseBuilder<'_>,
	) {
		match &self.0 {
			ConflictInner::Clause(lits) => clause.extend(lits.iter().map(|lit| lit.0)),
			&ConflictInner::Deferred {
				subject,
				propagator,
				data,
			} => {
				if let Some(subject) = subject {
					clause.push(subject.0);
				}
				let mut explanation = EngineReasonSink(clause);
				let head = subject.map(|s| s.into()).unwrap_or(true.into());
				props[propagator as usize].explain(actions, head, data, &mut explanation);
			}
		}
	}
}

impl<E, I> IntModelActions<E> for I
where
	E: ReasoningEngine,
	I: IntSolverActions<E>
		+ for<'a> IntAnalyzeActions<E::InitializationContext<'a>>
		+ for<'a> IntSimplificationActions<E::PropagationContext<'a>>
		+ Into<model::View<IntVal>>,
{
}

impl<E, I> IntSolverActions<E> for I
where
	E: ReasoningEngine + ?Sized,
	I: for<'a> IntInitActions<E::InitializationContext<'a>>
		+ for<'a> IntExplanationActions<E::ExplanationContext<'a>>
		+ for<'a> IntInspectionActions<E::NotificationContext<'a>>
		+ for<'a> IntPropagationActions<E::PropagationContext<'a>>,
{
}

impl<Atom> Nogood<Atom> {
	/// Returns an non-consuming iterator over the atom in the nogood clause.
	pub fn iter(&self) -> slice::Iter<'_, Atom> {
		self.0.iter()
	}
}

impl Nogood<solver::Decision<bool>> {
	/// Build the reported [`Nogood`] from the Boolean views that make up a
	/// conflict clause, resolving any constant views.
	pub(crate) fn from_view_iter(iter: impl IntoIterator<Item = solver::View<bool>>) -> Self {
		Self(
			iter.into_iter()
				.filter_map(|atom| match atom.0 {
					BoolView::Lit(lit) => Some(lit),
					BoolView::Const(true) => unreachable!("invalid nogood: contains `true`"),
					BoolView::Const(false) => None,
				})
				.collect(),
		)
	}
}

impl<Atom: Debug> Error for Nogood<Atom> {}

impl<Atom> IntoIterator for Nogood<Atom> {
	type IntoIter = <Box<[Atom]> as IntoIterator>::IntoIter;

	type Item = Atom;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<Atom: Debug> fmt::Display for Nogood<Atom> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "conflict detected: nogood {:?}", self.0)
	}
}
