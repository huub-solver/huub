//! Traits that encapsulate different sets of actions that can be performed at
//! different phases and by different objects in the solving process.

mod analyze;
mod boolean;
mod initialization;
mod integer;

use std::{marker::PhantomData, ops::Not};

pub use crate::actions::{
	analyze::{BoolAnalyzeActions, IntAnalyzeActions},
	boolean::{
		BoolInspectionActions, BoolOperations, BoolPropagationActions, BoolSimplificationActions,
	},
	initialization::{BoolInitActions, BrancherInitActions, InitActions, IntInitActions},
	integer::{
		IntDecisionActions, IntEvent, IntExplanationActions, IntInspectionActions, IntOperations,
		IntPropCond, IntPropagationActions, IntSimplificationActions,
	},
};
use crate::{
	constraints::{BoxedPropagator, Constraint},
	helpers::bytes::Bytes,
};

/// Actions that can be performed during the construction of
/// [`Propagator`](crate::constraints::Propagator)s and
/// [`Constraint`]s.
pub trait ConstructionActions {
	/// Create a new trailed integer value with the given initial value.
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T>;
}

/// Actions that can be performed by a
/// [`Brancher`](crate::solver::branchers::Brancher) when making search
/// decisions.
pub trait DecisionActions: TrailingActions {
	/// Returns the number of conflicts up to this point in the search process.
	fn num_conflicts(&self) -> u64;
}

/// A reason sink that additionally lets a propagator *defer* a reason: instead
/// of creating it immediately, it records that the reason is to be computed on
/// demand by the current propagator's
/// [`explain`](crate::constraints::Propagator::explain) (given `data`).
///
/// These actions are only available to [`PropagationContext`]s that are given
/// to [`Propagator`](crate::constraints::Propagator) implementations.
pub trait DeferReasonActions<Atom>: ReasonActions<Atom> {
	/// Defer this reason to the current propagator, which will compute it using
	/// `data` when the reason is needed.
	fn defer(&mut self, data: u64);
}

/// Actions that can be performed when posting propagators to the
/// [`Solver`](crate::solver::Solver).
pub trait PostingActions: ConstructionActions + PropagationContext {
	/// Add a new clause to be enforced by the solver.
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Add a new propagator to be initialized and propagated by the solver.
	fn add_propagator(&mut self, propagator: BoxedPropagator);
}

/// General actions that can be performed in
/// [`ReasoningEngine::PropagationContext`].
pub trait PropagationActions: DecisionActions + PropagationContext {
	/// Declare that the reason built by the given closure represents a conflict
	/// in the current state, requiring backtracking.
	///
	/// Note that it is generally recommended to use this method only when
	/// integer or Boolean propagation methods do not seem relevant.
	fn declare_conflict(
		&mut self,
		reason: impl FnOnce(&mut Self, &mut Self::ReasonSink<'_>),
	) -> Self::Conflict;
}

/// A context that can raise conflicts and build reasons for the changes it
/// makes.
///
/// This extends [`ReasoningContext`] with the
/// [`Conflict`](PropagationContext::Conflict) it can raise and the
/// [`ReasonSink`](PropagationContext::ReasonSink) into which a reason closure
/// pushes its atoms.
pub trait PropagationContext: ReasoningContext {
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;

	/// The sink into which a reason closure pushes the atoms of a reason while
	/// it is being built in this context.
	type ReasonSink<'a>: ReasonActions<Self::Atom>;
}

/// Actions for building the explanation of a propagation: the conjunction of
/// reason atoms that imply the change being explained (see
/// [`Propagator::explain`](crate::constraints::Propagator::explain)).
pub trait ReasonActions<Atom>: Extend<Atom> {
	/// Add a reason atom to the explanation.
	fn push(&mut self, atom: Atom);

	/// Reserve capacity for at least `additional` more reason atoms.
	///
	/// This is a hint; implementations that cannot usefully reserve may ignore
	/// it.
	fn reserve(&mut self, additional: usize) {
		let _ = additional;
	}
}

/// The `ReasoningContext` trait names the fundamental reasoning types used by
/// the context objects used by the various action traits.
pub trait ReasoningContext {
	/// Type used to represent an atom in a reason for propagation.
	type Atom: BoolOperations + Not<Output = Self::Atom>;
}

/// Trait for environments that support constraint propagation and decision
/// variable pruning to simplify the current problem state.
pub trait ReasoningEngine {
	/// Type used to represent an atom in a reason for propagation.
	type Atom: BoolOperations + Not<Output = Self::Atom>;
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;

	/// The context given to the constraint propagator when they are asked to
	/// explain a reason for a change they deferred with
	/// [`DeferReasonActions::defer`].
	type ExplanationContext<'a>: ReasoningContext<Atom = Self::Atom> + TrailingActions;
	/// The context given to constraint propagators to attach themselves to
	/// changes in the state of the reasoning engine or decision variables.
	type InitializationContext<'a>: ReasoningContext<Atom = Self::Atom> + InitActions;
	/// The context given to constraint propagators when they are advised of a
	/// change in the state of the reasoning engine or decision variables.
	type NotificationContext<'a>: ReasoningContext<Atom = Self::Atom> + TrailingActions;
	/// The context given to constraint propagators when they are asked to
	/// propagate changes based on the constraint they enforce.
	type PropagationContext<'a>: for<'b> PropagationContext<
			Atom = Self::Atom,
			Conflict = Self::Conflict,
			ReasonSink<'b>: DeferReasonActions<Self::Atom>,
		> + PropagationActions<Atom = Self::Atom, Conflict = Self::Conflict>;

	/// The sink given to
	/// [`Propagator::explain`](crate::constraints::Propagator::explain)
	/// to receive the conjunction of reason atoms that imply the propagated
	/// atom.
	///
	/// Unlike the propagation context's reason sink, an explanation is always
	/// eager and can never defer so this is only a [`ReasonActions`], and not a
	/// [`DeferReasonActions`].
	type ReasonSink<'a>: ReasonActions<Self::Atom>;
}

/// Actions that can be performed to simplify a [`Model`](crate::model::Model)
/// considering a given constraint.
pub trait SimplificationActions {
	/// The type of the reasoning engine that is used when adding new
	/// constraints.
	type Target: ReasoningEngine;

	/// Post a constraint to the model, mirroring
	/// [`Model::post_constraint`](crate::model::Model::post_constraint).
	///
	/// This functionality is generally used to replace the current constraint
	/// by a new one. The [`Constraint::simplify`] step posts one or more new
	/// constraints, and then returns
	/// [`SimplificationStatus::Subsumed`](crate::constraints::SimplificationStatus::Subsumed) to
	/// indicate that the current constraint can be removed.
	fn post_constraint<C: Constraint<Self::Target>>(&mut self, constraint: C);
}

/// A typed handle to a value tracked by the trail.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Trailed<T: Bytes> {
	/// Index into the trail's integer value storage.
	pub(crate) index: u32,
	/// Marker that binds the stored type to this handle.
	pub(crate) ty: PhantomData<T>,
}

/// Basic actions that can be performed when the trailing infrastructure is
/// available.
pub trait TrailingActions {
	/// Set a [`Trailed`] value, replacing the current value with the new value.
	///
	/// If any backtracking occurs, the value will be restored to its previous
	/// value.
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T;

	/// Get the current value of a [`Trailed`] value.
	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T;
}

impl<Atom> ReasonActions<Atom> for Vec<Atom> {
	fn push(&mut self, atom: Atom) {
		Vec::push(self, atom);
	}

	fn reserve(&mut self, additional: usize) {
		Vec::reserve(self, additional);
	}
}
