//! Traits that encapsulate different sets of actions that can be performed at
//! different phases and by different objects in the solving process.

mod boolean;
mod initialization;
mod integer;

use std::{marker::PhantomData, ops::Not};

pub use crate::actions::{
	boolean::{
		BoolInspectionActions, BoolOperations, BoolPropagationActions, BoolSimplificationActions,
	},
	initialization::{BoolInitActions, BrancherInitActions, InitActions, IntInitActions},
	integer::{
		IntDecisionActions, IntExplanationActions, IntInspectionActions, IntOperations,
		IntPropagationActions, IntSimplificationActions,
	},
};
use crate::{
	constraints::{BoxedPropagator, Constraint, DeferredReason, ReasonBuilder},
	helpers::bytes::Bytes,
};

/// Actions that can be performed during the construction of [`Propagator`]s and
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

/// Actions that can be performed when posting propagators to the
/// [`Solver`](crate::solver::Solver).
pub trait PostingActions: ConstructionActions + ReasoningContext {
	/// Add a new clause to be enforced by the solver.
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict>;

	/// Add a new propagator to be initialized and propagated by the solver.
	fn add_propagator(&mut self, propagator: BoxedPropagator);
}

/// General actions that can be performed in [`ReasoningEngine::PropagationCtx`]
pub trait PropagationActions: DecisionActions + ReasoningContext {
	/// Declare that given reason (seen as a conjunction of atoms) is represents
	/// a conflict in the current state (requiring backtracking).
	///
	/// Note that it is generally recommended to use this method only when
	/// integer or Boolean propagation methods do not seem relevant.
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self>) -> Self::Conflict;

	/// Create a placeholder reason that will cause the solver to call the
	/// propagator's [`crate::constraints::Propagator::explain`] method when the
	/// reason is needed.
	fn deferred_reason(&self, data: u64) -> DeferredReason;
}

/// The ReasoningContext trait names the fundamental reasoning types used by the
/// context objects used by the various Action traits.
pub trait ReasoningContext {
	/// Type used to represent an atom in an reason for propagation.
	type Atom: BoolOperations + Not<Output = Self::Atom>;
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;
}

/// Trait for environments that support constraint propagation and decision
/// variable pruning to simplify the current problem state.
pub trait ReasoningEngine {
	/// Type used to represent an atom in an reason for propagation.
	type Atom: BoolOperations + Not<Output = Self::Atom>;
	/// Type used to represent a conflict that occurs during propagation.
	type Conflict;

	/// The context given to the constraint propagator when they are asked to
	/// explain a reason for a change they made using
	/// [`PropagationActions::deferred_reason`].
	type ExplanationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ TrailingActions;
	/// The context given to constraint propagators to attach themselves to
	/// changes in the state of the reasoning engine or decision variables.
	type InitializationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ InitActions;
	/// The context given to constraint propagators when they are advised of a
	/// change in the state of the reasoning engine or decision variables.
	type NotificationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ TrailingActions;
	/// The context given to constraint propagators when they are asked to
	/// propagate changes based on the constraint they enforce.
	type PropagationCtx<'a>: ReasoningContext<Atom = Self::Atom, Conflict = Self::Conflict>
		+ PropagationActions<Atom = Self::Atom, Conflict = Self::Conflict>;
}

/// Actions that can be performed to simplify a Model considering a given
/// constraint.
pub trait SimplificationActions {
	/// The type of the reasoning engine that is used when adding new
	/// constraints.
	type Target: ReasoningEngine;

	/// Post a constraint to the model, mirroring [`Model::post_constraint`].
	///
	/// This functionality is generally used to replaced the current constraint
	/// by a new one. The [`Constraint::simplify`] step one or more new
	/// constraints and then returns [`SimplificationStatus::Subsumed`] to
	/// indicate that the current constraint can be removed.
	fn post_constraint<C: Constraint<Self::Target>>(&mut self, constraint: C);
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A typed handle to a value tracked by the trail.
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
