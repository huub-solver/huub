//! Data structures used to support proof logging.
//!
//! When proof logging is enabled, the [`Engine`](crate::solver::engine::Engine)
//! is connected to the SAT oracle as a proof tracer, and emits `tracing` events
//! on the `"proof"` target describing the clauses that are added and derived.
//! The structures in this module are used to track the provenance of the
//! clauses that the solver itself communicates to the oracle, so that the
//! emitted events can be labeled with the constraint or solver rule from which
//! each clause originates.
//!
//! All bookkeeping is stored in a [`ProofState`] object that is only allocated
//! when proof logging is enabled, ensuring that the data structures on the hot
//! path of the solver keep their exact shape, and that the cost of the
//! provenance tracking is only paid when proof logging is requested.

use pindakaas::Lit as RawLit;
use rustc_hash::FxHashMap;

use crate::solver::engine::PropRef;

/// Provenance of a clause that originates from a user-posted constraint.
///
/// This type is also used at the [`Model`](crate::model::Model) level to record
/// the provenance of each posted constraint before it is lowered.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ConstraintSource {
	/// The name of the constraint as it was posted (e.g., the FlatZinc
	/// constraint identifier).
	pub(crate) name: &'static str,
	/// The index of the originating constraint item (e.g., the position of the
	/// constraint item in the FlatZinc instance).
	pub(crate) index: u32,
}

/// Provenance description of a clause communicated to the SAT oracle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProofSource {
	/// The clause originates from the user-posted constraint currently being
	/// lowered.
	///
	/// This variant owns its provenance because a constraint can emit clauses
	/// directly (i.e. without a propagator), so the label must be available
	/// during lowering before any propagator that enforces the constraint
	/// exists.
	Constraint(ConstraintSource),
	/// The clause originates from a constraint propagator, whose provenance is
	/// recorded in [`ProofState::propagator_source`].
	Propagator(PropRef),
	/// The clause originates from a solver-internal rule, e.g. the clauses
	/// defining an integer literal, an objective bound, or a solution no-good.
	Rule(&'static str),
}

/// Bookkeeping used to support proof logging.
///
/// This structure is only allocated (as part of
/// [`State`](crate::solver::engine::State)) when proof logging is enabled, and
/// all interactions with it are guarded by checking its presence.
#[derive(Clone, Debug, Default)]
pub(crate) struct ProofState {
	/// Sidecar of [`State::conflict`](crate::solver::engine::State::conflict):
	/// the propagator that detected the current conflict.
	pub(crate) conflict_source: Option<PropRef>,
	/// Sticky register containing the provenance that will be attached to the
	/// next original clause(s) reaching the oracle.
	///
	/// This register is read (but not consumed) by the proof tracer callbacks,
	/// allowing a batch of clauses with the same provenance to be labelled by
	/// setting the register once.
	pub(crate) next_hint: Option<ProofSource>,
	/// The literal that is propagated by the next reason or conflict clause
	/// reaching the oracle.
	///
	/// This register is consumed (using [`Option::take`]) by the proof tracer
	/// callbacks, so that the propagated literal can never leak onto an
	/// unrelated clause. The propagated literal allows proof formats that
	/// describe inferences, such as DRCP, to split a clause into its premises
	/// and its consequent.
	pub(crate) next_propagated: Option<RawLit>,
	/// The provenance of each propagator, indexed in lockstep with
	/// [`Engine::propagators`](crate::solver::engine::Engine::propagators).
	///
	/// Only propagators created while lowering a constraint carry a provenance;
	/// all other propagators store [`None`].
	pub(crate) propagator_source: Vec<Option<ConstraintSource>>,
	/// Sidecar of
	/// [`State::reason_map`](crate::solver::engine::State::reason_map):
	/// the propagator that queued each propagation.
	pub(crate) reason_source: FxHashMap<RawLit, PropRef>,
}

impl ProofState {
	/// Resolve the current [`Self::next_hint`] register, returning the name of
	/// the source and the index of the originating constraint item, if any.
	pub(crate) fn resolve_hint(&self) -> (&str, Option<u32>) {
		match &self.next_hint {
			Some(ProofSource::Constraint(src)) => (src.name, Some(src.index)),
			Some(ProofSource::Propagator(p)) => match &self.propagator_source[p.index()] {
				Some(src) => (src.name, Some(src.index)),
				None => ("", None),
			},
			Some(ProofSource::Rule(name)) => (name, None),
			None => ("", None),
		}
	}
}
