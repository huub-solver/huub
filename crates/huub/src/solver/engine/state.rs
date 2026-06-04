//! Internal state representation of the propagation engine.

use std::collections::{BTreeMap, VecDeque};

use pindakaas::{Lit as RawLit, Var as RawVar};
use rustc_hash::FxHashMap;
use tracing::debug;

use crate::{
	Clause, IntVal,
	actions::{ReasoningContext, ReasoningEngine, Trailed, TrailingActions},
	constraints::{Conflict, Reason},
	helpers::bytes::Bytes,
	solver::{
		IntLitMeaning, SearchStrategy, SwitchTrigger,
		activation_list::ActivationList,
		bool_to_int::BoolToIntMap,
		decision::{Decision, integer::IntDecision},
		engine::{AdvisorDef, Engine, LitPropagation, PropRef},
		queue::PropagatorQueue,
		trail::Trail,
		view::View,
	},
};

/// Engine-side diff-logic dispatch metadata.
///
/// Replaces the old monolithic `State::diff_logic` field. The full
/// runtime graph now lives inside a [`DiffLogicPropagator`](
/// crate::constraints::diff_logic::DiffLogicPropagator) registered
/// like any other [`Propagator`](crate::constraints::Propagator); this
/// struct just remembers which propagator slot owns the service and
/// caches the mid-search lazy gate Booleans so the engine's main loop
/// can splice freshly-minted edges in between propagation cycles.
#[derive(Clone, Debug, Default)]
pub(crate) struct DiffLitMap {
	/// Slot in `Engine.propagators` that owns the diff-logic
	/// service. `None` until [`DiffLogicConstraint::to_solver`](
	/// crate::constraints::diff_logic::DiffLogicConstraint::to_solver)
	/// runs.
	pub(crate) owner: Option<PropRef>,
	/// Mid-search subsumption cache for `b ↔ (x − y ≤ d)`. Populated
	/// in both directions (`(x, y, d) → b` and `(y, x, −d − 1) → !b`)
	/// at lowering time and on every mid-search lazy mint.
	pub(crate) diff_lit_cache:
		FxHashMap<(View<IntVal>, View<IntVal>), BTreeMap<IntVal, View<bool>>>,
	/// Mid-search lazy edges queued by
	/// [`SolvingContext::diff_logic_lazy_diff_lit`](
	/// crate::solver::solving_context::SolvingContext::diff_logic_lazy_diff_lit).
	/// Drained between propagation cycles in
	/// `SolvingContext::run_propagators` so the owner propagator can be
	/// borrowed exclusively (no re-entrant alias with the running
	/// propagator).
	pub(crate) pending_register_edges: Vec<(View<IntVal>, View<IntVal>, IntVal, View<bool>)>,
}

/// Statistical information about the execution of the propagation engine.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct EngineStatistics {
	/// Number of conflicts encountered
	pub(crate) conflicts: u64,
	/// Number of search directives left to the SAT solver
	pub(crate) sat_search_directives: u64,
	/// Peak search depth
	pub(crate) peak_depth: u32,
	/// Number of times a CP propagator was called
	pub(crate) propagations: u64,
	/// Number of restarts (signalled by the SAT solver)
	pub(crate) restarts: u32,
	/// Number of search directives following the user-specified search
	/// heuristics
	pub(crate) user_search_directives: u64,
	/// Number of eagerly created SAT literals to represent decisions variables
	pub(crate) eager_literals: u64,
	/// Number of lazily created SAT literals to represent decision variables
	pub(crate) lazy_literals: u64,
}

/// Internal state representation of the propagation engine disconnected from
/// the storage of the propagators and branchers.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`crate::constraints::BoxedPropagator`], but it is not intended
/// to be constructed by the user. It should merely be seen as the
/// implementation of the [`crate::actions::IntExplanationActions`] trait.
#[derive(Clone, Debug, Default)]
pub struct State {
	/// Search strategy to use during solving
	pub(crate) search_strategy: SearchStrategy,

	// ---- Trailed Value Infrastructure (e.g., decision variables) ----
	/// Storage for the data of the integer decision variables.
	pub(crate) int_vars: Vec<IntDecision>,
	/// Mapping from boolean variables to integer variables.
	pub(crate) bool_to_int: BoolToIntMap,
	/// Engine-side diff-logic dispatch metadata: owner [`PropRef`],
	/// mid-search subsumption cache, and the lazy-edge queue drained
	/// between propagation cycles. The full runtime graph (Johnson
	/// potentials, trailed adjacency lists, the propagation algorithm)
	/// lives inside a
	/// [`DiffLogicPropagator`](crate::constraints::diff_logic::DiffLogicPropagator)
	/// registered as a regular propagator via
	/// [`DiffLogicConstraint::to_solver`](
	/// crate::constraints::diff_logic::DiffLogicConstraint::to_solver).
	pub(crate) diff_lit_map: DiffLitMap,
	/// Trailed storage, including lower and upper bounds for integer variables
	/// and Boolean variable assignments.
	pub(crate) trail: Trail,
	/// Literals to be propagated by the SAT solver
	pub(crate) propagation_queue: VecDeque<LitPropagation>,
	/// Reasons for setting values.
	pub(crate) reason_map: FxHashMap<RawLit, Reason<Decision<bool>>>,
	/// Whether conflict has (already) been detected.
	pub(crate) conflict: Option<Conflict<Decision<bool>>>,
	/// Whether the solver is in a failure state.
	///
	/// Triggered when a conflict is detected during propagation, the solver
	/// should backtrack. Debug assertions will be triggered if other actions
	/// are taken instead. Some mechanisms, such as propagator queuing, might
	/// be disabled to optimize the execution of the solver.
	pub(crate) failed: bool,

	// ---- Non-Trailed Infrastructure ----
	/// Storage for clauses to be communicated to the solver.
	pub(crate) clauses: VecDeque<Clause<RawLit>>,
	/// Solving statistics.
	pub(crate) statistics: EngineStatistics,
	/// Whether search decisions are currently being deferred to the SAT solver.
	pub(crate) sat_search: bool,
	/// Counter used to determine whether to action the [`SearchStrategy`].
	pub(crate) search_trigger: u64,

	// ---- Queuing Infrastructure ----
	/// Advisor data storage.
	pub(crate) advisors: Vec<AdvisorDef>,
	/// List of propagators to advise of backtracking.
	pub(crate) notify_of_backtrack: Vec<PropRef>,
	/// Boolean variable enqueueing information.
	pub(crate) bool_activation:
		FxHashMap<RawVar, Vec<crate::solver::activation_list::ActivationActionS>>,
	/// Integer variable enqueueing information.
	pub(crate) int_activation: Vec<ActivationList>,
	/// Queue of propagators awaiting action.
	pub(crate) propagator_queue: PropagatorQueue,
	/// Last literal propagated by the Engine.
	pub(crate) last_propagated:
		Option<(RawLit, Option<(Decision<IntVal>, crate::actions::IntEvent)>)>,

	// ---- Debugging Helpers ----
	/// List of integer variables that have been notified as fixed, but should
	/// be checked that the bounds match before propagation.
	#[cfg(debug_assertions)]
	pub(crate) check_int_fixed: Vec<(Decision<IntVal>, IntVal)>,
}

impl State {
	/// Returns the current decision level of the solver.
	pub(crate) fn decision_level(&self) -> u32 {
		self.trail.decision_level()
	}

	/// Internal method to get the integer variable and strongest
	/// [`IntLitMeaning`] for a given literal, if it is an integer literal.
	pub(crate) fn get_int_lit_meaning(
		&self,
		lit: Decision<bool>,
	) -> Option<(Decision<IntVal>, IntLitMeaning)> {
		let (iv, meaning) = self.bool_to_int.get(lit.0.var())?;
		let meaning = match meaning {
			// Eager literal, request meaning from variable itself.
			None => self.int_vars[iv.idx()].lit_meaning(lit),
			// Lazy literal, transform negated meanings dealing with gaps in domain when necessary.
			Some(IntLitMeaning::Less(i)) if !lit.is_negated() => {
				let i = self.int_vars[iv.idx()].tighten_less_lit(i);
				IntLitMeaning::Less(i)
			}
			Some(m) if lit.is_negated() => !m,
			Some(m) => m,
		};
		Some((iv, meaning))
	}

	/// Internal method called to process the backtracking to an earlier
	/// decision level.
	///
	/// The generic argument `ARTIFICIAL` is used to signal when the solver is
	/// backtracking from an artificial decision level. An example of the use
	/// of artificial decision levels is found in the `Engine::check_solution`
	/// method, where it is used to artificially fix any integer variables
	/// using lazy encoding.
	pub(crate) fn notify_backtrack<const ARTIFICIAL: bool>(&mut self, level: usize, restart: bool) {
		debug_assert!(!ARTIFICIAL || level as u32 == self.trail.decision_level() - 1);
		debug_assert!(!ARTIFICIAL || !restart);
		// Resolve the conflict status
		self.failed = false;
		self.conflict = None;
		// Remove (now invalid) propagations (but leave clauses in place)
		self.last_propagated = None;
		self.propagation_queue.clear();
		#[cfg(debug_assertions)]
		{
			// (DEBUG ONLY) Clear the debug checking queues.
			self.check_int_fixed.clear();
		}
		// Backtrack trail
		self.trail.notify_backtrack(level);
		// Empty propagation queue
		while self.propagator_queue.pop().is_some() {}
		if ARTIFICIAL {
			return;
		}

		// Update conflict statistics
		self.statistics.conflicts += 1;

		// Handle conflict-based search strategies
		if let SearchStrategy::Interleaved(SwitchTrigger::Conflicts(cfl))
		| SearchStrategy::Transition(SwitchTrigger::Conflicts(cfl)) = self.search_strategy
		{
			self.search_trigger += 1;
			// Change search strategy if the counted number of conflicts exceeds the
			// threshold
			if self.search_trigger >= cfl {
				self.sat_search = !self.sat_search;
				self.search_trigger = 0;
				debug!(
					target: "solver",
					sat_search = self.sat_search,
					conflicts = self.statistics.conflicts,
					"change search strategy after reaching conflict threshold"
				);
				// Transition has been completed. Strategy has permanently switched to SAT.
				if let SearchStrategy::Transition(_) = self.search_strategy {
					self.search_strategy = SearchStrategy::Sat;
				}
			}
		}

		if restart {
			// Update restart statistics
			self.statistics.restarts += 1;

			// Handle restart-based search strategies
			if let SearchStrategy::Interleaved(SwitchTrigger::Restarts(rst))
			| SearchStrategy::Transition(SwitchTrigger::Restarts(rst)) = self.search_strategy
			{
				self.search_trigger += 1;
				// Change search strategy if the counted number of restarts exceeds the
				// threshold
				if self.search_trigger >= rst {
					self.sat_search = !self.sat_search;
					self.search_trigger = 0;
					debug!(
						target: "solver",
						sat_search = self.sat_search,
						restarts = self.statistics.restarts,
						"change search strategy after reaching restart threshold"
					);
					// Transition has been completed. Strategy has permanently switched to SAT.
					if let SearchStrategy::Transition(_) = self.search_strategy {
						self.search_strategy = SearchStrategy::Sat;
					}
				}
			}
			if level == 0 {
				// Memory cleanup (Reasons are known to no longer be relevant)
				self.reason_map.clear();
			}
		}
	}

	/// Internal method called to trigger a new decision level.
	pub(crate) fn notify_new_decision_level(&mut self) {
		self.trail.notify_new_decision_level();
	}

	/// Register the [`Reason`] to explain why `lit` has been assigned.
	pub(crate) fn register_reason(
		&mut self,
		lit: RawLit,
		built_reason: Result<Reason<Decision<bool>>, bool>,
	) {
		match built_reason {
			Ok(reason) => {
				// Insert new reason, possibly overwriting old one (from previous search
				// attempt)
				self.reason_map.insert(lit, reason);
			}
			Err(true) => {
				// The propagator built a reason whose atoms all reduce to
				// `BoolView::Const(true)` — i.e. the propagation is
				// universally entailed and needs no antecedents. Store
				// an explicit empty-conjunction reason so the debug
				// `debug_check_reason` invariant ("propagated literals at
				// non-zero levels have a registered reason") holds. The
				// downstream `add_reason_clause` materializes this as
				// `vec![propagated_lit]` — a tautological unit clause
				// that SAT treats as a level-0 unit, matching the
				// semantics of a universal fact.
				self.reason_map
					.insert(lit, Reason::Eager(Vec::new().into_boxed_slice()));
			}
			Err(false) => unreachable!("invalid reason"),
		}
	}

	/// Set the overarching search strategy to use during solving.
	pub(crate) fn set_search_strategy(&mut self, strategy: SearchStrategy) {
		self.search_strategy = strategy;
		self.sat_search = matches!(self.search_strategy, SearchStrategy::Sat);
		self.search_trigger = 0;
	}
}

impl ReasoningContext for State {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl TrailingActions for State {
	fn set_trailed<T: Bytes>(&mut self, x: Trailed<T>, v: T) -> T {
		self.trail.set_trailed(x, v)
	}

	fn trailed<T: Bytes>(&self, x: Trailed<T>) -> T {
		self.trail.trailed(x)
	}
}
