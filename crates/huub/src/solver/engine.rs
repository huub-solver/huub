//! Module containing the main propagation engine of the solver.

/// Macro to output a trace message when a new literal is registered.
macro_rules! trace_new_lit {
	($iv:expr, $def:expr, $lit:expr) => {
		tracing::debug!(
			lit = i32::from($lit),
			int_var = usize::from($iv),
			is_eq = matches!($def.meaning, IntLitMeaning::Eq(_)),
			val = match $def.meaning {
				IntLitMeaning::Eq(val) => val,
				IntLitMeaning::Less(val) => val,
				_ => unreachable!(),
			},
			"register new literal"
		);
		tracing::trace!(lit = i32::from($lit), "lazy literal")
	};
}

use std::{
	collections::{HashMap, VecDeque},
	mem,
};

use delegate::delegate;
use index_vec::IndexVec;
use pindakaas::{
	solver::propagation::{
		ClausePersistence, Propagator as PropagatorExtension, SearchDecision, SolvingActions,
	},
	Lit as RawLit, Var as RawVar,
};
pub(crate) use trace_new_lit;
use tracing::{debug, trace};

use crate::{
	actions::{DecisionActions, ExplanationActions, InspectionActions, TrailingActions},
	branchers::{BoxedBrancher, Decision},
	constraints::{BoxedPropagator, Reason},
	solver::{
		activation_list::{ActivationList, IntEvent},
		bool_to_int::BoolToIntMap,
		int_var::{IntVar, IntVarRef, OrderStorage},
		queue::{PriorityLevel, PriorityQueue},
		solving_context::SolvingContext,
		trail::{Trail, TrailedInt},
		BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner, SolverConfiguration,
	},
	Clause, Conjunction, IntVal,
};

#[derive(Debug, Default, Clone)]
/// A propagation engine implementing the [`Propagator`] trait.
pub struct Engine {
	/// Storage of the propagators.
	pub(crate) propagators: IndexVec<PropRef, BoxedPropagator>,
	/// Storage of the branchers.
	pub(crate) branchers: Vec<BoxedBrancher>,
	/// Internal State representation of the propagation engine.
	pub(crate) state: State,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct SearchStatistics {
	/// Number of conflicts encountered
	pub(crate) conflicts: u64,
	/// Number of search decisions left to the oracle solver
	pub(crate) oracle_decisions: u64,
	/// Peak search depth
	pub(crate) peak_depth: u32,
	/// Number of times a CP propagator was called
	pub(crate) propagations: u64,
	/// Number of backtracks to level 0
	pub(crate) restarts: u32,
	/// Number of decisions following the user-specified search heuristics
	pub(crate) user_decisions: u64,
}

#[derive(Clone, Debug, Default)]
/// Internal state representation of the propagation engine disconnected from
/// the storage of the propagators and branchers.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`BoxedPropgator`], but it is not intended to be constructed by
/// the user. It should merely be seen as the implementation of the
/// [`ExplanationActions`] trait.
pub struct State {
	/// Solver configuration
	pub(crate) config: SolverConfiguration,

	// ---- Trailed Value Infrastructure (e.g., decision variables) ----
	/// Storage for the integer variables and
	pub(crate) int_vars: IndexVec<IntVarRef, IntVar>,
	/// Mapping from boolean variables to integer variables
	pub(crate) bool_to_int: BoolToIntMap,
	/// Trailed Storage
	/// Includes lower and upper bounds for integer variables and Boolean variable assignments
	pub(crate) trail: Trail,
	/// Literals to be propagated by the oracle
	pub(crate) propagation_queue: Conjunction,
	/// Reasons for setting values
	pub(crate) reason_map: HashMap<RawLit, Reason>,
	/// Whether conflict has (already) been detected
	pub(crate) conflict: Option<Clause>,
	/// Whether the solver is in a failure state.
	///
	/// Triggered when a conflict is detected during propagation, the solver
	/// should backtrack. Debug assertions will be triggered if other actions are
	/// taken instead. Some mechanisms, such as propagator queueing, might be
	/// disabled to optimize the execution of the solver.
	pub(crate) failed: bool,

	// ---- Non-Trailed Infrastructure ----
	/// Storage for clauses to be communicated to the solver
	pub(crate) clauses: VecDeque<Clause>,
	/// Solving statistics
	pub(crate) statistics: SearchStatistics,
	/// Whether VSIDS is currently enabled
	pub(crate) vsids: bool,

	// ---- Queueing Infrastructure ----
	/// Boolean variable enqueueing information
	pub(crate) bool_activation: HashMap<RawVar, Vec<PropRef>>,
	/// Integer variable enqueueing information
	pub(crate) int_activation: IndexVec<IntVarRef, ActivationList>,
	/// Queue of propagators awaiting action
	pub(crate) propagator_queue: PriorityQueue<PropRef>,
	/// Priority within the queue for each propagator
	pub(crate) propagator_priority: IndexVec<PropRef, PriorityLevel>,
	/// Flag for whether a propagator is enqueued
	pub(crate) enqueued: IndexVec<PropRef, bool>,
}

impl PropagatorExtension for Engine {
	fn add_external_clause(
		&mut self,
		_slv: &mut dyn SolvingActions,
	) -> Option<(Clause, ClausePersistence)> {
		if !self.state.clauses.is_empty() {
			let clause = self.state.clauses.pop_front(); // Known to be `Some`
			trace!(clause = ?clause.as_ref().unwrap().iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add external clause");
			clause.map(|c| (c, ClausePersistence::Irreduntant))
		} else if !self.state.propagation_queue.is_empty() {
			None // Require that the solver first applies the remaining propagation
		} else if let Some(conflict) = self.state.conflict.take() {
			debug!(clause = ?conflict.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add conflict clause");
			Some((conflict, ClausePersistence::Forgettable))
		} else {
			None
		}
	}

	fn add_reason_clause(&mut self, propagated_lit: RawLit) -> Clause {
		// Find reason
		let reason = self.state.reason_map.remove(&propagated_lit);
		// Restore the current state to the state when the propagation happened if explaining lazily
		if matches!(reason, Some(Reason::Lazy(_))) {
			self.state.trail.goto_assign_lit(propagated_lit);
		}
		// Create a clause from the reason
		let clause = if let Some(reason) = reason {
			reason.explain(&mut self.propagators, &mut self.state, Some(propagated_lit))
		} else {
			vec![propagated_lit]
		};

		debug!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add reason clause");
		clause
	}

	#[tracing::instrument(level = "debug", skip(self, slv, _sol))]
	fn check_solution(
		&mut self,
		slv: &mut dyn SolvingActions,
		_sol: &dyn pindakaas::Valuation,
	) -> bool {
		// Solver should not be in a failed state (no propagator conflict should
		// exist), and any conflict should have been communicated to the SAT oracle.
		debug_assert!(!self.state.failed);
		debug_assert!(self.state.conflict.is_none());
		// All propagation should have been communicated to the SAT oracle.
		debug_assert!(self.state.propagation_queue.is_empty());

		// Check model consistency assuming that all currently unfixed integer
		// variables take the lower bound as its value.
		//
		// Add artificial decision level to fix unfixed integer variables
		let level = self.state.decision_level();
		self.state.notify_new_decision_level();

		// Create a propagation context
		let mut ctx = SolvingContext::new(slv, &mut self.state);

		// Calculate values of each integer and notify popgators
		for r in (0..ctx.state.int_vars.len()).map(IntVarRef::new) {
			let (lb, ub) = ctx.state.int_vars[r].get_bounds(&ctx.state.trail);
			if lb != ub {
				debug_assert!(matches!(
					ctx.state.int_vars[r].order_encoding,
					OrderStorage::Lazy(_)
				));

				// Ensure the lazy literal for the upper bound exists
				let ub_lit = ctx.get_intref_lit(r, IntLitMeaning::Less(lb + 1));
				if let BoolViewInner::Lit(ub_lit) = ub_lit.0 {
					let prev = ctx.state.trail.assign_lit(ub_lit);
					debug_assert_eq!(prev, None);
				}
				let prev_ub = ctx.state.int_vars[r].notify_upper_bound(&mut ctx.state.trail, lb);
				debug_assert!(prev_ub > lb);

				ctx.state.enqueue_int_propagators(r, IntEvent::Fixed, None);
			}
		}

		// Run propgagators to find any conflicts
		ctx.run_propagators(&mut self.propagators);
		// No propagation can be triggered (all variables are fixed, so only
		// conflicts are possible)
		debug_assert!(self.state.propagation_queue.is_empty());

		// Process propagation results, and accept model if no conflict is detected
		let conflict = self.state.conflict.take();

		// Revert to real decision level
		self.state.notify_backtrack::<true>(level as usize, false);
		debug_assert!(self.state.conflict.is_none());
		self.state.conflict = conflict;

		let accept = self.state.conflict.is_none();
		debug!(accept, "check model");
		accept
	}

	fn decide(&mut self, slv: &mut dyn SolvingActions) -> SearchDecision {
		if !self.state.vsids {
			let mut current = self.state.trail.get_trailed_int(Trail::CURRENT_BRANCHER) as usize;
			if current == self.branchers.len() {
				self.state.statistics.oracle_decisions += 1;
				return SearchDecision::Free;
			}
			let mut ctx = SolvingContext::new(slv, &mut self.state);
			while current < self.branchers.len() {
				match self.branchers[current].decide(&mut ctx) {
					Decision::Select(lit) => {
						debug!(lit = i32::from(lit), "decide");
						self.state.statistics.user_decisions += 1;
						return SearchDecision::Assign(lit);
					}
					Decision::Exhausted => {
						current += 1;
						let _ = ctx.set_trailed_int(Trail::CURRENT_BRANCHER, current as i64);
					}
					Decision::Consumed => {
						// Remove the brancher
						//
						// Note that this shifts all subsequent branchers (so we don't need to
						// increment current), but has bad complexity. However, due to the low
						// number of branchers, this is (likely) acceptable.
						let _ = self.branchers.remove(current);
					}
				}
			}
		}
		self.state.statistics.oracle_decisions += 1;
		SearchDecision::Free
	}

	fn notify_assignments(&mut self, lits: &[RawLit]) {
		debug!(lits = ?lits.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "assignments");
		for &lit in lits {
			// Process Boolean assignment
			if self.state.trail.assign_lit(lit).is_some() {
				continue;
			}
			// Enqueue propagators, if no conflict has been found
			if !self.state.failed {
				self.state.enqueue_propagators(lit, None);
			}
		}
	}

	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		debug!(new_level, restart, "backtrack");
		// Revert value changes to previous decision level
		self.state.notify_backtrack::<false>(new_level, restart);
	}

	fn notify_new_decision_level(&mut self) {
		// Solver should not be in a failed state (no propagator conflict should
		// exist), and any conflict should have been communicated to the SAT oracle.
		debug_assert!(!self.state.failed);
		debug_assert!(self.state.conflict.is_none());
		// All propagation should have been communicated to the SAT oracle.
		debug_assert!(self.state.propagation_queue.is_empty());
		// Note that `self.state.clauses` may not be empty becuase [`Self::decide`]
		// might have introduced a new literal, which would in turn add its defining
		// clauses to `self.state.clauses`.

		trace!("new decision level");
		self.state.notify_new_decision_level();
	}

	#[tracing::instrument(level = "debug", skip(self, slv), fields(level = self.state.decision_level()))]
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Vec<RawLit> {
		// Check whether there are previous clauses to be communicated
		if !self.state.clauses.is_empty() {
			return Vec::new();
		}
		if self.state.propagation_queue.is_empty() && self.state.conflict.is_none() {
			// If there are no previous changes, run propagators
			SolvingContext::new(slv, &mut self.state).run_propagators(&mut self.propagators);
		}
		// Check whether there are new clauses that need to be communicated first
		if !self.state.clauses.is_empty() {
			return Vec::new();
		}
		let queue = mem::take(&mut self.state.propagation_queue);
		if queue.is_empty() {
			return Vec::new(); // Early return to avoid tracing statements
		}
		debug!(
			lits = ?queue
				.iter()
				.map(|&x| i32::from(x))
				.collect::<Vec<i32>>(),
			"propagate"
		);
		// Debug helper to ensure that any reason is based on known true literals
		#[cfg(debug_assertions)]
		{
			let mut prev = None;
			for &lit in queue.iter() {
				// Notify of the assignment of the previous literal so it is available
				// when checking the reason.
				if let Some(prev) = prev {
					self.notify_assignments(&[prev]);
				}
				if let Some(reason) = self.state.reason_map.get(&lit).cloned() {
					let clause: Clause =
						reason.explain(&mut self.propagators, &mut self.state, Some(lit));
					for &l in &clause {
						if l == lit {
							continue;
						}
						let val = self.state.trail.get_sat_value(!l);
						if !val.unwrap_or(false) {
							tracing::error!(lit_prop = i32::from(lit), lit_reason= i32::from(!l), reason_val = ?val, "invalid reason");
						}
						debug_assert!(
							val.unwrap_or(false),
							"Literal {} in Reason for {} is {:?}, but should be known true",
							!l,
							lit,
							val
						);
					}
				}
				prev = Some(lit);
			}
		}
		queue
	}
	fn reason_persistence(&self) -> ClausePersistence {
		ClausePersistence::Forgettable
	}
}

impl SearchStatistics {
	/// Returns the number of conflicts encountered during the search.
	pub fn conflicts(&self) -> u64 {
		self.conflicts
	}
	/// Return the number of search decisions that was left to the oracle solver.
	pub fn oracle_decisions(&self) -> u64 {
		self.oracle_decisions
	}
	/// Returns the peak depth of the search tree.
	pub fn peak_depth(&self) -> u32 {
		self.peak_depth
	}
	/// Returns the number of propagations performed by the constraint programming
	/// engine during the search.
	pub fn propagations(&self) -> u64 {
		self.propagations
	}
	/// Returns the number of times the search was restarted by the oracle solver.
	pub fn restarts(&self) -> u32 {
		self.restarts
	}
	/// Returns the number of search decisions that followed the user specified
	/// search heuristic.
	pub fn user_decisions(&self) -> u64 {
		self.user_decisions
	}
}

impl State {
	/// Returns the current decision level of the solver.
	fn decision_level(&self) -> u32 {
		self.trail.decision_level()
	}
	/// Determine whether assigning a literal triggers an event on an integer variable.
	///
	/// Returns `None` if the literal does not trigger an event on an integer
	/// variable. Otherwise, returns the relevant `IntVarRef` and the `IntEvent`
	/// that is triggered.
	fn determine_int_event(&mut self, lit: RawLit) -> Option<(IntVarRef, IntEvent)> {
		if let Some((iv, meaning)) = self.bool_to_int.get(lit.var()) {
			let (lb, ub) = self.int_vars[iv].get_bounds(self);
			let meaning = meaning
				.map(|l| if lit.is_negated() { !l } else { l })
				.unwrap_or_else(|| self.int_vars[iv].lit_meaning(lit));
			// Enact domain changes and determine change event
			let event: IntEvent = match meaning {
				IntLitMeaning::Eq(i) => {
					if i == lb || i == ub {
						return None;
					}
					if i < lb || i > ub {
						// Notified of invalid assignment, do nothing.
						//
						// Although we do not expect this to happen, it seems that Cadical
						// chronological backtracking might send notifications before
						// additional propagation.
						trace!(lit = i32::from(lit), lb, ub, "invalid eq notification");
						return None;
					}
					let prev_lb = self.int_vars[iv].notify_lower_bound(&mut self.trail, i);
					let prev_ub = self.int_vars[iv].notify_upper_bound(&mut self.trail, i);
					debug_assert!(prev_lb < i || prev_ub > i);
					debug_assert_eq!(self.get_int_val(IntView(IntViewInner::VarRef(iv))), Some(i));
					IntEvent::Fixed
				}
				IntLitMeaning::NotEq(i) => {
					if i < lb || i > ub {
						return None;
					}
					IntEvent::Domain
				}
				IntLitMeaning::GreaterEq(new_lb) => {
					if new_lb <= lb {
						return None;
					}
					let prev = self.int_vars[iv].notify_lower_bound(&mut self.trail, new_lb);
					debug_assert!(prev < new_lb);
					if new_lb == ub {
						IntEvent::Fixed
					} else {
						IntEvent::LowerBound
					}
				}
				IntLitMeaning::Less(i) => {
					let new_ub = self.int_vars[iv].tighten_upper_bound(i - 1);
					if new_ub >= ub {
						return None;
					}
					let prev = self.int_vars[iv].notify_upper_bound(&mut self.trail, new_ub);
					debug_assert!(new_ub < prev);
					if new_ub == lb {
						IntEvent::Fixed
					} else {
						IntEvent::UpperBound
					}
				}
			};
			Some((iv, event))
		} else {
			None
		}
	}

	/// Enqueue all propagators that are activated because the [`IntEvent`]
	/// `event` has happened to `int_var`.
	fn enqueue_int_propagators(
		&mut self,
		int_var: IntVarRef,
		event: IntEvent,
		skip: Option<PropRef>,
	) {
		for prop in self.int_activation[int_var].activated_by(event) {
			if Some(prop) != skip && !self.enqueued[prop] {
				self.propagator_queue
					.insert(self.propagator_priority[prop], prop);
				self.enqueued[prop] = true;
			}
		}
	}

	/// Enqueue all propagators that are activated because `lit` has been
	/// assigned.
	fn enqueue_propagators(&mut self, lit: RawLit, skip: Option<PropRef>) {
		for &prop in self.bool_activation.get(&lit.var()).into_iter().flatten() {
			if Some(prop) != skip && !self.enqueued[prop] {
				self.propagator_queue
					.insert(self.propagator_priority[prop], prop);
				self.enqueued[prop] = true;
			}
		}

		// Process Integer consequences
		if let Some((iv, event)) = self.determine_int_event(lit) {
			self.enqueue_int_propagators(iv, event, skip);
		}
	}

	/// Internal method called to process the backtracking to an earlier decision
	/// level.
	///
	/// The generic artugment `ARTIFICIAL` is used to signal when the solver is
	/// backtracking from an artificial decision level. An example of the use of
	/// artificial decision levels is found in the [`Engine::check_model`] method,
	/// where it is used to artificially fix any integer variables using lazy
	/// encodings.
	fn notify_backtrack<const ARTIFICIAL: bool>(&mut self, level: usize, restart: bool) {
		debug_assert!(!ARTIFICIAL || level as u32 == self.trail.decision_level() - 1);
		debug_assert!(!ARTIFICIAL || !restart);
		// Resolve the conflict status
		self.failed = false;
		self.conflict = None;
		// Remove (now invalid) propagations (but leave clauses in place)
		self.propagation_queue.clear();
		// Backtrack trail
		self.trail.notify_backtrack(level);
		// Empty propagation queue
		while let Some(p) = self.propagator_queue.pop() {
			self.enqueued[p] = false;
		}
		if ARTIFICIAL {
			return;
		}

		// Update conflict statistics
		self.statistics.conflicts += 1;

		// Switch to VSIDS if the number of conflicts exceeds the threshold
		if let Some(conflicts) = self.config.vsids_after {
			if !self.config.vsids_only
				&& !self.config.toggle_vsids
				&& self.statistics.conflicts > conflicts as u64
			{
				debug_assert!(!self.vsids);
				self.vsids = true;
				debug!(
					vsids = self.vsids,
					conflicts = self.statistics.conflicts,
					"enable vsids after N conflicts"
				);
			}
		}

		if restart {
			// Update restart statistics
			self.statistics.restarts += 1;
			if self.config.toggle_vsids && !self.config.vsids_only {
				self.vsids = !self.vsids;
				debug!(
					vsids = self.vsids,
					restart = self.statistics.restarts,
					"toggling vsids"
				);
			}
			if level == 0 {
				// Memory cleanup (Reasons are known to no longer be relevant)
				self.reason_map.clear();
			}
		}
	}

	/// Internal method called to trigger a new decision level.
	fn notify_new_decision_level(&mut self) {
		self.trail.notify_new_decision_level();

		// Update peak decision level
		let new_level = self.decision_level();
		if new_level > self.statistics.peak_depth {
			self.statistics.peak_depth = new_level;
		}
	}

	/// Register the [`Reason`] to explain why `lit` has been assigned.
	pub(crate) fn register_reason(&mut self, lit: RawLit, built_reason: Result<Reason, bool>) {
		match built_reason {
			Ok(reason) => {
				// Insert new reason, possibly overwriting old one (from previous search attempt)
				let _ = self.reason_map.insert(lit, reason);
			}
			Err(true) => {
				// No (previous) reason required
				let _ = self.reason_map.remove(&lit);
			}
			Err(false) => unreachable!("invalid reason"),
		}
	}

	/// Set whether the solver should toggle between VSIDS and a user defined
	/// search strategy after every restart.
	///
	/// Note that this setting is ignored if the solver is set to use VSIDS only.
	pub(crate) fn set_toggle_vsids(&mut self, enabled: bool) {
		self.config.toggle_vsids = enabled;
	}

	/// Set the number of conflicts after which the solver should switch to using
	/// VSIDS to make search decisions.
	pub(crate) fn set_vsids_after(&mut self, conflicts: Option<u32>) {
		self.config.vsids_after = conflicts;
	}

	/// Set wether the solver should make all search decisions based on the VSIDS
	/// only.
	pub(crate) fn set_vsids_only(&mut self, enable: bool) {
		self.config.vsids_only = enable;
		self.vsids = enable;
	}
}

impl ExplanationActions for State {
	fn get_int_lit_relaxed(
		&mut self,
		var: IntView,
		meaning: IntLitMeaning,
	) -> (BoolView, IntLitMeaning) {
		debug_assert!(
			matches!(meaning, IntLitMeaning::GreaterEq(_) | IntLitMeaning::Less(_)),
			"relaxed integer literals are only supported for LitMeaning::GreaterEq and LitMeaning::Less"
		);
		// Transform literal meaning if view is a linear transformation
		let meaning = match var.0 {
			IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } => {
				match transformer.rev_transform_lit(meaning.clone()) {
					Ok(m) => m,
					Err(v) => return (BoolView(BoolViewInner::Const(v)), meaning),
				}
			}
			_ => meaning,
		};

		// Get the (relaxed) boolean view representing the meaning and the actual (relaxed) meaning
		let (bv, meaning) = match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				let var = &mut self.int_vars[iv];
				match meaning {
					IntLitMeaning::GreaterEq(v) => {
						let (bv, v) = var.get_greater_eq_lit_or_weaker(&self.trail, v);
						(bv, IntLitMeaning::GreaterEq(v))
					}
					IntLitMeaning::Less(v) => {
						let (bv, v) = var.get_less_lit_or_weaker(&self.trail, v);
						(bv, IntLitMeaning::Less(v))
					}
					_ => unreachable!(),
				}
			}
			IntViewInner::Const(c) => (
				BoolView(BoolViewInner::Const(match meaning {
					IntLitMeaning::GreaterEq(i) => c >= i,
					IntLitMeaning::Less(i) => c < i,
					_ => unreachable!(),
				})),
				meaning,
			),
			IntViewInner::Bool { lit, .. } => {
				let (b_meaning, negated) =
					if matches!(meaning, IntLitMeaning::NotEq(_) | IntLitMeaning::Less(_)) {
						(!meaning.clone(), true)
					} else {
						(meaning.clone(), false)
					};
				let bv = BoolView(match b_meaning {
					IntLitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					_ => unreachable!(),
				});
				(if negated { !bv } else { bv }, meaning)
			}
		};

		// Transform the meaning back to fit the original view if it was linearly transformed
		let meaning = if let IntViewInner::Linear { transformer, .. }
		| IntViewInner::Bool { transformer, .. } = var.0
		{
			transformer.transform_lit(meaning)
		} else {
			meaning
		};
		(bv, meaning)
	}

	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView {
		match var.0 {
			IntViewInner::VarRef(var) => self.int_vars[var].get_lower_bound_lit(self),
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					self.int_vars[var].get_lower_bound_lit(self)
				} else {
					self.int_vars[var].get_upper_bound_lit(self)
				}
			}
			IntViewInner::Const(_) => BoolView(BoolViewInner::Const(true)),
			IntViewInner::Bool { lit, transformer } => BoolView(
				match (self.trail.get_sat_value(lit), transformer.positive_scale()) {
					(Some(true), true) => BoolViewInner::Lit(lit),
					(Some(false), false) => BoolViewInner::Lit(!lit),
					_ => BoolViewInner::Const(true),
				},
			),
		}
	}

	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView {
		match var.0 {
			IntViewInner::VarRef(var) => self.int_vars[var].get_upper_bound_lit(self),
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					self.int_vars[var].get_upper_bound_lit(self)
				} else {
					self.int_vars[var].get_lower_bound_lit(self)
				}
			}
			IntViewInner::Const(_) => BoolView(BoolViewInner::Const(true)),
			IntViewInner::Bool { lit, transformer } => BoolView(
				match (self.trail.get_sat_value(lit), transformer.positive_scale()) {
					(Some(false), true) => BoolViewInner::Lit(!lit),
					(Some(true), false) => BoolViewInner::Lit(lit),
					_ => BoolViewInner::Const(true),
				},
			),
		}
	}

	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		self.get_int_val(var).map(|v| {
			self.try_int_lit(var, IntLitMeaning::Eq(v))
				.expect("value literals cannot be created during explanation")
		})
	}
	fn try_int_lit(&self, var: IntView, mut meaning: IntLitMeaning) -> Option<BoolView> {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			match transformer.rev_transform_lit(meaning) {
				Ok(m) => meaning = m,
				Err(v) => return Some(BoolView(BoolViewInner::Const(v))),
			}
		}

		match var.0 {
			IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
				self.int_vars[var].get_bool_lit(meaning)
			}
			IntViewInner::Const(c) => Some(BoolView(BoolViewInner::Const(match meaning {
				IntLitMeaning::Eq(i) => c == i,
				IntLitMeaning::NotEq(i) => c != i,
				IntLitMeaning::GreaterEq(i) => c >= i,
				IntLitMeaning::Less(i) => c < i,
			}))),
			IntViewInner::Bool { lit, .. } => {
				let (meaning, negated) =
					if matches!(meaning, IntLitMeaning::NotEq(_) | IntLitMeaning::Less(_)) {
						(!meaning, true)
					} else {
						(meaning, false)
					};
				let bv = BoolView(match meaning {
					IntLitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
					IntLitMeaning::Eq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::Eq(_) => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					_ => unreachable!(),
				});
				Some(if negated { !bv } else { bv })
			}
		}
	}
}

impl InspectionActions for State {
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		let (lb, ub) = self.get_int_bounds(var);
		if lb <= val && val <= ub {
			let eq_lit = self.try_int_lit(var, IntLitMeaning::Eq(val));
			if let Some(eq_lit) = eq_lit {
				self.get_bool_val(eq_lit).unwrap_or(true)
			} else {
				true
			}
		} else {
			false
		}
	}
	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_vars[iv].get_bounds(self),
			IntViewInner::Const(i) => (i, i),
			IntViewInner::Linear { transformer, var } => {
				let (lb, ub) = self.int_vars[var].get_bounds(self);
				let lb = transformer.transform(lb);
				let ub = transformer.transform(ub);
				if lb <= ub {
					(lb, ub)
				} else {
					(ub, lb)
				}
			}
			IntViewInner::Bool { transformer, lit } => {
				let val = self.trail.get_sat_value(lit).map(Into::into);
				let lb = transformer.transform(val.unwrap_or(0));
				let ub = transformer.transform(val.unwrap_or(1));
				if lb <= ub {
					(lb, ub)
				} else {
					(ub, lb)
				}
			}
		}
	}
	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_vars[iv].get_lower_bound(self),
			IntViewInner::Const(i) => i,
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					let lb = self.int_vars[var].get_lower_bound(self);
					transformer.transform(lb)
				} else {
					let ub = self.int_vars[var].get_upper_bound(self);
					transformer.transform(ub)
				}
			}
			IntViewInner::Bool { transformer, lit } => {
				let val = self.trail.get_sat_value(lit).map(IntVal::from);
				let lb = val.unwrap_or(0);
				let ub = val.unwrap_or(1);
				if transformer.positive_scale() {
					transformer.transform(lb)
				} else {
					transformer.transform(ub)
				}
			}
		}
	}
	fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_vars[iv].get_upper_bound(self),
			IntViewInner::Const(i) => i,
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					let ub = self.int_vars[var].get_upper_bound(self);
					transformer.transform(ub)
				} else {
					let lb = self.int_vars[var].get_lower_bound(self);
					transformer.transform(lb)
				}
			}
			IntViewInner::Bool { transformer, lit } => {
				let val = self.trail.get_sat_value(lit).map(Into::into);
				let lb = val.unwrap_or(0);
				let ub = val.unwrap_or(1);
				if transformer.positive_scale() {
					transformer.transform(ub)
				} else {
					transformer.transform(lb)
				}
			}
		}
	}
}

impl TrailingActions for State {
	delegate! {
		to self.trail {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

index_vec::define_index_type! {
	/// Identifies an propagator in a [`Solver`]
	pub struct PropRef = u32;
}
