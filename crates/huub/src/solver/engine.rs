pub(crate) mod activation_list;
pub(crate) mod bool_to_int;
pub(crate) mod int_var;
pub(crate) mod queue;
pub(crate) mod solving_context;
pub(crate) mod trail;

use std::{
	any::Any,
	collections::{HashMap, VecDeque},
	mem,
};

use delegate::delegate;
use index_vec::IndexVec;
use pindakaas::{
	solver::{Propagator as IpasirPropagator, SolvingActions},
	Lit as RawLit, Var as RawVar,
};
use tracing::{debug, trace};

use crate::{
	actions::{
		decision::DecisionActions, explanation::ExplanationActions, inspection::InspectionActions,
		trailing::TrailingActions,
	},
	brancher::Decision,
	propagator::reason::Reason,
	solver::{
		engine::{
			activation_list::{ActivationList, IntEvent},
			bool_to_int::BoolToIntMap,
			int_var::{IntVar, IntVarRef, LitMeaning, OrderStorage},
			queue::{PriorityLevel, PriorityQueue},
			solving_context::SolvingContext,
			trail::{Trail, TrailedInt},
		},
		poster::{BoxedBrancher, BoxedPropagator},
		view::{BoolViewInner, IntViewInner},
		SolverConfiguration,
	},
	BoolView, Clause, Conjunction, IntVal, IntView,
};

macro_rules! trace_new_lit {
	($iv:expr, $def:expr, $lit:expr) => {
		tracing::debug!(
			lit = i32::from($lit),
			int_var = usize::from($iv),
			is_eq = matches!($def.meaning, LitMeaning::Eq(_)),
			val = match $def.meaning {
				LitMeaning::Eq(val) => val,
				LitMeaning::GreaterEq(val) => val,
				_ => unreachable!(),
			},
			"register new literal"
		);
		tracing::trace!(lit = i32::from($lit), "lazy literal")
	};
}
pub(crate) use trace_new_lit;

#[derive(Debug, Default, Clone)]
pub(crate) struct Engine {
	/// Storage of the propagators
	pub(crate) propagators: IndexVec<PropRef, BoxedPropagator>,
	/// Storage of the branchers
	pub(crate) branchers: Vec<BoxedBrancher>,
	/// Internal State representation of the constraint programming engine
	pub(crate) state: State,
	/// Storage of literals that have been persistently propagated
	///
	/// These literals are repeatedly propagated when backtracking. If the engine
	/// backtracks to level zero, then the changes can be permanently applied, and
	/// the list can be cleared.
	persistent: Conjunction,
}

index_vec::define_index_type! {
	/// Identifies an propagator in a [`Solver`]
	pub struct PropRef = u32;
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct SearchStatistics {
	// Number of conflicts encountered
	conflicts: u64,
	// Peak search depth
	peak_depth: u32,
	// Number of times a CP propagator was called
	propagations: u64,
	// Number of backtracks to level 0
	restarts: u32,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct State {
	// Solver confifguration
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

impl IpasirPropagator for Engine {
	fn notify_assignment(&mut self, lit: RawLit, persistent: bool) {
		trace!(lit = i32::from(lit), persistent, "assignment");
		// Process Boolean assignment
		if persistent && self.state.decision_level() != 0 {
			// Note that the assignment might already be known and trailed, but not previously marked as persistent
			self.persistent.push(lit);
			if self.state.trail.is_explaining() {
				return;
			}
		}
		if self.state.trail.assign_lit(lit).is_some() {
			return;
		}

		// Enqueue propagators, if no conflict has been found
		if self.state.conflict.is_none() {
			self.state.enqueue_propagators(lit, None);
		}
	}

	fn notify_new_decision_level(&mut self) {
		debug_assert!(self.state.conflict.is_none());
		trace!("new decision level");
		self.state.notify_new_decision_level();
	}

	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		debug!(new_level, restart, "backtrack");

		// Revert value changes to previous decision level
		self.state.notify_backtrack::<false>(new_level, restart);

		// Re-apply persistent changes
		for lit in self.persistent.clone() {
			self.notify_assignment(lit, false);
		}
		if new_level == 0 {
			// Persistent changes are now permanently applied in the Trail
			self.persistent.clear();
		}
	}

	fn decide(&mut self, slv: &mut dyn SolvingActions) -> Option<RawLit> {
		if !self.state.vsids {
			let mut current = self.state.trail.get_trailed_int(Trail::CURRENT_BRANCHER) as usize;
			if current == self.branchers.len() {
				return None;
			}
			let mut ctx = SolvingContext::new(slv, &mut self.state);
			while current < self.branchers.len() {
				match self.branchers[current].decide(&mut ctx) {
					Decision::Select(lit) => {
						debug!(lit = i32::from(lit), "decide");
						return Some(lit);
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
		None
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
			for lit in queue.iter() {
				// Notify of the assignment of the previous literal so it is available
				// when checking the reason.
				if let Some(prev) = prev {
					self.notify_assignment(prev, false);
				}
				if let Some(reason) = self.state.reason_map.get(lit).cloned() {
					let clause: Vec<_> = reason.to_clause(&mut self.propagators, &mut self.state);
					for l in &clause {
						let val = self.state.trail.get_sat_value(!l);
						if !val.unwrap_or(false) {
							tracing::error!(lit_prop = i32::from(*lit), lit_reason= i32::from(!l), reason_val = ?val, "invalid reason");
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
				prev = Some(*lit);
			}
		}
		queue
	}

	fn add_reason_clause(&mut self, propagated_lit: RawLit) -> Clause {
		// Find reason
		let reason = self.state.reason_map.remove(&propagated_lit);
		// Restore the current state to the state when the propagation happened if explaining lazily
		if matches!(reason, Some(Reason::Lazy(_, _))) {
			self.state.trail.goto_assign_lit(propagated_lit);
		}
		// Create a clause from the reason
		let mut clause = reason.map_or_else(Vec::new, |r| {
			r.to_clause(&mut self.propagators, &mut self.state)
		});
		clause.push(propagated_lit);

		debug!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add reason clause");
		clause
	}

	#[tracing::instrument(level = "debug", skip(self, slv, model))]
	fn check_model(
		&mut self,
		slv: &mut dyn SolvingActions,
		model: &dyn pindakaas::Valuation,
	) -> bool {
		debug_assert!(self.state.conflict.is_none());
		// If there is a known conflict, return false
		if !self.state.propagation_queue.is_empty() || self.state.conflict.is_some() {
			self.state.ensure_clause_changes(&mut self.propagators);
			debug!(accept = false, "check model");
			return false;
		}

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
				debug_assert_eq!(lb, ctx.state.int_vars[r].get_value(model));

				// Ensure the lazy literal for the upper bound exists
				let ub_lit = ctx.get_intref_lit(r, LitMeaning::Less(lb + 1));
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
		let accept = if let Some(conflict) = self.state.conflict.clone() {
			// Move conflict to clauses before backtrack
			self.state.clauses.push_back(conflict);
			false
		} else {
			true
		};

		// Revert to real decision level
		self.state.notify_backtrack::<true>(level as usize, false);

		debug!(accept, "check model");
		accept
	}

	fn add_external_clause(&mut self, _slv: &mut dyn SolvingActions) -> Option<Clause> {
		if !self.state.clauses.is_empty() {
			let clause = self.state.clauses.pop_front(); // Known to be `Some`
			trace!(clause = ?clause.as_ref().unwrap().iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add external clause");
			clause
		} else if !self.state.propagation_queue.is_empty() {
			None // Require that the solver first applies the remaining propagation
		} else if let Some(conflict) = self.state.conflict.clone() {
			debug!(clause = ?conflict.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add conflict clause");
			Some(conflict)
		} else {
			None
		}
	}

	fn as_any(&self) -> &dyn Any {
		self
	}
	fn as_mut_any(&mut self) -> &mut dyn Any {
		self
	}
}

impl SearchStatistics {
	pub fn conflicts(&self) -> u64 {
		self.conflicts
	}
	pub fn peak_depth(&self) -> u32 {
		self.peak_depth
	}
	pub fn propagations(&self) -> u64 {
		self.propagations
	}
	pub fn restarts(&self) -> u32 {
		self.restarts
	}
}

impl State {
	fn determine_int_event(&mut self, lit: RawLit) -> Option<(IntVarRef, IntEvent)> {
		if let Some((iv, meaning)) = self.bool_to_int.get(lit.var()) {
			let (lb, ub) = self.int_vars[iv].get_bounds(self);
			let meaning = meaning
				.map(|l| if lit.is_negated() { !l } else { l })
				.unwrap_or_else(|| self.int_vars[iv].lit_meaning(lit));
			// Enact domain changes and determine change event
			let event: IntEvent = match meaning {
				LitMeaning::Eq(i) => {
					if i == lb || i == ub {
						return None;
					}
					let prev_lb = self.int_vars[iv].notify_lower_bound(&mut self.trail, i);
					let prev_ub = self.int_vars[iv].notify_upper_bound(&mut self.trail, i);
					debug_assert!(prev_lb < i || prev_ub > i);
					debug_assert_eq!(self.get_int_val(IntView(IntViewInner::VarRef(iv))), Some(i));
					IntEvent::Fixed
				}
				LitMeaning::NotEq(i) => {
					if i < lb || i > ub {
						return None;
					}
					IntEvent::Domain
				}
				LitMeaning::GreaterEq(new_lb) => {
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
				LitMeaning::Less(i) => {
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

	fn decision_level(&self) -> u32 {
		self.trail.decision_level()
	}

	pub(crate) fn enqueue_propagator(&mut self, prop: PropRef) {
		debug_assert!(!self.enqueued[prop]);
		self.propagator_queue
			.insert(self.propagator_priority[prop], prop);
	}

	// Helper method that ensures that all changes are communicated to the solver as clauses.
	//
	// The method returns whether any propagations were converted to clauses.
	#[inline]
	fn ensure_clause_changes(&mut self, propagators: &mut IndexVec<PropRef, BoxedPropagator>) {
		let queue = mem::take(&mut self.propagation_queue);
		for lit in queue {
			let mut clause = self
				.reason_map
				.remove(&lit)
				.map_or_else(Vec::new, |r| r.to_clause(propagators, self));
			clause.push(lit);
			self.clauses.push_back(clause);
		}
	}

	fn notify_new_decision_level(&mut self) {
		self.trail.notify_new_decision_level();

		// Update peak decision level
		let new_level = self.decision_level();
		if new_level > self.statistics.peak_depth {
			self.statistics.peak_depth = new_level;
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
			}
		}
	}

	fn enqueue_propagators(&mut self, lit: RawLit, skip: Option<PropRef>) {
		for &prop in self.bool_activation.get(&lit.var()).into_iter().flatten() {
			if Some(prop) != skip && !self.enqueued[prop] {
				self.propagator_queue
					.insert(self.propagator_priority[prop], prop);
			}
		}

		// Process Integer consequences
		if let Some((iv, event)) = self.determine_int_event(lit) {
			self.enqueue_int_propagators(iv, event, skip);
		}
	}

	fn register_reason(&mut self, lit: RawLit, built_reason: Result<Reason, bool>) {
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

	pub(crate) fn set_vsids_after(&mut self, conflicts: Option<u32>) {
		self.config.vsids_after = conflicts;
	}

	pub(crate) fn set_toggle_vsids(&mut self, enabled: bool) {
		self.config.toggle_vsids = enabled;
	}

	pub(crate) fn set_vsids_only(&mut self, enable: bool) {
		self.config.vsids_only = enable;
		self.vsids = enable;
	}
}

impl ExplanationActions for State {
	fn try_int_lit(&self, var: IntView, mut meaning: LitMeaning) -> Option<BoolView> {
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
				LitMeaning::Eq(i) => c == i,
				LitMeaning::NotEq(i) => c != i,
				LitMeaning::GreaterEq(i) => c >= i,
				LitMeaning::Less(i) => c < i,
			}))),
			IntViewInner::Bool { lit, .. } => {
				let (meaning, negated) =
					if matches!(meaning, LitMeaning::NotEq(_) | LitMeaning::Less(_)) {
						(!meaning, true)
					} else {
						(meaning, false)
					};
				let bv = BoolView(match meaning {
					LitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
					LitMeaning::Eq(1) => BoolViewInner::Lit(lit),
					LitMeaning::Eq(_) => BoolViewInner::Const(false),
					LitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					LitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					LitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					_ => unreachable!(),
				});
				Some(if negated { !bv } else { bv })
			}
		}
	}

	fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning) {
		debug_assert!(
			matches!(meaning, LitMeaning::GreaterEq(_) | LitMeaning::Less(_)),
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
					LitMeaning::GreaterEq(v) => {
						let (bv, v) = var.get_greater_eq_lit_or_weaker(&self.trail, v);
						(bv, LitMeaning::GreaterEq(v))
					}
					LitMeaning::Less(v) => {
						let (bv, v) = var.get_less_lit_or_weaker(&self.trail, v);
						(bv, LitMeaning::Less(v))
					}
					_ => unreachable!(),
				}
			}
			IntViewInner::Const(c) => (
				BoolView(BoolViewInner::Const(match meaning {
					LitMeaning::GreaterEq(i) => c >= i,
					LitMeaning::Less(i) => c < i,
					_ => unreachable!(),
				})),
				meaning,
			),
			IntViewInner::Bool { lit, .. } => {
				let (b_meaning, negated) =
					if matches!(meaning, LitMeaning::NotEq(_) | LitMeaning::Less(_)) {
						(!meaning.clone(), true)
					} else {
						(meaning.clone(), false)
					};
				let bv = BoolView(match b_meaning {
					LitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					LitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					LitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
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

	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		self.get_int_val(var).map(|v| {
			self.try_int_lit(var, LitMeaning::Eq(v))
				.expect("value literals cannot be created during explanation")
		})
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
}

impl InspectionActions for State {
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
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		let (lb, ub) = self.get_int_bounds(var);
		if lb <= val && val <= ub {
			let eq_lit = self.try_int_lit(var, LitMeaning::Eq(val));
			if let Some(eq_lit) = eq_lit {
				self.get_bool_val(eq_lit).unwrap_or(true)
			} else {
				true
			}
		} else {
			false
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
