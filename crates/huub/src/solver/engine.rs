pub(crate) mod bool_to_int;
pub(crate) mod int_var;
pub(crate) mod propagation_context;
pub(crate) mod queue;
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
use tracing::trace;

use crate::{
	actions::{
		explanation::ExplanationActions, inspection::InspectionActions, trailing::TrailingActions,
	},
	propagator::{
		int_event::IntEvent,
		reason::{Reason, ReasonBuilder},
	},
	solver::{
		engine::{
			bool_to_int::BoolToIntMap,
			int_var::{IntVar, IntVarRef, LitMeaning, OrderStorage},
			propagation_context::PropagationContext,
			queue::{PriorityLevel, PriorityQueue},
			trail::{Trail, TrailedInt},
		},
		poster::BoxedPropagator,
		view::{BoolViewInner, IntViewInner},
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
	/// Internal State representation of the constraint programming engine
	pub(crate) state: State,
	/// Storage of literals that have been persistently propagated
	///
	/// These literals are repeatedly propagated when backtracking. If the engine
	/// backtracks to level zero, then the changes can be permanently applied, and
	/// the list can be cleared.
	persistent: Conjunction,
}

impl IpasirPropagator for Engine {
	fn notify_assignment(&mut self, lit: RawLit, persistent: bool) {
		trace!(lit = i32::from(lit), persistent, "assignment");
		// Process Boolean assignment
		if persistent && self.state.decision_level() != 0 {
			// Note that the assignment might already be known and trailed, but not previously marked as persistent
			self.persistent.push(lit);
			if self.state.trail.is_backtracking() {
				return;
			}
		}
		if self.state.trail.assign_sat(lit).is_some() {
			return;
		}

		// Enqueue propagators, if no conflict has been found
		if !self.state.conflict {
			self.state
				.enqueue_propagators(&mut self.propagators, lit, None);
		}
	}

	fn notify_new_decision_level(&mut self) {
		debug_assert!(!self.state.conflict);
		trace!("new decision level");
		self.state.notify_new_decision_level();
	}

	fn notify_backtrack(&mut self, new_level: usize) {
		trace!(new_level, "backtrack");

		// Revert value changes to previous decision level
		self.state.notify_backtrack(new_level);
		// Notify propagators to backtrack
		for p in &mut self.propagators {
			p.notify_backtrack(new_level);
		}

		// Re-apply persistent changes
		for lit in self.persistent.clone() {
			self.notify_assignment(lit, false);
		}
		if new_level == 0 {
			// Persistent changes are now permanently applied in the Trail
			self.persistent.clear()
		}
	}

	fn decide(&mut self) -> Option<RawLit> {
		None
	}

	#[tracing::instrument(level = "debug", skip(self, slv), fields(level = self.state.decision_level()))]
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Vec<RawLit> {
		// Helper function to handle returning a change
		let ret_change = |engine: &mut Self, change| {
			match change {
				ChangeType::Propagate(_) => {
					let ChangeType::Propagate(queue) = engine.state.changes.pop().unwrap() else {
						unreachable!()
					};
					trace!(
						lits = ?queue
							.iter()
							.map(|&x| i32::from(x))
							.collect::<Vec<i32>>(),
						"propagate"
					);
					for &lit in queue.iter() {
						engine
							.state
							.enqueue_propagators(&mut engine.propagators, lit, None);
					}
					// Debug helper to ensure that any reason is based on known true literals
					#[cfg(debug_assertions)]
					{
						for lit in queue.iter() {
							if let Some(reason) = engine.state.reason_map.get(lit).cloned() {
								let clause: Vec<_> =
									reason.to_clause(&mut engine.propagators, &mut engine.state);
								for l in &clause {
									let val = engine.state.trail.get_sat_value(!l);
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
						}
					}
					queue
				}
				// Clause must be added to the oracle, before further propagation
				ChangeType::AddClause(_) => Vec::new(),
			}
		};

		// Check whether there are previous changes to be communicated
		if let Some(change) = self.state.changes.peek_ty() {
			return ret_change(self, change);
		}
		debug_assert!(!self.state.conflict);
		// Otherwise run propagagors
		PropagationContext::new(slv, &mut self.state).run_propagators(&mut self.propagators);
		if let Some(change) = self.state.changes.peek_ty() {
			ret_change(self, change)
		} else {
			Vec::new()
		}
	}

	fn add_reason_clause(&mut self, propagated_lit: RawLit) -> Clause {
		// Find reason
		let reason = self.state.reason_map.remove(&propagated_lit);
		// Restore the current state to the state when the propagation happened if explaining lazily
		if matches!(reason, Some(Reason::Lazy(_, _))) {
			self.state.trail.undo_until_found_lit(propagated_lit)
		}
		// Create a clause from the reason
		let mut clause = reason.map_or_else(Vec::new, |r| {
			r.to_clause(&mut self.propagators, &mut self.state)
		});
		clause.push(propagated_lit);

		trace!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add reason clause");
		clause
	}

	#[tracing::instrument(level = "debug", skip(self, slv, model))]
	fn check_model(
		&mut self,
		slv: &mut dyn SolvingActions,
		model: &dyn pindakaas::Valuation,
	) -> bool {
		debug_assert!(!self.state.conflict);
		// If there is a known conflict, return false
		if self.state.conflict {
			debug_assert!(!self.state.changes.is_empty());
			let _ = self.state.ensure_clause_changes(&mut self.propagators);
			return false;
		}

		// Add temporary decision level
		let level = self.state.decision_level();
		self.notify_new_decision_level();

		// Create a propagation context
		let mut ctx = PropagationContext::new(slv, &mut self.state);

		// Calculate values of each integer and notify popgators
		for r in (0..ctx.state.int_vars.len()).map(IntVarRef::new) {
			let (lb, ub) = ctx.state.int_vars[r].get_bounds(&ctx.state.trail);
			if lb != ub {
				let val = ctx.state.int_vars[r].get_value(model);
				let prev_lb = ctx.state.int_vars[r].notify_lower_bound(&mut ctx.state.trail, val);
				// TODO: this two step approach could be unified
				if matches!(ctx.state.int_vars[r].order_encoding, OrderStorage::Lazy(_)) {
					// Ensure lazy literal exists
					let _ = ctx.get_intref_lit(r, LitMeaning::Less(val + 1));
				}
				let prev_ub = ctx.state.int_vars[r].notify_upper_bound(&mut ctx.state.trail, val);
				debug_assert!(prev_lb < val || prev_ub > val);

				ctx.state
					.enqueue_int_propagators(&mut self.propagators, r, IntEvent::Fixed, None);
			}
		}
		// Run propgagators to find any additional changes required
		ctx.run_propagators(&mut self.propagators);

		// Process propagation results
		// Accept model if no conflict is detected, and no propagation is performed (but allow creation of defining clauses)
		let mut accept = !self.state.conflict;
		accept &= !self.state.ensure_clause_changes(&mut self.propagators);

		// Revert to real decision level
		self.notify_backtrack(level);

		trace!(accept, "check model result");
		accept
	}

	fn add_external_clause(&mut self, _slv: &mut dyn SolvingActions) -> Option<Clause> {
		if let Some(ChangeType::AddClause(())) = self.state.changes.peek_ty() {
			let ChangeType::AddClause(clause) = self.state.changes.pop().unwrap() else {
				unreachable!()
			};
			trace!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add external clause");
			Some(clause)
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

impl Engine {}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct ChangeLog {
	ty: VecDeque<ChangeType<usize>>,
	lits: VecDeque<RawLit>,
}

impl ChangeLog {
	fn add_clause(&mut self, clause: impl IntoIterator<Item = RawLit>) {
		let len = self.lits.len();
		self.lits.extend(clause);
		let len = self.lits.len() - len;
		if len > 0 {
			self.ty.push_back(ChangeType::AddClause(len));
		}
	}

	fn clear_propagation(&mut self) {
		let ChangeLog { ty, lits } = self
			.filter(|e| !matches!(e, ChangeType::Propagate(_)))
			.collect();
		self.ty = ty;
		self.lits = lits;
		debug_assert_eq!(self.ty.is_empty(), self.lits.is_empty());
	}

	fn is_empty(&self) -> bool {
		debug_assert_eq!(self.ty.is_empty(), self.lits.is_empty());
		self.ty.is_empty()
	}

	fn peek_ty(&self) -> Option<ChangeType<()>> {
		self.ty.front().map(|ty| match ty {
			ChangeType::Propagate(_) => ChangeType::Propagate(()),
			ChangeType::AddClause(_) => ChangeType::AddClause(()),
		})
	}

	fn pop(&mut self) -> Option<ChangeType<Vec<RawLit>>> {
		let mut split_off = |n| {
			let mut lits = Vec::with_capacity(n);
			for _ in 0..n {
				lits.push(self.lits.pop_front().unwrap())
			}
			lits
		};
		self.ty.pop_front().map(|ty| match ty {
			ChangeType::Propagate(n) => ChangeType::Propagate(split_off(n)),
			ChangeType::AddClause(n) => ChangeType::AddClause(split_off(n)),
		})
	}

	fn propagate(&mut self, lit: RawLit) {
		self.lits.push_back(lit);
		if let Some(ChangeType::Propagate(n)) = self.ty.back_mut() {
			*n += 1
		} else {
			self.ty.push_back(ChangeType::Propagate(1))
		}
		debug_assert!(matches!(self.ty.back(), Some(ChangeType::Propagate(_))))
	}
}

impl Iterator for ChangeLog {
	type Item = ChangeType<Vec<RawLit>>;

	fn next(&mut self) -> Option<Self::Item> {
		self.pop()
	}
}

impl<I: IntoIterator<Item = RawLit>> FromIterator<ChangeType<I>> for ChangeLog {
	fn from_iter<T: IntoIterator<Item = ChangeType<I>>>(iter: T) -> Self {
		let mut log = Self::default();
		for ty in iter {
			match ty {
				ChangeType::Propagate(lits) => {
					let len = log.lits.len();
					log.lits.extend(lits);
					let added = log.lits.len() - len;
					if let Some(ChangeType::Propagate(n)) = log.ty.back_mut() {
						*n += added
					} else if added > 0 {
						log.ty.push_back(ChangeType::Propagate(added))
					}
					debug_assert!(matches!(log.ty.back(), Some(ChangeType::Propagate(_))))
				}
				ChangeType::AddClause(lits) => log.add_clause(lits),
			}
		}
		log
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ChangeType<T> {
	Propagate(T),
	AddClause(T),
}

index_vec::define_index_type! {
	/// Identifies an propagator in a [`Solver`]
	pub struct PropRef = u32;
}

#[derive(Clone, Debug, Default)]
pub(crate) struct State {
	// ---- Trailed Value Infrastructure (e.g., decision variables) ----
	/// Storage for the integer variables
	pub(crate) int_vars: IndexVec<IntVarRef, IntVar>,
	/// Mapping from boolean variables to integer variables
	pub(crate) bool_to_int: BoolToIntMap,
	/// Trailed Storage
	/// Includes lower and upper bounds for integer variables and Boolean variable assignments
	pub(crate) trail: Trail,
	/// Reasons for setting values
	pub(crate) reason_map: HashMap<RawLit, Reason>,
	/// Whether conflict has (already) been detected
	pub(crate) conflict: bool,

	// ---- Non-Trailed Infrastructure ----
	/// Storage for changes to be communicated to the solver
	pub(crate) changes: ChangeLog,

	// ---- Queueing Infrastructure ----
	/// Boolean variable subscriptions
	pub(crate) bool_subscribers: HashMap<RawVar, Vec<(PropRef, u32)>>,
	/// Integer variable subscriptions
	// TODO: Shrink Propref and IntEvent to fit in 32 bits
	pub(crate) int_subscribers: HashMap<IntVarRef, Vec<(PropRef, IntEvent, u32)>>,
	/// Queue of propagators awaiting action
	pub(crate) prop_queue: PriorityQueue<PropRef>,
	/// Priority within the queue for each propagator
	pub(crate) prop_priority: IndexVec<PropRef, PriorityLevel>,
	/// Flag for whether a propagator is enqueued
	pub(crate) enqueued: IndexVec<PropRef, bool>,
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
					if lb == i {
						let prev = self.int_vars[iv].notify_lower_bound(&mut self.trail, i + 1);
						debug_assert!(prev < (i + 1));
						if lb + 1 == ub {
							IntEvent::Fixed
						} else {
							IntEvent::LowerBound
						}
					} else if ub == i {
						let prev = self.int_vars[iv].notify_upper_bound(&mut self.trail, i - 1);
						debug_assert!((i - 1) < prev);
						if lb == ub - 1 {
							IntEvent::Fixed
						} else {
							IntEvent::UpperBound
						}
					} else {
						IntEvent::Domain
					}
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
					let new_ub = i - 1;
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

	fn decision_level(&self) -> usize {
		self.trail.decision_level()
	}

	pub(crate) fn enqueue_propagator(&mut self, prop: PropRef) {
		debug_assert!(!self.enqueued[prop]);
		self.prop_queue.insert(self.prop_priority[prop], prop);
	}

	// Helper method that ensures that all changes are communicated to the solver as clauses.
	//
	// The method returns whether any propagations were converted to clauses.
	#[inline]
	fn ensure_clause_changes(
		&mut self,
		propagators: &mut IndexVec<PropRef, BoxedPropagator>,
	) -> bool {
		let mut converted = false;
		let old = mem::take(&mut self.changes);
		self.changes = old
			.flat_map(|change| match change {
				ChangeType::Propagate(lits) => lits
					.into_iter()
					.map(|lit| {
						converted = true;
						let mut clause = self
							.reason_map
							.remove(&lit)
							.map_or_else(Vec::new, |r| r.to_clause(propagators, self));
						clause.push(lit);
						ChangeType::AddClause(clause)
					})
					.collect(),
				ChangeType::AddClause(_) => vec![change],
			})
			.collect();
		converted
	}

	fn notify_new_decision_level(&mut self) {
		self.trail.notify_new_decision_level();
	}

	fn notify_backtrack(&mut self, level: usize) {
		// Resolve the conflict status
		self.conflict = false;
		// Remove (now invalid) propagations (but leave clauses in place)
		self.changes.clear_propagation();
		// Backtrack trail
		self.trail.notify_backtrack(level);
		// Empty propagation queue
		while let Some(p) = self.prop_queue.pop() {
			self.enqueued[p] = false;
		}
		if level == 0 {
			// Memory cleanup (Reasons are known to no longer be relevant)
			self.reason_map.clear()
		}
	}

	fn enqueue_int_propagators(
		&mut self,
		propagators: &mut IndexVec<PropRef, BoxedPropagator>,
		int_var: IntVarRef,
		event: IntEvent,
		skip: Option<PropRef>,
	) {
		for (prop, level, data) in self.int_subscribers.get(&int_var).into_iter().flatten() {
			if Some(*prop) == skip || self.enqueued[*prop] || !level.is_activated_by(&event) {
				continue;
			}
			if propagators[*prop].notify_event(*data, &event, &mut self.trail) {
				self.prop_queue.insert(self.prop_priority[*prop], *prop);
			}
		}
	}

	fn enqueue_propagators(
		&mut self,
		propagators: &mut IndexVec<PropRef, BoxedPropagator>,
		lit: RawLit,
		skip: Option<PropRef>,
	) {
		for &(prop, data) in self.bool_subscribers.get(&lit.var()).into_iter().flatten() {
			if Some(prop) == skip || self.enqueued[prop] {
				continue;
			}
			if propagators[prop].notify_event(data, &IntEvent::Fixed, &mut self.trail) {
				self.prop_queue.insert(self.prop_priority[prop], prop);
			}
		}

		// Process Integer consequences
		if let Some((iv, event)) = self.determine_int_event(lit) {
			self.enqueue_int_propagators(propagators, iv, event, skip)
		}
	}

	fn register_reason(&mut self, lit: RawLit, builder: &ReasonBuilder, prop: PropRef) {
		match Reason::build_reason(builder, prop) {
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
}

impl TrailingActions for State {
	delegate! {
		to self.trail {
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

impl InspectionActions for State {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		match bv.0 {
			BoolViewInner::Lit(lit) => self.trail.get_sat_value(lit),
			BoolViewInner::Const(b) => Some(b),
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

impl ExplanationActions for State {
	fn try_int_lit(&self, var: IntView, mut meaning: LitMeaning) -> Option<BoolView> {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			if let Some(m) = transformer.rev_transform_lit(meaning) {
				meaning = m;
			} else {
				return Some(BoolView(BoolViewInner::Const(false)));
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

	fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView {
		self.int_vars[var]
			.get_bool_lit(meaning)
			.expect("literals part of explanations should have been created during propagation")
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
