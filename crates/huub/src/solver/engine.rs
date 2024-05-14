pub(crate) mod bool_to_int;
pub(crate) mod int_var;
pub(crate) mod propagation_context;
pub(crate) mod queue;
pub(crate) mod trail;

use std::{any::Any, collections::HashMap};

use index_vec::IndexVec;
use pindakaas::{
	solver::{Propagator as IpasirPropagator, SolvingActions},
	Lit as RawLit, Var as RawVar,
};
use tracing::{debug, trace};

use self::{
	bool_to_int::BoolToIntMap,
	propagation_context::PropagationContext,
	trail::{SatTrail, Trail},
};
use super::view::{BoolViewInner, IntViewInner};
use crate::{
	propagator::{
		conflict::Conflict,
		int_event::IntEvent,
		reason::{Reason, ReasonBuilder},
		ExplainActions, Propagator,
	},
	solver::engine::{
		int_var::{IntVar, IntVarRef, LitMeaning},
		queue::PriorityQueue,
		trail::HasChanged,
	},
	BoolView, Clause, Conjunction, IntVal, IntView,
};

#[derive(Default, Clone)]
pub(crate) struct Engine {
	/// Storage of the propagators
	pub(crate) propagators: IndexVec<PropRef, Box<dyn Propagator>>,
	/// Internal State representation of the constraint programming engine
	pub(crate) state: State,

	/// Temporary storage of literals that have been persistently propagated
	persistent: Conjunction,
	/// Temporary storage of a conflict clause that was detected during propagation
	conflict_clauses: Vec<Clause>,
}

impl IpasirPropagator for Engine {
	fn notify_assignment(&mut self, lit: RawLit, persistent: bool) {
		if self.state.notify_sat_assignment(lit) == HasChanged::NoChange {
			return;
		}
		trace!(lit = i32::from(lit), persistent, "assignment");

		// Process Boolean assignment
		if persistent && self.state.decision_level() != 0 {
			self.persistent.push(lit)
		}
		for &(prop, data) in self
			.state
			.bool_subscribers
			.get(&lit.var())
			.into_iter()
			.flatten()
		{
			if self.propagators[prop].notify_event(data, &IntEvent::Fixed)
				&& !self.state.enqueued[prop]
			{
				let level = self.propagators[prop].queue_priority_level();
				self.state.prop_queue.insert(level, prop);
			}
		}

		// Process Integer consequences
		if let Some((iv, event)) = self.state.determine_int_event(lit) {
			for (prop, level, data) in self.state.int_subscribers.get(&iv).into_iter().flatten() {
				if level.is_activated_by(&event)
					&& self.propagators[*prop].notify_event(*data, &event)
					&& !self.state.enqueued[*prop]
				{
					let level = self.propagators[*prop].queue_priority_level();
					self.state.prop_queue.insert(level, *prop);
				}
			}
		}
	}

	fn notify_new_decision_level(&mut self) {
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
		// Clear the conflict reasons
		self.conflict_clauses.clear();

		// Re-apply persistent changes
		for lit in self.persistent.clone() {
			self.notify_assignment(lit, false);
		}
		if new_level == 0 {
			self.persistent.clear()
		}
	}

	fn decide(&mut self) -> Option<pindakaas::Lit> {
		None
	}

	#[tracing::instrument(level = "debug", skip(self, _slv))]
	fn propagate(&mut self, _slv: &mut dyn SolvingActions) -> Vec<pindakaas::Lit> {
		if self.has_conflict() {
			return Vec::new();
		}
		while let Some(p) = self.state.prop_queue.pop() {
			self.state.enqueued[p] = false;
			let prop = self.propagators[p].as_mut();
			let mut ctx = PropagationContext {
				prop: p,
				state: &mut self.state,
				prop_queue: Vec::new(),
			};
			if let Err(Conflict { reason }) = prop.propagate(&mut ctx) {
				trace!(lits = ?reason, "conflict detected");
				self.conflict_clauses
					.push(reason.to_clause(&mut self.propagators, &mut self.state));
				return Vec::new();
			} else if !ctx.prop_queue.is_empty() {
				trace!(
					lits = ?ctx
						.prop_queue
						.iter()
						.map(|&x| i32::from(x))
						.collect::<Vec<i32>>(),
					"propagate"
				);
				return ctx.prop_queue;
			}
		}
		Vec::new()
	}

	fn add_reason_clause(&mut self, propagated_lit: pindakaas::Lit) -> Clause {
		let mut clause = self
			.state
			.reason_map
			.remove(&propagated_lit)
			.map_or_else(Vec::new, |r| {
				r.to_clause(&mut self.propagators, &mut self.state)
			});
		clause.push(propagated_lit);
		trace!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "give reason clause");
		clause
	}

	#[tracing::instrument(level = "debug", skip(self, slv, model))]
	fn check_model(
		&mut self,
		slv: &mut dyn SolvingActions,
		model: &dyn pindakaas::Valuation,
	) -> bool {
		if self.has_conflict() {
			trace!("check model failed: existing conflict");
			return false;
		}
		for (r, iv) in self.state.int_vars.iter_mut().enumerate() {
			let r = IntVarRef::new(r);
			let lb = self.state.int_trail[iv.lower_bound];
			let ub = self.state.int_trail[iv.upper_bound];
			if lb != ub {
				let val = iv.get_value(model);
				let change_lb = self.state.int_trail.assign(iv.lower_bound, val);
				let change_ub = self.state.int_trail.assign(iv.upper_bound, val);
				debug_assert!(change_lb == HasChanged::Changed || change_ub == HasChanged::Changed);

				for (prop, level, data) in self.state.int_subscribers.get(&r).into_iter().flatten()
				{
					if level.is_activated_by(&IntEvent::Fixed)
						&& self.propagators[*prop].notify_event(*data, &IntEvent::Fixed)
					{
						let l = self.propagators[*prop].queue_priority_level();
						self.state.prop_queue.insert(l, *prop)
					}
				}
			}
		}
		let lits = self.propagate(slv);
		// If any additional literal were propagated, then conjoin then with their
		// reasons into conflict clauses to check with the oracle
		for lit in lits {
			let mut clause = self
				.state
				.reason_map
				.remove(&lit)
				.map_or_else(Vec::new, |r| {
					r.to_clause(&mut self.propagators, &mut self.state)
				});
			clause.push(lit);
			self.conflict_clauses.push(clause)
		}
		trace!(correct = !self.has_conflict(), "check model result");
		!self.has_conflict()
	}

	fn add_external_clause(&mut self, _slv: &mut dyn SolvingActions) -> Option<Clause> {
		if let Some(clause) = self.conflict_clauses.pop() {
			debug!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "declare conflict");
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

impl Engine {
	fn has_conflict(&self) -> bool {
		!self.conflict_clauses.is_empty()
	}
}

index_vec::define_index_type! {
	/// Identifies an propagator in a [`Solver`]
	pub struct PropRef = u32;
}

index_vec::define_index_type! {
	/// Identifies an trailed integer tracked within [`Solver`]
	pub struct TrailedInt = u32;
}

#[derive(Clone, Debug, Default)]
pub(crate) struct State {
	// ---- Trailed Value Infrastructure (e.g., decision variables) ----
	/// Storage for the integer variables
	pub(crate) int_vars: IndexVec<IntVarRef, IntVar>,
	/// Mapping from boolean variables to integer variables
	pub(crate) bool_to_int: BoolToIntMap,
	/// Trailed integers
	/// Includes lower and upper bounds
	int_trail: Trail<TrailedInt, IntVal>,
	/// Boolean trail
	sat_trail: SatTrail,
	/// Reasons for setting values
	pub(crate) reason_map: HashMap<RawLit, Reason>,

	// ---- Queueing Infrastructure ----
	/// Boolean variable subscriptions
	pub(crate) bool_subscribers: HashMap<RawVar, Vec<(PropRef, u32)>>,
	/// Integer variable subscriptions
	// TODO: Shrink Propref and IntEvent to fit in 32 bits
	pub(crate) int_subscribers: HashMap<IntVarRef, Vec<(PropRef, IntEvent, u32)>>,
	/// Queue of propagators awaiting action
	pub(crate) prop_queue: PriorityQueue<PropRef>,
	/// Flag for whether a propagator is enqueued
	pub(crate) enqueued: IndexVec<PropRef, bool>,
}

impl State {
	fn notify_sat_assignment(&mut self, lit: RawLit) -> HasChanged {
		self.sat_trail.assign(lit.var(), !lit.is_negated())
	}

	fn determine_int_event(&mut self, lit: RawLit) -> Option<(IntVarRef, IntEvent)> {
		if let Some(iv) = self.bool_to_int.get(lit.var()) {
			let lb = self.int_trail[self.int_vars[iv].lower_bound];
			let ub = self.int_trail[self.int_vars[iv].upper_bound];
			// Enact domain changes and determine change event
			let event: IntEvent = match self.int_vars[iv].lit_meaning(lit) {
				LitMeaning::Eq(i) => {
					if i == lb || i == ub {
						return None;
					}
					let change_lb = self.int_trail.assign(self.int_vars[iv].lower_bound, i);
					let change_ub = self.int_trail.assign(self.int_vars[iv].upper_bound, i);
					debug_assert!(
						change_lb == HasChanged::Changed || change_ub == HasChanged::Changed
					);
					IntEvent::Fixed
				}
				LitMeaning::NotEq(i) => {
					if i < lb || i > ub {
						return None;
					}
					if lb == i {
						let change = self.int_trail.assign(self.int_vars[iv].lower_bound, i + 1);
						debug_assert_eq!(change, HasChanged::Changed);
						if lb + 1 == ub {
							IntEvent::Fixed
						} else {
							IntEvent::LowerBound
						}
					} else if ub == i {
						let change = self.int_trail.assign(self.int_vars[iv].upper_bound, i - 1);
						debug_assert_eq!(change, HasChanged::Changed);
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
					let change = self.int_trail.assign(self.int_vars[iv].lower_bound, new_lb);
					debug_assert_eq!(change, HasChanged::Changed);
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
					let change = self.int_trail.assign(self.int_vars[iv].upper_bound, new_ub);
					debug_assert_eq!(change, HasChanged::Changed);
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
		debug_assert_eq!(
			self.sat_trail.decision_level(),
			self.int_trail.decision_level()
		);

		self.sat_trail.decision_level()
	}

	fn notify_new_decision_level(&mut self) {
		self.int_trail.notify_new_decision_level();
		self.sat_trail.notify_new_decision_level();
	}

	fn notify_backtrack(&mut self, level: usize) {
		self.int_trail.notify_backtrack(level);
		self.sat_trail.notify_backtrack(level);
	}

	fn register_reason(&mut self, lit: RawLit, builder: &ReasonBuilder, prop: PropRef) {
		match Reason::build_reason(builder, prop) {
			Ok(reason) => {
				let _ = self.reason_map.insert(lit, reason);
			}
			Err(true) => (),
			Err(false) => unreachable!("invalid reason"),
		}
	}
}

impl ExplainActions for State {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		match bv.0 {
			BoolViewInner::Lit(lit) => self.sat_trail.get(lit),
			BoolViewInner::Const(b) => Some(b),
		}
	}

	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_trail[self.int_vars[iv].lower_bound],
			IntViewInner::Const(i) => i,
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					let lb = self.int_trail[self.int_vars[var].lower_bound];
					transformer.transform(lb)
				} else {
					let ub = self.int_trail[self.int_vars[var].upper_bound];
					transformer.transform(ub)
				}
			}
			IntViewInner::Bool { transformer, lit } => {
				let val = self.sat_trail.get(lit).map(Into::into);
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
			IntViewInner::VarRef(iv) => self.int_trail[self.int_vars[iv].upper_bound],
			IntViewInner::Const(i) => i,
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					let ub = self.int_trail[self.int_vars[var].upper_bound];
					transformer.transform(ub)
				} else {
					let lb = self.int_trail[self.int_vars[var].lower_bound];
					transformer.transform(lb)
				}
			}
			IntViewInner::Bool { transformer, lit } => {
				let val = self.sat_trail.get(lit).map(Into::into);
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

	fn get_int_lit(&self, var: IntView, mut meaning: LitMeaning) -> BoolView {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			if let Some(m) = transformer.rev_transform_lit(meaning) {
				meaning = m;
			} else {
				return BoolView(BoolViewInner::Const(false));
			}
		}

		match var.0 {
			IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
				self.int_vars[var].get_bool_lit(meaning)
			}
			IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match meaning {
				LitMeaning::Eq(i) => c == i,
				LitMeaning::NotEq(i) => c != i,
				LitMeaning::GreaterEq(i) => c >= i,
				LitMeaning::Less(i) => c < i,
			})),
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
				if negated {
					!bv
				} else {
					bv
				}
			}
		}
	}
}
