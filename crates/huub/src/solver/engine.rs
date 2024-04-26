pub(crate) mod bool_to_int;
pub(crate) mod int_var;
pub(crate) mod queue;
pub(crate) mod trail;

use std::{any::Any, collections::HashMap, iter::once, num::NonZeroI32};

use index_vec::IndexVec;
use pindakaas::{
	solver::{Propagator as IpasirPropagator, SolvingActions},
	Lit as RawLit, Var as RawVar,
};
use tracing::trace;

use self::{
	bool_to_int::BoolToIntMap,
	int_var::IntVal,
	trail::{SatTrail, Trail},
};
use crate::{
	propagator::{
		int_event::IntEvent, propagation_action::PropagationActions, reason::Reason, Propagator,
	},
	solver::engine::{
		int_var::{IntVar, IntVarRef, LitMeaning},
		queue::PriorityQueue,
	},
};

#[derive(Default)]
pub struct Engine {
	/// Boolean variable subscriptions
	pub(crate) bool_subscribers: HashMap<RawVar, Vec<(PropRef, u32)>>,
	/// Integer variable subscriptions
	// TODO: Shrink Propref and IntEvent to fit in 32 bits
	pub(crate) int_subscribers: HashMap<IntVarRef, Vec<(PropRef, IntEvent, u32)>>,
	/// Mapping from boolean variables to integer variables
	pub(crate) bool_to_int: BoolToIntMap,

	/// Queue of propagators awaiting action
	pub(crate) prop_queue: PriorityQueue<PropRef>,

	pub(crate) reason_map: HashMap<RawLit, Reason>,

	/// Storage of the propagators
	pub(crate) propagators: IndexVec<PropRef, Box<dyn Propagator>>,
	/// Flag for whether a propagator is enqueued
	pub(crate) enqueued: IndexVec<PropRef, bool>,
	/// Storage for the integer variables
	pub(crate) int_vars: IndexVec<IntVarRef, IntVar>,
	/// Trailed integers
	/// Includes lower and upper bounds
	int_trail: Trail<TrailedInt, IntVal>,
	// Boolean trail
	bool_trail: SatTrail,

	external_queue: Vec<Vec<RawLit>>,
	persistent: Vec<(RawVar, bool)>,
}

impl IpasirPropagator for Engine {
	fn is_lazy(&self) -> bool {
		false
	}

	fn notify_assignment(&mut self, var: RawVar, val: bool, persistent: bool) {
		trace!(
			lit = {
				let v: NonZeroI32 = if val { var.into() } else { (!var).into() };
				v
			},
			persistent,
			"assignment"
		);

		// Process Boolean assignment
		if persistent && self.int_trail.decision_level() != 0 {
			self.persistent.push((var, val))
		}
		self.bool_trail.assign(var, val);
		for &(prop, data) in self.bool_subscribers.get(&var).into_iter().flatten() {
			if self.propagators[prop].notify_event(data) && !self.enqueued[prop] {
				let level = self.propagators[prop].queue_priority_level();
				self.prop_queue.insert(level, prop);
			}
		}

		// Process Integer consequences
		if let Some(iv) = self.bool_to_int.get(var) {
			let lb = self.int_trail[self.int_vars[iv].lower_bound];
			let ub = self.int_trail[self.int_vars[iv].upper_bound];
			// Enact domain changes and determine change e
			let lit = if val { var.into() } else { !var };
			let event: IntEvent = match self.int_vars[iv].lit_meaning(lit) {
				LitMeaning::Eq(i) => {
					if i == lb || i == ub {
						return;
					}
					self.int_trail.assign(self.int_vars[iv].lower_bound, i);
					self.int_trail.assign(self.int_vars[iv].upper_bound, i);
					IntEvent::Fixed
				}
				LitMeaning::NotEq(i) => {
					if i < lb || i > ub {
						return;
					}
					if lb == i {
						self.int_trail.assign(self.int_vars[iv].lower_bound, i + 1);
						if lb + 1 == ub {
							IntEvent::Fixed
						} else {
							IntEvent::LowerBound
						}
					} else if ub == i {
						self.int_trail.assign(self.int_vars[iv].upper_bound, i - 1);
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
						return;
					}
					self.int_trail.assign(self.int_vars[iv].lower_bound, new_lb);
					if new_lb == ub {
						IntEvent::Fixed
					} else {
						IntEvent::LowerBound
					}
				}
				LitMeaning::Less(i) => {
					let new_ub = i - 1;
					if new_ub >= ub {
						return;
					}
					self.int_trail.assign(self.int_vars[iv].upper_bound, new_ub);
					if new_ub == lb {
						IntEvent::Fixed
					} else {
						IntEvent::UpperBound
					}
				}
			};

			for (prop, level, data) in self.int_subscribers.get(&iv).into_iter().flatten() {
				if level.is_activated_by(&event)
					&& self.propagators[*prop].notify_event(*data)
					&& !self.enqueued[*prop]
				{
					let level = self.propagators[*prop].queue_priority_level();
					self.prop_queue.insert(level, *prop);
				}
			}
		}
	}

	fn notify_new_decision_level(&mut self) {
		trace!("new decision level");

		self.int_trail.notify_new_decision_level();
		self.bool_trail.notify_new_decision_level();
	}

	fn notify_backtrack(&mut self, new_level: usize) {
		trace!(new_level, "backtrack");

		// Revert changes to previous decision level
		self.int_trail.notify_backtrack(new_level);
		self.bool_trail.notify_backtrack(new_level);
		self.external_queue.clear();
		for p in &mut self.propagators {
			p.notify_backtrack(new_level);
		}
		// Re-apply persistent changes
		for (var, val) in self.persistent.clone() {
			self.notify_assignment(var, val, false);
		}
		if new_level == 0 {
			self.persistent.clear()
		}
	}

	fn decide(&mut self) -> Option<pindakaas::Lit> {
		None
	}

	#[tracing::instrument(level = "debug", skip(self, slv))]
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Vec<pindakaas::Lit> {
		let mut context = PropagationActions {
			prop: PropRef::new(0), // will be replaced
			lit_queue: Vec::new(),
			sat: slv,
			int_vars: &mut self.int_vars,
			reason_map: &mut self.reason_map,
			int_trail: &mut self.int_trail,
			sat_trail: &mut self.bool_trail,
		};
		while let Some(p) = self.prop_queue.pop() {
			self.enqueued[p] = false;
			let prop = self.propagators[p].as_mut();
			let _ = prop.propagate(&mut context);
			if !context.lit_queue.is_empty() {
				trace!(
					lits = ?context
						.lit_queue
						.iter()
						.map(|&x| i32::from(x))
						.collect::<Vec<i32>>(),
					"propagate"
				);
				break;
			}
		}
		context.lit_queue
	}

	fn add_reason_clause(&mut self, propagated_lit: pindakaas::Lit) -> Vec<pindakaas::Lit> {
		let reason = self
			.reason_map
			.get(&propagated_lit)
			.map(|r| match r {
				Reason::Lazy(prop, data) => {
					let reason = self.propagators[*prop].explain(*data);
					once(propagated_lit)
						.chain(reason.iter().map(|l| !l))
						.collect()
				}
				Reason::Eager(v) => once(propagated_lit).chain(v.iter().map(|l| !l)).collect(),
				Reason::Simple(l) => vec![propagated_lit, !l],
			})
			.unwrap_or_else(|| vec![propagated_lit]);
		trace!(clause = ?reason.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "give reason clause");
		reason
	}

	fn check_model(&mut self, sat_value: &dyn pindakaas::Valuation) -> bool {
		trace!("check model");
		for (r, iv) in self.int_vars.iter_mut().enumerate() {
			let r = IntVarRef::new(r);
			let lb = self.int_trail[iv.lower_bound];
			let ub = self.int_trail[iv.upper_bound];
			if lb != ub {
				let val = iv.get_value(sat_value);
				self.int_trail.assign(iv.lower_bound, val);
				self.int_trail.assign(iv.upper_bound, val);

				for (prop, level, data) in self.int_subscribers.get(&r).into_iter().flatten() {
					if level.is_activated_by(&IntEvent::Fixed)
						&& self.propagators[*prop].notify_event(*data)
					{
						let l = self.propagators[*prop].queue_priority_level();
						self.prop_queue.insert(l, *prop)
					}
				}
			}
		}
		struct NoOp {}
		impl SolvingActions for NoOp {
			fn new_var(&mut self) -> RawVar {
				todo!()
			}

			fn add_observed_var(&mut self, _var: RawVar) {
				todo!()
			}

			fn is_decision(&mut self, _lit: pindakaas::Lit) -> bool {
				todo!()
			}
		}
		let lits = self.propagate(&mut NoOp {});
		for lit in lits {
			let clause = self.add_reason_clause(lit);
			self.external_queue.push(clause);
		}
		self.external_queue.is_empty()
	}

	fn add_external_clause(&mut self) -> Option<Vec<pindakaas::Lit>> {
		self.external_queue.pop()
	}

	fn as_any(&self) -> &dyn Any {
		self
	}

	fn as_mut_any(&mut self) -> &mut dyn Any {
		self
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
