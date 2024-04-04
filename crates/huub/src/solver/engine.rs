pub(crate) mod int_var;
pub(crate) mod queue;

use std::{any::Any, collections::HashMap, iter::once, mem, num::NonZeroI32};

use flatzinc_serde::RangeList;
use index_vec::IndexVec;
use pindakaas::{
	solver::{Propagator as IpasirPropagator, SolvingActions},
	Lit as RawLit, Var as RawVar,
};
use tracing::trace;

use crate::{
	propagator::{
		int_event::IntEvent, propagation_action::PropagationActions, reason::Reason, Propagator,
	},
	solver::engine::{
		int_var::{BoolVarMap, IntVar, IntVarRef},
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
	// TODO: (URGENT) this is incredibly inefficient. Maybe use a BTreeMap over the ranges?
	pub(crate) bool_to_int: HashMap<RawVar, IntVarRef>,

	/// Queue of propagators awaiting action
	prop_queue: PriorityQueue<PropRef>,

	pub(crate) reason_map: HashMap<RawLit, Reason>,

	/// Storage for the propagators used by the
	pub(crate) propagators: IndexVec<PropRef, Box<dyn Propagator>>,
	/// Storage for the integer variables
	pub(crate) int_vars: IndexVec<IntVarRef, IntVar>,
	/// Domain trail
	// TODO: Inefficient, optimise!
	int_domain_trail: Vec<(IntVarRef, RangeList<i64>)>,
	trail_level: Vec<usize>,

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
		if persistent {
			self.persistent.push((var, val))
		}
		for (prop, data) in self.bool_subscribers.get(&var).into_iter().flatten() {
			if let Some(l) = self.propagators[*prop].notify_event(*data) {
				self.prop_queue.insert(l, *prop);
			}
		}
		if let Some(iv) = self.bool_to_int.get(&var) {
			// Enact domain changes and determine change e
			let event = match self.int_vars[*iv].map_bool_var(var) {
				BoolVarMap::Eq(i) => {
					let range_without = |rl: &RangeList<i64>, i| {
						rl.into_iter()
							.flat_map(|r| {
								if r.contains(&&i) {
									vec![**r.start()..=(i - 1), (i + 1)..=**r.end()]
								} else {
									vec![**r.start()..=**r.end()]
								}
							})
							.collect()
					};
					if val {
						let old_dom =
							mem::replace(&mut self.int_vars[*iv].domain, RangeList::from(i..=i));
						self.int_domain_trail.push((*iv, old_dom));
						IntEvent::Fixed
					} else {
						let lb = *self.int_vars[*iv].domain.lower_bound().unwrap();
						let ub = *self.int_vars[*iv].domain.upper_bound().unwrap();
						let new_dom: RangeList<i64> = range_without(&self.int_vars[*iv].domain, i);
						let singular = new_dom.lower_bound() == new_dom.upper_bound();
						let old_dom = mem::replace(&mut self.int_vars[*iv].domain, new_dom);
						self.int_domain_trail.push((*iv, old_dom));
						if singular {
							IntEvent::Fixed
						} else if i == lb {
							IntEvent::LowerBound
						} else if i == ub {
							IntEvent::UpperBound
						} else {
							IntEvent::Domain
						}
					}
				}
			};

			for (prop, level, data) in self.int_subscribers.get(iv).into_iter().flatten() {
				if level.is_activated_by(&event) {
					if let Some(l) = self.propagators[*prop].notify_event(*data) {
						self.prop_queue.insert(l, *prop)
					}
				}
			}
		}
	}

	fn notify_new_decision_level(&mut self) {
		trace!("new decision level");
		self.trail_level.push(self.int_domain_trail.len())
	}

	fn notify_backtrack(&mut self, new_level: usize) {
		trace!(new_level, "backtrack");
		// Determine size of reverted trail
		let dom_trail_size = if new_level > 0 {
			self.trail_level[new_level - 1]
		} else {
			0
		};
		// Revert changes to previous decision level
		for (var, dom) in self.int_domain_trail.drain(dom_trail_size..).rev() {
			self.int_vars[var].domain = dom;
		}
		self.external_queue.clear();
		for p in &mut self.propagators {
			p.notify_backtrack(new_level);
		}
		// Re-apply persistent changes
		for (var, val) in self.persistent.clone() {
			self.notify_assignment(var, val, false);
		}
		self.persistent.clear()
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
		};
		while let Some(p) = self.prop_queue.pop() {
			let prop = self.propagators[p].as_mut();
			if prop.propagate(&mut context).is_err() {
				break;
			}
		}
		context.lit_queue
	}

	fn add_reason_clause(&mut self, propagated_lit: pindakaas::Lit) -> Vec<pindakaas::Lit> {
		let reason = match &self.reason_map[&propagated_lit] {
			Reason::Lazy(prop, data) => {
				let reason = self.propagators[*prop].explain(*data);
				once(propagated_lit)
					.chain(reason.iter().map(|l| !l))
					.collect()
			}
			Reason::Eager(v) => once(propagated_lit).chain(v.iter().map(|l| !l)).collect(),
			Reason::Simple(l) => vec![propagated_lit, !l],
		};
		trace!(clause = ?reason.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "give reason clause");
		reason
	}

	fn check_model(&mut self, sat_value: &dyn pindakaas::Valuation) -> bool {
		let value = &|iv: &IntVar| {
			for (i, l) in iv.one_hot.clone().enumerate() {
				if sat_value(l.into()) == Some(true) {
					// TODO: Does not account for holes
					return iv.orig_domain.lower_bound().unwrap() + i as i64;
				}
			}
			unreachable!()
		};

		for (r, iv) in self.int_vars.iter_mut().enumerate() {
			let lb = iv.domain.lower_bound().unwrap();
			let ub = iv.domain.upper_bound().unwrap();
			if lb != ub {
				let r = IntVarRef::new(r);
				let val = value(iv);
				let old_dom = mem::replace(&mut iv.domain, RangeList::from(val..=val));
				self.int_domain_trail.push((r, old_dom));

				for (prop, level, data) in self.int_subscribers.get(&r).into_iter().flatten() {
					if level.is_activated_by(&IntEvent::Fixed) {
						if let Some(l) = self.propagators[*prop].notify_event(*data) {
							self.prop_queue.insert(l, *prop)
						}
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
