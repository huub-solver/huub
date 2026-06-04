//! Propagation pipeline: how the [`Engine`] interacts with the SAT solver and
//! drives registered propagators.

use std::mem;

use pindakaas::{
	Lit as RawLit,
	solver::propagation::{
		ClausePersistence, Propagator as PropagatorExtension, SearchDecision, SolvingActions,
	},
};
use tracing::{debug, trace};

use crate::{
	Clause, IntVal,
	actions::{BoolInspectionActions, IntEvent, TrailingActions},
	constraints::{DeferredReason, Reason},
	solver::{
		IntLitMeaning, Polarity,
		activation_list::ActivationAction,
		branchers::Directive,
		decision::{Decision, integer::OrderStorage},
		engine::{AdvRef, AdvisorDef, Engine, PropRef},
		solving_context::SolvingContext,
		trail::Trail,
		view::{View, boolean::BoolView},
	},
};

/// Description of a literal propagation event in the propagation queue.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LitPropagation {
	/// The literal that was propagated.
	pub(crate) lit: RawLit,
	/// The reason for which the literal was propagated.
	pub(crate) reason: Result<Reason<Decision<bool>>, bool>,
	/// The underlying event on complex types that triggered the propagation.
	///
	/// This event should be used to schedule further propagators.
	pub(crate) event: Option<(Decision<IntVal>, IntEvent)>,
}

impl Engine {
	/// (DEBUG ONLY) Check that the reason of a propagated literal contains only
	/// known true literals.
	///
	/// A reason atom is also accepted when its raw trail value is unknown or
	/// false but its [`IntLitMeaning`] is **currently entailed** by the
	/// CP-side bounds of its underlying integer variable. This guards
	/// against the asymmetry where the CP engine has already tightened the
	/// bounds via `trail.assign_lit` for one boundary literal but SAT has
	/// not yet unit-propagated weaker (but currently entailed) literals on
	/// the same integer variable. Those antecedents are semantically true
	/// even though the trail's variable value lags behind. We emit a
	/// warning rather than panicking.
	#[cfg(debug_assertions)]
	fn debug_check_reason(&mut self, lit: RawLit) {
		use rustc_hash::FxHashSet;

		if let Some(reason) = self.state.reason_map.get(&lit).cloned() {
			// If reason is lazy, go to the assignment level of the literal.
			if let Reason::Lazy(_) = reason {
				self.state.trail.goto_assign_lit(lit);
			}
			// Reason is in the form (a /\ b /\ ...), which then forms the
			// implication (a /\ b /\ ...) -> lit
			let clause: Clause<_> =
				reason.explain(&mut self.propagators, &mut self.state, Some(Decision(lit)));
			// This is converted into a clause (¬a \/ ¬b \/ ... \/ lit)
			let mut seen = FxHashSet::default();
			for &l in &clause {
				// Ensure that the same literal is not negated in the reason
				if seen.contains(&!l) {
					tracing::error!(
						target: "solver",
						clause = ?clause.iter().map(|&l| i32::from(l)).collect::<Vec<_>>(),
						lit_explained = i32::from(lit),
						lit_pos = i32::from(!l),
						lit_neg = i32::from(l),
						"invalid reason: literal and its negation in clause"
					);
					debug_assert!(
						false,
						"Both {l} and {} are found in the Reason for {lit}",
						!l
					);
				}
				let _ = seen.insert(l);
				if l == lit {
					continue;
				}
				// Get the value of the original reason lit by negating again:
				// ¬¬a gives a.
				let atom = Decision::<bool>(!l);
				let val = atom.val(&self.state.trail);
				if val == Some(true) {
					continue;
				}
				// Trail says unknown-or-false. Try to rescue via the CP-side
				// integer bounds: if the atom is an integer literal whose
				// meaning is currently entailed by the trailed bounds of its
				// underlying integer variable, the reason is still
				// semantically true and we emit a warning instead of a panic.
				if let Some((iv, meaning)) = self.state.get_int_lit_meaning(atom) {
					let int_var = &self.state.int_vars[iv.idx()];
					let lb = int_var.lower_bound(&self.state.trail);
					let ub = int_var.upper_bound(&self.state.trail);
					let entailed = match meaning {
						IntLitMeaning::GreaterEq(b) => lb >= b,
						IntLitMeaning::Less(b) => ub < b,
						IntLitMeaning::Eq(b) => lb == b && ub == b,
						IntLitMeaning::NotEq(b) => b < lb || b > ub,
					};
					if entailed {
						tracing::warn!(
							target: "solver",
							clause = ?clause.iter().map(|&l| i32::from(l)).collect::<Vec<_>>(),
							lit_explained = i32::from(lit),
							lit_stale = i32::from(!l),
							trail_val = ?val,
							meaning = ?meaning,
							bounds = ?(lb, ub),
							"reason atom not yet propagated on SAT trail but currently \
							 entailed by CP bounds — accepting"
						);
						continue;
					}
				}
				tracing::error!(
					target: "solver",
					clause = ?clause.iter().map(|&l| i32::from(l)).collect::<Vec<_>>(),
					lit_explained = i32::from(lit),
					lit_invalid = i32::from(!l),
					invalid_val = ?val,
					"invalid reason: not all antecedents are known true"
				);
				debug_assert!(
					false,
					"Literal {} in Reason for {lit} is {val:?}, but should be known true",
					!l,
				);
			}
			// If reason is lazy, return to current level
			if let Reason::Lazy(_) = reason {
				self.state.trail.reset_to_trail_head();
			}
		} else {
			debug_assert_eq!(
				self.state.decision_level(),
				0,
				"Literal {lit} propagated without reason at non-zero decision level",
			);
		}
	}

	/// [`PropagatorExtension::notify_backtrack`] implementation with additional
	/// `ARTIFICIAL` const generic parameter, used to signal when the solver is
	/// backtracking from an artificial decision level
	fn notify_backtrack<const ARTIFICIAL: bool>(&mut self, new_level: usize, restart: bool) {
		// Revert value changes to previous decision level
		self.state
			.notify_backtrack::<ARTIFICIAL>(new_level, restart);

		// Notify subscribed propagators of backtracking
		let notify = mem::take(&mut self.state.notify_of_backtrack);
		for &p in &notify {
			self.propagators[p.index()].advise_of_backtrack(&mut self.state);
		}
		self.state.notify_of_backtrack = notify;
	}

	/// Notify the given propagator about the integer change, providing the
	/// given data.
	///
	/// If `negated` is true, then the event is negated.
	pub(crate) fn notify_int_advisor(
		&mut self,
		prop: PropRef,
		event: IntEvent,
		data: u64,
		negated: bool,
	) -> bool {
		let event = match event {
			IntEvent::LowerBound if negated => IntEvent::UpperBound,
			IntEvent::UpperBound if negated => IntEvent::LowerBound,
			e => e,
		};
		self.propagators[prop.index()].advise_of_int_change(&mut self.state, data, event)
	}

	/// Notify the given propagator about the literal change, providing the
	/// given data.
	///
	/// If `bool2int` is true, then the literal is transformed into an integer
	/// view.
	pub(crate) fn notify_lit_advisor(&mut self, prop: PropRef, data: u64, bool2int: bool) -> bool {
		if bool2int {
			self.propagators[prop.index()].advise_of_int_change(
				&mut self.state,
				data,
				IntEvent::Fixed,
			)
		} else {
			self.propagators[prop.index()].advise_of_bool_change(&mut self.state, data)
		}
	}
}

impl PropagatorExtension for Engine {
	fn add_external_clause(
		&mut self,
		slv: &mut dyn SolvingActions,
	) -> Option<(Clause<RawLit>, ClausePersistence)> {
		if !self.state.clauses.is_empty() {
			let clause = self.state.clauses.pop_front(); // Known to be `Some`
			trace!(
				target: "solver",
				clause = ?clause.as_ref().unwrap().iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(),
				"add external clause"
			);
			clause.map(|c| (c, ClausePersistence::Irreduntant))
		} else if !self.state.propagation_queue.is_empty() {
			None // Require that the solver first applies the remaining propagation
		} else if let Some(conflict) = self.state.conflict.take() {
			let ctx = SolvingContext::new(slv, &mut self.state);
			let clause: Clause<_> =
				conflict
					.reason
					.explain(&mut self.propagators, ctx.state, conflict.subject);
			debug!(
				target: "solver",
				clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(),
				"add conflict clause"
			);
			Some((clause, ClausePersistence::Forgettable))
		} else {
			None
		}
	}

	fn add_reason_clause(&mut self, propagated_lit: RawLit) -> Clause<RawLit> {
		// Find reason in storage
		let reason = self.state.reason_map.remove(&propagated_lit);
		// Create an explanation clause from the reason
		let clause = if let Some(reason) = reason {
			// If the reason is lazy, restore the current state to the state when the
			// propagation happened before explaining.
			if matches!(reason, Reason::Lazy(_)) {
				self.state.trail.goto_assign_lit(propagated_lit);
			}

			reason.explain(
				&mut self.propagators,
				&mut self.state,
				Some(Decision(propagated_lit)),
			)
		} else {
			vec![propagated_lit]
		};

		debug!(
			target: "solver",
			clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(),
			"add reason clause"
		);
		clause
	}

	#[tracing::instrument(target = "solver", level = "debug", skip(self, slv, _sol))]
	fn check_solution(
		&mut self,
		slv: &mut dyn SolvingActions,
		_sol: &dyn pindakaas::Valuation,
	) -> bool {
		use crate::actions::IntDecisionActions;

		// Solver should not be in a failed state (no propagator conflict should
		// exist), and any conflict should have been communicated to the SAT solver.
		debug_assert!(!self.state.failed);
		debug_assert!(self.state.conflict.is_none());
		// All propagation should have been communicated to the SAT solver.
		debug_assert!(self.state.propagation_queue.is_empty());

		// Check model consistency assuming that all currently unfixed integer
		// variables take the lower bound as its value.
		//
		// Add artificial decision level to fix unfixed integer variables
		let level = self.state.decision_level();
		self.state.notify_new_decision_level();

		// Create a propagation context
		let mut ctx = SolvingContext::new(slv, &mut self.state);

		// Calculate values of each integer and notify propagators
		for r in (0..ctx.state.int_vars.len()).map(|v| Decision(v as u32)) {
			let (lb, ub) = ctx.state.int_vars[r.idx()].bounds(&ctx.state.trail);
			if lb != ub {
				debug_assert!(matches!(
					ctx.state.int_vars[r.idx()].order_encoding,
					OrderStorage::Lazy(_)
				));

				// Fix the unfixed variable to the bound preferred by its polarity:
				// a positive polarity fixes to the upper bound (by raising the
				// lower bound), otherwise to the lower bound (by lowering the upper
				// bound). Either way the required lazy literal is created.
				match ctx.state.int_vars[r.idx()].polarity {
					Some(Polarity::Positive) => {
						let lb_lit = r.lit(&mut ctx, IntLitMeaning::GreaterEq(ub));
						if let BoolView::Lit(lb_lit) = lb_lit.0 {
							let prev = ctx.state.trail.assign_lit(lb_lit.0);
							debug_assert_eq!(prev, None);
						}
						ctx.state.int_vars[r.idx()].notify_lower_bound(&mut ctx.state.trail, ub);
					}
					Some(Polarity::Negative) | None => {
						let ub_lit = r.lit(&mut ctx, IntLitMeaning::Less(lb + 1));
						if let BoolView::Lit(ub_lit) = ub_lit.0 {
							let prev = ctx.state.trail.assign_lit(ub_lit.0);
							debug_assert_eq!(prev, None);
						}
						ctx.state.int_vars[r.idx()].notify_upper_bound(&mut ctx.state.trail, lb);
					}
				}

				let activation = mem::take(&mut ctx.state.int_activation[r.idx()]);
				activation.for_each_activated_by(IntEvent::Fixed, |action| {
					let prop = match action {
						ActivationAction::Advise::<AdvRef, _>(adv) => {
							let &AdvisorDef {
								data, propagator, ..
							} = &ctx.state.advisors[adv.index()];
							if !self.propagators[propagator.index()].advise_of_int_change(
								ctx.state,
								data,
								IntEvent::Fixed,
							) {
								return;
							}
							propagator
						}
						ActivationAction::Enqueue(prop) => prop,
					};
					ctx.state.propagator_queue.enqueue_propagator(prop.raw());
				});
				ctx.state.int_activation[r.idx()] = activation;
			}
		}

		// Run propagators to find any conflicts
		ctx.run_propagators(&mut self.propagators);
		// No propagation can be triggered (all variables are fixed, so only
		// conflicts are possible)
		debug_assert!(self.state.propagation_queue.is_empty());

		// Process propagation results, and accept model if no conflict is detected
		let conflict = self.state.conflict.take().map(|c| {
			// Convert Lazy reasons into an eager ones
			if let Reason::Lazy(DeferredReason {
				propagator: prop,
				data,
			}) = c.reason
			{
				let lit_atom = c.subject.map(View::from).unwrap_or(true.into());
				let reason =
					self.propagators[prop as usize].explain(&mut self.state, lit_atom, data);
				crate::constraints::Conflict {
					subject: c.subject,
					reason: match Reason::from_view(Reason::from_iter(reason)) {
						Err(false) => panic!("invalid lazy reason"),
						Err(true) => Reason::Eager(Vec::new().into_boxed_slice()),
						Ok(r) => r,
					},
				}
			} else {
				c
			}
		});

		// Revert to real decision level
		self.notify_backtrack::<true>(level as usize, false);
		debug_assert!(self.state.conflict.is_none());
		self.state.conflict = conflict;

		let accept = self.state.conflict.is_none();
		debug!(target: "solver", accept, "check model");
		accept
	}

	fn decide(&mut self, slv: &mut dyn SolvingActions) -> SearchDecision {
		if !self.state.sat_search {
			// Find the current position in the brancher queue, and return
			// immediately if all branchers have been exhausted.
			let mut current = self.state.trail.trailed(Trail::CURRENT_BRANCHER);
			if current == self.branchers.len() {
				self.state.statistics.sat_search_directives += 1;
				return SearchDecision::Free;
			}

			// Create actions object and run current brancher
			let mut ctx = SolvingContext::new(slv, &mut self.state);
			while current < self.branchers.len() {
				match self.branchers[current].decide(&mut ctx) {
					Directive::Select(lit) => {
						let BoolView::Lit(lit) = lit.0 else {
							panic!("brancher yielded an already fixed literal");
						};
						debug_assert!(
							lit.val(&ctx).is_none(),
							"brancher yielded an already fixed literal"
						);
						// The current brancher has selected a literal, return it as our decision
						debug!(target: "solver", lit = i32::from(lit.0), "decide");
						self.state.statistics.user_search_directives += 1;
						return SearchDecision::Assign(lit.0);
					}
					Directive::Exhausted => {
						// The current brancher exhausted, move to next
						current += 1;
						ctx.set_trailed(Trail::CURRENT_BRANCHER, current);
					}
					Directive::Consumed => {
						// The current brancher has signaled to never yield decisions again. Remove
						// the brancher from the queue permanently.
						//
						// Note that this shifts all subsequent branchers (so we don't need to
						// increment current), but has bad complexity. However, due to the low
						// number of branchers, this is (likely) acceptable.
						let _ = self.branchers.remove(current);
					}
				}
			}
		}
		self.state.statistics.sat_search_directives += 1;
		SearchDecision::Free
	}

	fn notify_assignment(&mut self, lits: &[RawLit]) {
		debug!(
			target: "solver",
			lits = ?lits.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(),
			"assignments"
		);

		self.state.trail.reset_to_trail_head();

		// Enqueue propagators
		for &lit in lits {
			let iv_event = match self.state.trail.assign_lit(lit) {
				Some(false) => {
					self.state.failed = true;
					continue;
				}
				Some(true) => match self.state.last_propagated {
					Some((prev, event)) if lit == prev => {
						self.state.last_propagated = None;
						event
					}
					_ => self
						.state
						.propagation_queue
						.iter()
						.position(|event| event.lit == lit)
						.and_then(|pos| self.state.propagation_queue.remove(pos))
						.and_then(|event| event.event),
				},
				None => None,
			};

			// Enqueue based on direct literal
			if !self.state.failed
				&& let Some(activations) = self
					.state
					.bool_activation
					.get_mut(&lit.var())
					.map(mem::take)
			{
				for &action in &activations {
					let prop = match action.into() {
						ActivationAction::Advise::<AdvRef, _>(adv) => {
							let &AdvisorDef {
								bool2int,
								data,
								propagator,
								..
							} = &self.state.advisors[adv.index()];
							let enqueue = self.notify_lit_advisor(propagator, data, bool2int);
							if !enqueue {
								continue;
							}
							propagator
						}
						ActivationAction::Enqueue(prop) => prop,
					};
					self.state.propagator_queue.enqueue_propagator(prop.raw());
				}

				*self.state.bool_activation.get_mut(&lit.var()).unwrap() = activations;
			}

			// Enqueue based on literal meaning in complex type
			let iv_event = iv_event.or_else(|| {
				let (iv, meaning) = self.state.get_int_lit_meaning(Decision(lit))?;
				// Enact domain changes and determine change event
				let (lb, ub) = self.state.int_vars[iv.idx()].bounds(&self.state);
				let event = match meaning {
					IntLitMeaning::Eq(val) if val == lb && val == ub => None,
					IntLitMeaning::Eq(val) if val < lb || val > ub => {
						// Notified of invalid assignment, do nothing.
						//
						// Although we do not expect this to happen, it seems that CaDiCaL
						// chronological backtracking might send notifications before
						// additional propagation.
						trace!(
							target: "solver",
							lit = i32::from(lit),
							lb,
							ub,
							"invalid eq notification"
						);
						None
					}
					IntLitMeaning::Eq(val) => {
						#[cfg(debug_assertions)]
						{
							// (DEBUG ONLY) Push the integer variable and its value to check
							// that its bounds were updated before propagation occurs.
							self.state.check_int_fixed.push((iv, val));
						}
						if val > lb {
							self.state.int_vars[iv.idx()]
								.notify_lower_bound(&mut self.state.trail, val);
						}
						if val < ub {
							self.state.int_vars[iv.idx()]
								.notify_upper_bound(&mut self.state.trail, val);
						}
						Some(IntEvent::Fixed)
					}
					IntLitMeaning::NotEq(i) if i < lb || i > ub => None,
					IntLitMeaning::NotEq(_) => Some(IntEvent::Domain),
					IntLitMeaning::GreaterEq(new_lb) if new_lb <= lb => None,
					IntLitMeaning::GreaterEq(new_lb) => {
						trace!(target: "solver", lit = i32::from(lit), lb = new_lb, "new lb");
						self.state.int_vars[iv.idx()]
							.notify_lower_bound(&mut self.state.trail, new_lb);
						Some(if new_lb == ub {
							IntEvent::Fixed
						} else {
							IntEvent::LowerBound
						})
					}
					IntLitMeaning::Less(i) => {
						let new_ub = i - 1;
						if new_ub < ub {
							trace!(
								target: "solver",
								lit = i32::from(lit),
								ub = new_ub,
								"new ub"
							);
							self.state.int_vars[iv.idx()]
								.notify_upper_bound(&mut self.state.trail, new_ub);
							Some(if new_ub == lb {
								IntEvent::Fixed
							} else {
								IntEvent::UpperBound
							})
						} else {
							None
						}
					}
				}?;
				Some((iv, event))
			});

			if !self.state.failed
				&& let Some((iv, event)) = iv_event
			{
				let activations = mem::take(&mut self.state.int_activation[iv.idx()]);
				activations.for_each_activated_by(event, |action| {
					let prop = match action {
						ActivationAction::Advise::<AdvRef, _>(adv) => {
							let &AdvisorDef {
								negated,
								data,
								propagator,
								..
							} = &self.state.advisors[adv.index()];
							let enqueue = self.notify_int_advisor(propagator, event, data, negated);
							if !enqueue {
								return;
							}
							propagator
						}
						ActivationAction::Enqueue(prop) => prop,
					};
					self.state.propagator_queue.enqueue_propagator(prop.raw());
				});
				self.state.int_activation[iv.idx()] = activations;
			}
		}
	}

	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		debug!(target: "solver", new_level, restart, "backtrack");
		self.notify_backtrack::<false>(new_level, restart);
	}

	fn notify_new_decision_level(&mut self) {
		// Solver should not be in a failed state (no propagator conflict should
		// exist), and any conflict should have been communicated to the SAT solver.
		debug_assert!(!self.state.failed);
		debug_assert!(self.state.conflict.is_none());
		// All propagation should have been communicated to the SAT solver.
		debug_assert!(self.state.propagation_queue.is_empty());
		// Note that `self.state.clauses` may not be empty because [`Self::decide`]
		// might have introduced a new literal, which would in turn add its defining
		// clauses to `self.state.clauses`.

		trace!(target: "solver", "new decision level");
		self.state.notify_new_decision_level();

		// Update peak decision level
		let new_level = self.state.decision_level();
		if new_level > self.state.statistics.peak_depth {
			self.state.statistics.peak_depth = new_level;
		}
	}

	#[tracing::instrument(
		target = "solver",
		level = "debug",
		skip(self, slv),
		fields(level = self.state.decision_level())
	)]
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Option<RawLit> {
		debug_assert!(self.state.last_propagated.is_none());
		// Check whether there are previous clauses to be communicated
		if !self.state.clauses.is_empty() {
			return None;
		}
		if self.state.propagation_queue.is_empty() && self.state.conflict.is_none() {
			#[cfg(debug_assertions)]
			{
				use crate::actions::{BoolInspectionActions, IntInspectionActions};

				// (DEBUG ONLY) Check that all integers that where fixed by equality
				// literals had their bound literals set to match.
				for (iv, i) in mem::take(&mut self.state.check_int_fixed) {
					debug_assert_eq!(iv.val(&self.state), Some(i));
					let lb_lit = iv
						.try_lit(&self.state, IntLitMeaning::GreaterEq(i))
						.unwrap();
					let ub_lit = iv.try_lit(&self.state, IntLitMeaning::Less(i + 1)).unwrap();
					debug_assert_eq!(lb_lit.val(&self.state), Some(true));
					debug_assert_eq!(ub_lit.val(&self.state), Some(true));
				}
			}
			// If there are no previous changes, run propagators
			SolvingContext::new(slv, &mut self.state).run_propagators(&mut self.propagators);
		}
		// Check whether there are new clauses that need to be communicated first
		if !self.state.clauses.is_empty() {
			return None;
		}
		if let Some(LitPropagation { lit, reason, event }) =
			self.state.propagation_queue.pop_front()
		{
			debug!(target: "solver", lit = i32::from(lit), "propagate");
			debug_assert!(self.state.trail.sat_value(lit).is_some());
			self.state.register_reason(lit, reason);
			#[cfg(debug_assertions)]
			{
				// (DEBUG ONLY) Ensure the literal's explanation is valid in its trail
				// position.
				self.debug_check_reason(lit);
			}
			self.state.last_propagated = Some((lit, event));
			Some(lit)
		} else {
			None
		}
	}
}
