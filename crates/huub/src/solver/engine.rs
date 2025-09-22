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

use std::{collections::VecDeque, mem};

use index_vec::IndexVec;
use pindakaas::{
	solver::{
		cadical::{ProofTracer, ProofTracerDefinition},
		propagation::{
			ClausePersistence, Propagator as PropagatorExtension,
			PropagatorDefinition as PropagatorExtensionDefinition, SearchDecision, SolvingActions,
		},
	},
	Lit as RawLit, Var as RawVar,
};
use rustc_hash::FxHashMap;
pub(crate) use trace_new_lit;
use tracing::{debug, trace};

use crate::{
	actions::{
		DecisionActions, ExplanationActions, InspectionActions, ProofActions, TrailingActions,
	},
	branchers::{BoxedBrancher, Decision},
	constraints::{BoxedPropagator, Conflict, LazyReason, Reason},
	solver::{
		activation_list::{ActivationAction, ActivationActionS, ActivationList, IntEvent},
		bool_to_int::BoolToIntMap,
		int_var::{IntVar, IntVarRef, OrderStorage},
		queue::PropagatorQueue,
		solving_context::SolvingContext,
		trail::{Trail, TrailedInt},
		BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner, SolverConfiguration,
	},
	Clause, ConstraintProofID, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Definition of an [`Advisor`] giving the information about the [`View`]
/// subscribed to and the way in which to advise the propagator.
pub(crate) struct AdvisorDef {
	/// Whether the advise is on a [`BoolView`] being used as an [`IntView`]
	pub(crate) bool2int: bool,
	/// 64 bits of data communicated when advising propagator.
	pub(crate) data: u64,
	/// Whether the advise is on a [`IntView`] with a negative coefficient.
	pub(crate) negated: bool,
	/// The propagator being advised.
	pub(crate) propagator: PropRef,
}

#[derive(Debug, Default, Clone)]
/// A propagation engine implementing the [`Propagator`] trait.
pub(crate) struct Engine {
	/// Storage of the propagators.
	pub(crate) propagators: IndexVec<PropRef, (BoxedPropagator, Option<ProofHint>)>,
	/// List of propagators to advise of backtracking
	pub(crate) notify_of_backtrack: Vec<PropRef>,
	/// Storage of the branchers.
	pub(crate) branchers: Vec<BoxedBrancher>,
	/// Internal State representation of the propagation engine.
	pub(crate) state: State,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub(crate) struct EngineStatistics {
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

#[derive(Clone, Debug, Eq, PartialEq)]
/// Description of a literal propagation event in the propagation queue.
pub(crate) struct LitPropagation {
	/// The literal that was propagated.
	pub(crate) lit: RawLit,
	/// The reason for which the literal was propagated.
	pub(crate) reason: Result<Reason, bool>,
	/// The underlying event on complex types that triggered the propagation.
	///
	/// This event should be used to schedule further propagators.
	pub(crate) event: Option<(IntVarRef, IntEvent)>,
}

#[derive(Clone, Debug, Default)]
/// Internal state representation of the propagation engine disconnected from
/// the storage of the propagators and branchers.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`BoxedPropagator`], but it is not intended to be constructed by
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
	/// Includes lower and upper bounds for integer variables and Boolean
	/// variable assignments
	pub(crate) trail: Trail,
	/// Literals to be propagated by the oracle
	pub(crate) propagation_queue: VecDeque<LitPropagation>,
	/// Reasons for setting values
	pub(crate) reason_map: FxHashMap<RawLit, (Reason, Option<ProofHint>)>,
	/// Whether conflict has (already) been detected
	pub(crate) conflict: Option<(Conflict, Option<ProofHint>)>,
	/// Whether the solver is in a failure state.
	///
	/// Triggered when a conflict is detected during propagation, the solver
	/// should backtrack. Debug assertions will be triggered if other actions
	/// are taken instead. Some mechanisms, such as propagator queuing, might
	/// be disabled to optimize the execution of the solver.
	pub(crate) failed: bool,

	// ---- Non-Trailed Infrastructure ----
	/// Storage for clauses to be communicated to the solver
	pub(crate) clauses: VecDeque<(Clause, Option<ProofHint>)>,
	/// Solving statistics
	pub(crate) statistics: EngineStatistics,
	/// Whether VSIDS is currently enabled
	pub(crate) vsids: bool,

	// ---- Queuing Infrastructure ----
	/// Advisor data storage
	pub(crate) advisors: IndexVec<Advisor, AdvisorDef>,
	/// Boolean variable enqueueing information
	pub(crate) bool_activation: FxHashMap<RawVar, Vec<ActivationActionS>>,
	/// Integer variable enqueueing information
	pub(crate) int_activation: IndexVec<IntVarRef, ActivationList>,
	/// Queue of propagators awaiting action
	pub(crate) propagator_queue: PropagatorQueue,
	/// Last literal propagated by the Engine.
	last_propagated: Option<(RawLit, Option<(IntVarRef, IntEvent)>)>,

	// ---- Debugging Helpers ----
	#[cfg(debug_assertions)]
	/// List of integer variables that have been notified as fixed, but should
	/// be checked that the bounds match before propagation.
	pub(crate) check_int_fixed: Vec<(IntVarRef, IntVal)>,

	// ---- Proof Logging ----
	/// Whether proof logging is enabled.
	pub(crate) prove: bool,
	/// The proof hint information for the next clause to be logged to the
	/// proof.
	pub(crate) next_proof_hint: Option<ProofHint>,
}

/// A store of information that can be logged to the proof along with each
/// clause.
#[derive(Clone, Debug, Default)]
pub struct ProofHint {
	/// Identifiers for original user constraints
	pub constraint_ids: Vec<ConstraintProofID>,
	/// A name for the hint:
	/// either a solver constraint or a solver function e.g. AllDiff, LitDef
	/// etc.
	pub name: &'static str,
	// There will probably need to be more fields in future.
}
impl Engine {
	#[cfg(debug_assertions)]
	/// (DEBUG ONLY) Check that the reason of a propagated literal contains only
	/// known true literals
	fn debug_check_reason(&mut self, lit: RawLit) {
		use rustc_hash::FxHashSet;

		if let Some((reason, _proof_hint)) = self.state.reason_map.get(&lit).cloned() {
			// If reason is lazy, go to the assignment level of the literal.
			if let Reason::Lazy(_) = reason {
				self.state.trail.goto_assign_lit(lit);
			}
			// Reason is in the form (a /\ b /\ ...), which then forms the
			// implication (a /\ b /\ ...) -> lit
			let clause: Clause = reason.explain(&mut self.propagators, &mut self.state, Some(lit));
			// This is converted into a clause (¬a \/ ¬b \/ ... \/ lit)
			let mut seen = FxHashSet::default();
			for &l in &clause {
				// Ensure that the same literal is not negated in the reason
				if seen.contains(&!l) {
					tracing::error!(
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
				// Get the value of the original reason lit by negating again: ¬¬a
				// gives a
				let val = self.state.trail.get_sat_value(!l);
				if !val.unwrap_or(false) {
					tracing::error!(
						clause = ?clause.iter().map(|&l| i32::from(l)).collect::<Vec<_>>(),
						lit_explained = i32::from(lit),
						lit_invalid = i32::from(!l),
						invalid_val = ?val,
						"invalid reason: not all antecedents are known true"
					);
				}
				debug_assert!(
					val.unwrap_or(false),
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
		self.state.notify_backtrack::<false>(new_level, restart);

		// Notify subscribed propagators of backtracking
		for &p in self.notify_of_backtrack.iter() {
			self.propagators[p].0.advise_of_backtrack(&mut self.state);
		}
	}

	/// Notify the given propagator about the integer change, providing the
	/// given data.
	///
	/// If `negated` is true, then the event is negated.
	pub(crate) fn notify_int_advisor(
		&mut self,
		prop: PropRef,
		iv: IntView,
		event: IntEvent,
		data: u64,
		negated: bool,
	) -> bool {
		let event = match event {
			IntEvent::LowerBound if negated => IntEvent::UpperBound,
			IntEvent::UpperBound if negated => IntEvent::LowerBound,
			e => e,
		};
		self.propagators[prop]
			.0
			.advise_of_int_change(&mut self.state, iv, event, data)
	}

	/// Notify the given propagator about the literal change, providing the
	/// given data.
	///
	/// If `bool2int` is true, then the literal is transformed into an integer
	/// view.
	pub(crate) fn notify_lit_advisor(
		&mut self,
		prop: PropRef,
		lit: RawLit,
		data: u64,
		bool2int: bool,
	) -> bool {
		if bool2int {
			self.propagators[prop].0.advise_of_int_change(
				&mut self.state,
				IntView(IntViewInner::Bool {
					transformer: Default::default(),
					lit,
				}),
				IntEvent::Fixed,
				data,
			)
		} else {
			self.propagators[prop].0.advise_of_bool_change(
				&mut self.state,
				BoolView(BoolViewInner::Lit(lit)),
				data,
			)
		}
	}
}

impl ProofActions for Engine {
	fn prove(&self) -> bool {
		self.state.prove
	}
	fn set_next_proof_hint(&mut self, proof_hint: Option<ProofHint>) {
		self.state.next_proof_hint = proof_hint;
	}

	fn get_current_proof_hint(&self) -> Option<ProofHint> {
		self.state.next_proof_hint.clone()
	}
}
impl PropagatorExtension for Engine {
	fn add_external_clause(
		&mut self,
		slv: &mut dyn SolvingActions,
	) -> Option<(Clause, ClausePersistence)> {
		if !self.state.clauses.is_empty() {
			let clause = self.state.clauses.pop_front(); // Known to be `Some`
			trace!(clause = ?clause.as_ref().unwrap().0.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add external clause");
			clause.map(|c| (c.0, ClausePersistence::Irreduntant))
		} else if !self.state.propagation_queue.is_empty() {
			None // Require that the solver first applies the remaining propagation
		} else if let Some(conflict) = self.state.conflict.take() {
			let ctx = SolvingContext::new(slv, &mut self.state);
			let clause: Clause =
				conflict
					.0
					.reason
					.explain(&mut self.propagators, ctx.state, conflict.0.subject);
			debug!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add conflict clause");
			Some((clause, ClausePersistence::Forgettable))
		} else {
			None
		}
	}

	fn add_reason_clause(&mut self, propagated_lit: RawLit) -> Clause {
		// Find reason in storage
		let reason = self.state.reason_map.remove(&propagated_lit);
		// Create an explanation clause from the reason
		let clause = if let Some((reason, proof_hint)) = reason {
			// If the reason is lazy, restore the current state to the state when the
			// propagation happened before explaining.
			if matches!(reason, Reason::Lazy(_)) {
				self.state.trail.goto_assign_lit(propagated_lit);
			}

			// Ensure the tracer logs the hint associated with this clause
			self.set_next_proof_hint(proof_hint);
			reason.explain(&mut self.propagators, &mut self.state, Some(propagated_lit))
		} else {
			self.set_next_proof_hint(None);
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

		// Calculate values of each integer and notify propagators
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
				ctx.state.int_vars[r].notify_upper_bound(&mut ctx.state.trail, lb);

				let activation = mem::take(&mut ctx.state.int_activation[r]);
				for action in activation.activated_by(IntEvent::Fixed) {
					let prop = match action {
						ActivationAction::Advise(adv) => {
							let &AdvisorDef {
								data, propagator, ..
							} = &ctx.state.advisors[adv];
							if !self.propagators[propagator].0.advise_of_int_change(
								ctx.state,
								IntView(IntViewInner::VarRef(r)),
								IntEvent::Fixed,
								data,
							) {
								continue;
							}
							propagator
						}
						ActivationAction::Enqueue(prop) => prop,
					};
					ctx.state.propagator_queue.enqueue_propagator(prop);
				}
				ctx.state.int_activation[r] = activation;
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
			if let Reason::Lazy(LazyReason(prop, data)) = c.0.reason {
				let reason = self.propagators[prop]
					.0
					.explain(&mut self.state, c.0.subject, data);
				Conflict {
					subject: c.0.subject,
					reason: Reason::Eager(reason.into()),
				}
			} else {
				c.0
			}
		});

		// Revert to real decision level
		self.notify_backtrack::<true>(level as usize, false);
		debug_assert!(self.state.conflict.is_none());
		self.state.conflict = conflict.map(|c| (c, self.state.get_current_proof_hint()));

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
					_ => {
						self.state
							.propagation_queue
							.retain(|event| event.lit != lit);
						None
					}
				},
				None => None,
			};

			// Enqueue based on direct literal
			if !self.state.failed {
				if let Some(activations) = self
					.state
					.bool_activation
					.get_mut(&lit.var())
					.map(mem::take)
				{
					for &action in &activations {
						let prop = match action.into() {
							ActivationAction::Advise(adv) => {
								let &AdvisorDef {
									bool2int,
									data,
									propagator,
									..
								} = &self.state.advisors[adv];
								let enqueue =
									self.notify_lit_advisor(propagator, lit, data, bool2int);
								if !enqueue {
									continue;
								}
								propagator
							}
							ActivationAction::Enqueue(prop) => prop,
						};
						self.state.propagator_queue.enqueue_propagator(prop);
					}

					*self.state.bool_activation.get_mut(&lit.var()).unwrap() = activations;
				}
			}

			// Enqueue based on literal meaning in complex type
			let iv_event = iv_event.or_else(|| {
				let (iv, meaning) = self.state.get_int_lit_meaning(lit)?;
				// Enact domain changes and determine change event
				let (lb, ub) = self.state.int_vars[iv].get_bounds(&self.state);
				let event = match meaning {
					IntLitMeaning::Eq(val) if val == lb && val == ub => None,
					IntLitMeaning::Eq(val) if val < lb || val > ub => {
						// Notified of invalid assignment, do nothing.
						//
						// Although we do not expect this to happen, it seems that CaDiCaL
						// chronological backtracking might send notifications before
						// additional propagation.
						trace!(lit = i32::from(lit), lb, ub, "invalid eq notification");
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
							self.state.int_vars[iv].notify_lower_bound(&mut self.state.trail, val);
						}
						if val < ub {
							self.state.int_vars[iv].notify_upper_bound(&mut self.state.trail, val);
						}
						Some(IntEvent::Fixed)
					}
					IntLitMeaning::NotEq(i) if i < lb || i > ub => None,
					IntLitMeaning::NotEq(_) => Some(IntEvent::Domain),
					IntLitMeaning::GreaterEq(new_lb) if new_lb <= lb => None,
					IntLitMeaning::GreaterEq(new_lb) => {
						trace!(lit = i32::from(lit), lb = new_lb, "new lb");
						self.state.int_vars[iv].notify_lower_bound(&mut self.state.trail, new_lb);
						Some(if new_lb == ub {
							IntEvent::Fixed
						} else {
							IntEvent::LowerBound
						})
					}
					IntLitMeaning::Less(i) => {
						let new_ub = i - 1;
						if new_ub < ub {
							trace!(lit = i32::from(lit), ub = new_ub, "new ub");
							self.state.int_vars[iv]
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

			if !self.state.failed {
				if let Some((iv, event)) = iv_event {
					let activations = mem::take(&mut self.state.int_activation[iv]);
					for action in activations.activated_by(event) {
						let prop = match action {
							ActivationAction::Advise(adv) => {
								let &AdvisorDef {
									negated,
									data,
									propagator,
									..
								} = &self.state.advisors[adv];
								let enqueue = self.notify_int_advisor(
									propagator,
									IntView(IntViewInner::VarRef(iv)),
									event,
									data,
									negated,
								);
								if !enqueue {
									continue;
								}
								propagator
							}
							ActivationAction::Enqueue(prop) => prop,
						};
						self.state.propagator_queue.enqueue_propagator(prop);
					}
					self.state.int_activation[iv] = activations;
				}
			}
		}
	}

	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		debug!(new_level, restart, "backtrack");
		self.notify_backtrack::<false>(new_level, restart);
	}

	fn notify_new_decision_level(&mut self) {
		// Solver should not be in a failed state (no propagator conflict should
		// exist), and any conflict should have been communicated to the SAT oracle.
		debug_assert!(!self.state.failed);
		debug_assert!(self.state.conflict.is_none());
		// All propagation should have been communicated to the SAT oracle.
		debug_assert!(self.state.propagation_queue.is_empty());
		// Note that `self.state.clauses` may not be empty because [`Self::decide`]
		// might have introduced a new literal, which would in turn add its defining
		// clauses to `self.state.clauses`.

		trace!("new decision level");
		self.state.notify_new_decision_level();
	}

	#[tracing::instrument(level = "debug", skip(self, slv), fields(level = self.state.decision_level()))]
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Option<RawLit> {
		debug_assert!(self.state.last_propagated.is_none());
		// Check whether there are previous clauses to be communicated
		if !self.state.clauses.is_empty() {
			return None;
		}
		if self.state.propagation_queue.is_empty() && self.state.conflict.is_none() {
			#[cfg(debug_assertions)]
			{
				// (DEBUG ONLY) Check that all integers that where fixed by equality
				// literals had their bound literals set to match.
				for (iv, i) in mem::take(&mut self.state.check_int_fixed) {
					let iv = IntView(IntViewInner::VarRef(iv));
					debug_assert_eq!(self.state.get_int_val(iv), Some(i));
					let lb_lit = self
						.state
						.try_int_lit(iv, IntLitMeaning::GreaterEq(i))
						.unwrap();
					let ub_lit = self
						.state
						.try_int_lit(iv, IntLitMeaning::Less(i + 1))
						.unwrap();
					debug_assert_eq!(self.state.get_bool_val(lb_lit), Some(true));
					debug_assert_eq!(self.state.get_bool_val(ub_lit), Some(true));
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
			debug!(lit = i32::from(lit), "notify oracle");
			debug_assert!(self.state.trail.get_sat_value(lit).is_some());
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

impl PropagatorExtensionDefinition for Engine {
	const CHECK_ONLY: bool = false;
	const REASON_PERSISTENCE: ClausePersistence = ClausePersistence::Forgettable;
}

impl ProofTracer for Engine {
	fn add_original_clause(&mut self, id: u64, redundant: bool, clause: &[RawLit], restored: bool) {
		if let Some(proof_hint) = self.get_current_proof_hint() {
			trace!(target : "proof", id = id, redundant = redundant, restored = restored, clause = ?clause.iter().map(|&lit| i32::from(lit)).collect::<Vec<i32>>(), constraint_ids = ?proof_hint.constraint_ids, hint_name = proof_hint.name, "add_original_clause");
		} else {
			trace!(target : "proof", id = id, redundant = redundant, restored = restored, clause = ?clause.iter().map(|&lit| i32::from(lit)).collect::<Vec<i32>>(),  "add_original_clause");
		}
	}
	fn add_derived_clause(
		&mut self,
		id: u64,
		redundant: bool,
		clause: &[RawLit],
		antecedents: &[u64],
	) {
		trace!(target : "proof", id = id, redundant = redundant, clause = ?clause.iter().map(|&lit| i32::from(lit)).collect::<Vec<i32>>(), antecedents = ?antecedents.to_vec(), "add_derived_clause");
	}
	fn delete_clause(&mut self, id: u64, redundant: bool, clause: &[RawLit]) {
		trace!(target: "proof", id = id, redundant = redundant, clause = ?clause.iter().map(|&lit| i32::from(lit)).collect::<Vec<i32>>(), "delete_clause");
	}
}

impl ProofTracerDefinition for Engine {
	const ANTECEDENTS: bool = true;

	const FINALIZE_CLAUSES: bool = false;
}

impl State {
	/// Returns the current decision level of the solver.
	fn decision_level(&self) -> u32 {
		self.trail.decision_level()
	}

	/// Internal method called to process the backtracking to an earlier
	/// decision level.
	///
	/// The generic argument `ARTIFICIAL` is used to signal when the solver is
	/// backtracking from an artificial decision level. An example of the use of
	/// artificial decision levels is found in the [`Engine::check_model`]
	/// method, where it is used to artificially fix any integer variables
	/// using lazy encoding.
	fn notify_backtrack<const ARTIFICIAL: bool>(&mut self, level: usize, restart: bool) {
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

		// Switch to VSIDS if the number of conflicts exceeds the threshold
		if let Some(conflicts) = self.config.vsids_after_conflict {
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
			} else if self.config.vsids_after_restart {
				self.vsids = true;
				debug!(
					vsids = self.vsids,
					restart = self.statistics.restarts,
					"enable vsids after restart"
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

	/// Internal method to get the [`IntVarRef`] and strongest [`IntLitMeaning`]
	/// for a given literal, if it is an integer literal.
	fn get_int_lit_meaning(&self, lit: RawLit) -> Option<(IntVarRef, IntLitMeaning)> {
		let (iv, meaning) = self.bool_to_int.get(lit.var())?;
		let meaning = match meaning {
			// Eager literal, request meaning from variable itself.
			None => self.int_vars[iv].lit_meaning(lit),
			// Lazy literal, transform negated meanings dealing with gaps in domain when necessary.
			Some(IntLitMeaning::Less(i)) if !lit.is_negated() => {
				let i = self.int_vars[iv].tighten_less_lit(i);
				IntLitMeaning::Less(i)
			}
			Some(m) if lit.is_negated() => !m,
			Some(m) => m,
		};
		Some((iv, meaning))
	}

	/// Register the [`Reason`] to explain why `lit` has been assigned.
	pub(crate) fn register_reason(&mut self, lit: RawLit, built_reason: Result<Reason, bool>) {
		match built_reason {
			Ok(reason) => {
				// Insert new reason, possibly overwriting old one (from previous search
				// attempt)
				let _ = self
					.reason_map
					.insert(lit, (reason, self.get_current_proof_hint()));
			}
			Err(true) => {
				// No (previous) reason required
				let _ = self.reason_map.remove(&lit);
			}
			Err(false) => unreachable!("invalid reason"),
		}
	}

	/// Enable proof logging functionality.
	pub(crate) fn set_prove(&mut self, enabled: bool) {
		self.prove = enabled;
	}
	/// Set whether the solver should toggle between VSIDS and a user defined
	/// search strategy after every restart.
	///
	/// Note that this setting is ignored if the solver is set to use VSIDS
	/// only.
	pub(crate) fn set_toggle_vsids(&mut self, enabled: bool) {
		self.config.toggle_vsids = enabled;
	}

	/// Set the number of conflicts after which the solver should switch to
	/// using VSIDS to make search decisions.
	pub(crate) fn set_vsids_after_conflict(&mut self, conflicts: Option<u32>) {
		self.config.vsids_after_conflict = conflicts;
	}

	/// Set whether the solver should switch to using VSIDS after a restart.
	pub(crate) fn set_vsids_after_restart(&mut self, enable: bool) {
		self.config.vsids_after_restart = enable;
	}

	/// Set whether the solver should make all search decisions based on the
	/// VSIDS only.
	pub(crate) fn set_vsids_only(&mut self, enable: bool) {
		self.config.vsids_only = enable;
		self.vsids = enable;
	}
}

impl ExplanationActions for State {
	fn get_int_lit_meaning(&self, var: IntView, lit: RawLit) -> Option<IntLitMeaning> {
		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				let (iv2, mut meaning) = self.get_int_lit_meaning(lit)?;
				if iv != iv2 {
					return None;
				}
				if let IntViewInner::Linear { transformer, .. } = var.0 {
					meaning = transformer.transform_lit(meaning);
				}
				Some(meaning)
			}
			IntViewInner::Const(_) => None,
			IntViewInner::Bool { lit: var_lit, .. } if lit.var() != var_lit.var() => None,
			IntViewInner::Bool {
				lit: var_lit,
				transformer,
			} => {
				let mut meaning = IntLitMeaning::GreaterEq(1);
				if var_lit != lit {
					meaning = !meaning;
				}
				meaning = transformer.transform_lit(meaning);
				Some(meaning)
			}
		}
	}

	fn get_int_lit_relaxed(
		&mut self,
		var: IntView,
		meaning: IntLitMeaning,
	) -> (BoolView, IntLitMeaning) {
		debug_assert!(
			!matches!(meaning, IntLitMeaning::Eq(_)),
			"relaxed integer literals are not yet supported for IntLitMeaning::Eq(_)"
		);
		// Transform literal meaning if view is a linear transformation
		let meaning = match var.0 {
			IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } => {
				match transformer.rev_transform_lit(meaning) {
					Ok(m) => m,
					Err(v) => return (BoolView(BoolViewInner::Const(v)), meaning),
				}
			}
			_ => meaning,
		};

		// Get the (relaxed) boolean view representing the meaning and the actual
		// (relaxed) meaning
		let (bv, meaning) = match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				let var_def = &mut self.int_vars[iv];
				match meaning {
					IntLitMeaning::GreaterEq(v) => {
						let (bv, v) = var_def.get_greater_eq_lit_or_weaker(&self.trail, v);
						(bv, IntLitMeaning::GreaterEq(v))
					}
					IntLitMeaning::Less(v) => {
						let (bv, v) = var_def.get_less_lit_or_weaker(&self.trail, v);
						(bv, IntLitMeaning::Less(v))
					}
					IntLitMeaning::NotEq(v) => {
						if let Some(bv) = self.try_int_lit(var, meaning) {
							(bv, IntLitMeaning::NotEq(v))
						} else {
							let lb = self.get_int_lower_bound(var);
							if lb > v {
								(
									self.get_int_lower_bound_lit(var),
									IntLitMeaning::GreaterEq(lb),
								)
							} else {
								let ub = self.get_int_upper_bound(var);
								debug_assert!(ub < v);
								(
									self.get_int_upper_bound_lit(var),
									IntLitMeaning::Less(ub + 1),
								)
							}
						}
					}
					_ => unreachable!(),
				}
			}
			IntViewInner::Const(c) => (
				BoolView(BoolViewInner::Const(match meaning {
					IntLitMeaning::GreaterEq(i) => c >= i,
					IntLitMeaning::Less(i) => c < i,
					IntLitMeaning::Eq(i) => c == i,
					IntLitMeaning::NotEq(i) => c != i,
				})),
				meaning,
			),
			IntViewInner::Bool { lit, .. } => {
				let (b_meaning, negated) =
					if matches!(meaning, IntLitMeaning::NotEq(_) | IntLitMeaning::Less(_)) {
						(!meaning, true)
					} else {
						(meaning, false)
					};
				let bv = BoolView(match b_meaning {
					IntLitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					IntLitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
					IntLitMeaning::Eq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::Eq(_) => BoolViewInner::Const(false),
					_ => unreachable!(),
				});
				(if negated { !bv } else { bv }, meaning)
			}
		};

		// Transform the meaning back to fit the original view if it was linearly
		// transformed
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
				self.int_vars[var].get_bool_lit(meaning).map(|t| t.0)
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

impl ProofActions for State {
	fn prove(&self) -> bool {
		self.prove
	}
	fn set_next_proof_hint(&mut self, proof_hint: Option<ProofHint>) {
		self.next_proof_hint = proof_hint;
	}

	fn get_current_proof_hint(&self) -> Option<ProofHint> {
		self.next_proof_hint.clone()
	}
}
impl TrailingActions for State {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		self.trail.get_bool_val(bv)
	}

	fn get_trailed_int(&self, x: TrailedInt) -> IntVal {
		self.trail.get_trailed_int(x)
	}

	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal {
		self.trail.set_trailed_int(x, v)
	}
}

impl ProofHint {
	/// Helper function to make a proof hint with with just a string name
	pub fn name_only(name: &'static str) -> Self {
		ProofHint {
			constraint_ids: vec![],
			name,
		}
	}
}
index_vec::define_index_type! {
	/// Identifies an propagator in a [`Solver`]
	pub struct PropRef = u32;
	// Allow storing as i32 in [`ActivationActionS`]
	MAX_INDEX = i32::MAX as usize;
}

index_vec::define_index_type! {
	/// Identifies an advisor in the [`State`]
	pub struct Advisor = u32;
	// Allow storing as i32 in [`ActivationActionS`]
	MAX_INDEX = i32::MAX as usize;
}
