//! Module containing the main propagation engine of the solver.

/// Macro to output a trace message when a new literal is registered.
macro_rules! trace_new_lit {
	($iv:expr, $def:expr, $lit:expr) => {
		tracing::trace!(
			target: "literal",
			lit = i32::from($lit),
			int_var = $iv.ident(),
			is_eq = matches!($def.meaning, IntLitMeaning::Eq(_)),
			val = match $def.meaning {
				IntLitMeaning::Eq(val) => val,
				IntLitMeaning::Less(val) => val,
				_ => unreachable!(),
			},
			"register new literal"
		);
	};
}

use std::{collections::VecDeque, mem};

use pindakaas::{
	Lit as RawLit, Var as RawVar,
	solver::propagation::{
		ClausePersistence, Propagator as PropagatorExtension,
		PropagatorDefinition as PropagatorExtensionDefinition, SearchDecision, SolvingActions,
	},
};
use rustc_hash::FxHashMap;
pub(crate) use trace_new_lit;
use tracing::{debug, trace, warn};

use crate::{
	Clause, IntVal,
	actions::{
		BoolInspectionActions, IntEvent, ReasoningContext, ReasoningEngine, Trailed,
		TrailingActions,
	},
	constraints::{BoxedPropagator, Conflict, DeferredReason, Reason},
	helpers::bytes::Bytes,
	solver::{
		IntLitMeaning, SearchStrategy, SwitchTrigger,
		activation_list::{ActivationAction, ActivationActionS, ActivationList},
		bool_to_int::BoolToIntMap,
		branchers::{BoxedBrancher, Directive},
		decision::{
			Decision,
			integer::{IntDecision, OrderStorage},
		},
		initialization_context::InitializationContext,
		queue::PropagatorQueue,
		solving_context::SolvingContext,
		trail::Trail,
		view::{View, boolean::BoolView},
	},
};

/// Identifies an advisor in the [`State`]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AdvRef(u32);

/// Definition of an [`Advisor`] giving the information about the [`View`]
/// subscribed to and the way in which to advise the propagator.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

/// A propagation engine implementing the [`Propagator`] trait.
#[derive(Clone, Debug, Default)]
pub struct Engine {
	/// Storage of the propagators.
	pub(crate) propagators: Vec<BoxedPropagator>,
	/// Storage of the branchers.
	pub(crate) branchers: Vec<BoxedBrancher>,
	/// Internal State representation of the propagation engine.
	pub(crate) state: State,
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
/// Identifies an propagator in a [`Solver`]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PropRef(u32);

/// Internal state representation of the propagation engine disconnected from
/// the storage of the propagators and branchers.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`BoxedPropagator`], but it is not intended to be constructed by
/// the user. It should merely be seen as the implementation of the
/// [`ExplanationActions`] trait.
#[derive(Clone, Debug, Default)]
pub struct State {
	/// Search strategy to use during solving
	pub(crate) search_strategy: SearchStrategy,

	// ---- Trailed Value Infrastructure (e.g., decision variables) ----
	/// Storage for the data of the integer decision variables.
	pub(crate) int_vars: Vec<IntDecision>,
	/// Mapping from boolean variables to integer variables.
	pub(crate) bool_to_int: BoolToIntMap,
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
	pub(crate) bool_activation: FxHashMap<RawVar, Vec<ActivationActionS>>,
	/// Integer variable enqueueing information.
	pub(crate) int_activation: Vec<ActivationList>,
	/// Queue of propagators awaiting action.
	pub(crate) propagator_queue: PropagatorQueue,
	/// Last literal propagated by the Engine.
	last_propagated: Option<(RawLit, Option<(Decision<IntVal>, IntEvent)>)>,

	// ---- Debugging Helpers ----
	/// List of integer variables that have been notified as fixed, but should
	/// be checked that the bounds match before propagation.
	#[cfg(debug_assertions)]
	pub(crate) check_int_fixed: Vec<(Decision<IntVal>, IntVal)>,
}

impl AdvRef {
	/// Recreate the advisor reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the advisor vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new advisor reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index <= i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the advisor reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}

impl Engine {
	/// (DEBUG ONLY) Check that the reason of a propagated literal contains only
	/// known true literals
	#[cfg(debug_assertions)]
	fn debug_check_reason(&mut self, lit: RawLit) {
		use rustc_hash::FxHashSet;

		use crate::actions::BoolInspectionActions;

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
				seen.insert(l);
				if l == lit {
					continue;
				}
				// Get the value of the original reason lit by negating again: ¬¬a
				// gives a
				let val = Decision::<bool>(!l).val(&self.state.trail);
				if !val.unwrap_or(false) {
					tracing::error!(
						target: "solver",
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

				// Ensure the lazy literal for the upper bound exists
				let ub_lit = r.lit(&mut ctx, IntLitMeaning::Less(lb + 1));
				if let BoolView::Lit(ub_lit) = ub_lit.0 {
					let prev = ctx.state.trail.assign_lit(ub_lit.0);
					debug_assert_eq!(prev, None);
				}
				ctx.state.int_vars[r.idx()].notify_upper_bound(&mut ctx.state.trail, lb);

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
				let reason = self.propagators[prop as usize].explain(
					&mut self.state,
					c.subject.map(View::from).unwrap_or(true.into()),
					data,
				);
				Conflict {
					subject: c.subject,
					reason: match Reason::from_view(Reason::from_iter(reason)) {
						Err(false) => panic!("invalid lazy reason"), // TODO: Improve message
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
						self.branchers.remove(current);
					}
				}
			}
		}
		self.state.statistics.sat_search_directives += 1;
		SearchDecision::Free
	}

	fn notify_assignments(&mut self, lits: &[RawLit]) {
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

impl PropagatorExtensionDefinition for Engine {
	const CHECK_ONLY: bool = false;
	const REASON_PERSISTENCE: ClausePersistence = ClausePersistence::Forgettable;
}

impl ReasoningEngine for Engine {
	type Atom = View<bool>;
	type Conflict = Conflict<Decision<bool>>;

	type ExplanationCtx<'a> = State;
	type InitializationCtx<'a> = InitializationContext<'a>;
	type NotificationCtx<'a> = State;
	type PropagationCtx<'a> = SolvingContext<'a>;
}

impl PropRef {
	/// Invalid propagator reference to be used as a placeholder.
	pub(crate) const INVALID: PropRef = PropRef(i32::MAX as u32);

	/// Recreate the propagator reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the propagator vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new propagator reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index <= i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the propagator reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}

impl State {
	/// Returns the current decision level of the solver.
	fn decision_level(&self) -> u32 {
		self.trail.decision_level()
	}

	/// Internal method to get the [`IntVarRef`] and strongest [`IntLitMeaning`]
	/// for a given literal, if it is an integer literal.
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
	fn notify_new_decision_level(&mut self) {
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
				// No (previous) reason required
				self.reason_map.remove(&lit);
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

#[cfg(test)]
mod tests {
	use pindakaas::solver::propagation::Propagator as ExternalPropagator;

	use crate::{
		IntSet, IntVal,
		actions::{
			BoolPropagationActions, InitActions, IntDecisionActions, IntEvent, IntInitActions,
			IntPropCond, IntPropagationActions, ReasoningEngine,
		},
		constraints::Propagator,
		solver::{
			BoolView, Decision, IntLitMeaning, Solver, View,
			decision::integer::{EncodingType, IntDecision},
			engine::Engine,
		},
	};

	/// Regression test for losing an integer notification when a queued
	/// propagation is also implied by another propagated literal.
	///
	/// The propagator emits two consequences in order:
	/// - first `req_first`, then `ge_1_second >= 1`.
	/// - A clause also makes `req_first -> ge_1_second >= 1`.
	///
	/// After the engine returns `req_first` to the SAT solver, the lower-bound
	/// literal is still queued, but its effect is already reflected in the
	/// trailed integer state. When the SAT solver reports both assignments
	/// together, the lower-bound advisor still has to be notified exactly once.
	/// Before the fix, the queued event was purged and this notification was
	/// lost.
	#[test]
	fn queued_integer_event_survives_sat_assignment() {
		use std::{cell::RefCell, rc::Rc};

		#[derive(Clone, Debug)]
		struct ProducerAndListener {
			req_first: Decision<bool>,
			notifications: Rc<RefCell<usize>>,
			ge_1_second: View<IntVal>,
			done: bool,
		}

		impl Propagator<Engine> for ProducerAndListener {
			fn initialize(&mut self, ctx: &mut <Engine as ReasoningEngine>::InitializationCtx<'_>) {
				ctx.enqueue_now(true);
				self.ge_1_second
					.advise_when(ctx, IntPropCond::LowerBound, 0);
			}

			fn advise_of_int_change(
				&mut self,
				_: &mut <Engine as ReasoningEngine>::NotificationCtx<'_>,
				data: u64,
				event: IntEvent,
			) -> bool {
				assert_eq!(data, 0);
				assert_eq!(event, IntEvent::LowerBound);
				*self.notifications.borrow_mut() += 1;
				false
			}

			fn propagate(
				&mut self,
				ctx: &mut <Engine as ReasoningEngine>::PropagationCtx<'_>,
			) -> Result<(), <Engine as ReasoningEngine>::Conflict> {
				assert!(!self.done);
				self.done = true;
				self.req_first.require(ctx, [])?;
				self.ge_1_second.tighten_min(ctx, 1, [])?;
				Ok(())
			}
		}

		let mut slv: Solver = Solver::default();
		let notifications = Rc::new(RefCell::new(0));
		let imply = slv.new_bool_decision();
		let var = IntDecision::new_in(
			&mut slv,
			IntSet::from(0..=2),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		slv.add_propagator(
			Box::new(ProducerAndListener {
				req_first: imply,
				notifications: Rc::clone(&notifications),
				ge_1_second: var,
				done: false,
			}),
			false,
		);
		let ge_view = var.lit(&mut slv, IntLitMeaning::GreaterEq(1));
		let BoolView::Lit(ge) = ge_view.0 else {
			unreachable!()
		};
		// The second consequence is also implied by the first one through SAT.
		slv.add_clause([(!imply).into(), ge_view]).unwrap();

		let (mut actions, mut engine) = slv.as_parts_mut();
		// Running propagate once communicates only the first consequence back to
		// SAT. The lower-bound propagation remains queued, but its bound update is
		// already visible in the integer trail.
		let propagated = ExternalPropagator::propagate(&mut *engine, &mut actions);
		assert_eq!(propagated, Some(imply.0));
		assert_eq!(engine.state.propagation_queue.len(), 1);
		assert_eq!(engine.state.propagation_queue[0].lit, ge.0);

		// SAT now reports both literals together. The queued lower-bound event must
		// survive this path so the advisor is still notified.
		ExternalPropagator::notify_assignments(&mut *engine, &[imply.0, ge.0]);
		assert_eq!(*notifications.borrow(), 1);

		let propagated = ExternalPropagator::propagate(&mut *engine, &mut actions);
		assert_eq!(propagated, None);

		assert_eq!(*notifications.borrow(), 1);
	}
}
