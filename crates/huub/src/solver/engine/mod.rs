//! Main propagation engine of the solver.
//!
//! This module is split into several files:
//!
//! - [`state`]: the [`State`] struct that holds all engine-internal storage
//!   (trail, integer/Boolean variable data, queues, statistics).
//! - [`propagation`]: the [`pindakaas::solver::propagation::Propagator`]
//!   implementation that drives propagation, conflict analysis, and
//!   decision-making, together with the [`LitPropagation`] event record.
//! - [`advisor`]: the [`AdvRef`] / [`AdvisorDef`] types describing how
//!   propagators subscribe to variable change notifications.
//! - [`prop_ref`]: the [`PropRef`] index type for propagator storage.

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

pub(crate) mod advisor;
pub(crate) mod prop_ref;
pub(crate) mod propagation;
pub(crate) mod state;

use pindakaas::solver::propagation::{
	ClausePersistence, PropagatorDefinition as PropagatorExtensionDefinition,
};
pub(crate) use trace_new_lit;

pub(crate) use crate::solver::engine::{
	advisor::{AdvRef, AdvisorDef},
	prop_ref::PropRef,
	propagation::LitPropagation,
	state::State,
};
use crate::{
	actions::ReasoningEngine,
	constraints::{BoxedPropagator, Conflict},
	solver::{
		branchers::BoxedBrancher, decision::Decision,
		initialization_context::InitializationContext, solving_context::SolvingContext, view::View,
	},
};

/// A propagation engine implementing the
/// [`pindakaas::solver::propagation::Propagator`] trait.
#[derive(Clone, Debug, Default)]
pub struct Engine {
	/// Storage of the propagators.
	pub(crate) propagators: Vec<BoxedPropagator>,
	/// Storage of the branchers.
	pub(crate) branchers: Vec<BoxedBrancher>,
	/// Internal State representation of the propagation engine.
	pub(crate) state: State,
}

impl PropagatorExtensionDefinition for Engine {
	const CHECK_ONLY: bool = false;
	const REASON_PERSISTENCE: ClausePersistence = ClausePersistence::Forgettable;
}

impl ReasoningEngine for Engine {
	type Atom = View<bool>;
	type Conflict = Conflict<Decision<bool>>;

	type ExplanationContext<'a> = State;
	type InitializationContext<'a> = InitializationContext<'a>;
	type NotificationContext<'a> = State;
	type PropagationContext<'a> = SolvingContext<'a>;
}

#[cfg(test)]
mod tests {
	use pindakaas::solver::propagation::Propagator as ExternalPropagator;

	use crate::{
		IntVal,
		actions::{
			BoolPropagationActions, InitActions, IntDecisionActions, IntEvent, IntInitActions,
			IntPropCond, IntPropagationActions, ReasoningEngine,
		},
		constraints::Propagator,
		solver::{
			BoolView, Decision, IntLitMeaning, LiteralStrategy, Solver, View, engine::Engine,
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
			fn initialize(
				&mut self,
				ctx: &mut <Engine as ReasoningEngine>::InitializationContext<'_>,
			) {
				ctx.enqueue_now(true);
				self.ge_1_second
					.advise_when(ctx, IntPropCond::LowerBound, 0);
			}

			fn advise_of_int_change(
				&mut self,
				_: &mut <Engine as ReasoningEngine>::NotificationContext<'_>,
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
				ctx: &mut <Engine as ReasoningEngine>::PropagationContext<'_>,
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
		let var = slv
			.new_int_decision(0..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
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
		ExternalPropagator::notify_assignment(&mut *engine, &[imply.0, ge.0]);
		assert_eq!(*notifications.borrow(), 1);

		let propagated = ExternalPropagator::propagate(&mut *engine, &mut actions);
		assert_eq!(propagated, None);

		assert_eq!(*notifications.borrow(), 1);
	}
}
