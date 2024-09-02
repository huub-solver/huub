use delegate::delegate;
use pindakaas::{
	solver::{PropagatingSolver, PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use crate::{
	actions::{
		decision::DecisionActions, initialization::InitializationActions,
		inspection::InspectionActions, trailing::TrailingActions,
	},
	propagator::int_event::IntEvent,
	solver::{
		engine::{int_var::IntVarRef, trail::TrailedInt, PropRef},
		view::{BoolViewInner, IntViewInner},
		SatSolver,
	},
	BoolView, IntVal, IntView, LitMeaning, Solver,
};

/// Reference to the construct that we are intilizing
pub(crate) enum InitRef {
	// a brancher
	Brancher,
	// a specific propagator
	Propagator(PropRef),
}

pub(crate) struct InitializationContext<'a, Sat: SatSolver + 'a>
where
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) init_ref: InitRef,
	pub(crate) slv: &'a mut Solver<Sat>,
}

impl<'a, Sol, Sat> InitializationActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), crate::ReformulationError> {
		self.slv.add_clause(clause)
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.slv.engine_mut().state.trail.track_int(init)
	}

	fn subscribe_bool(&mut self, var: BoolView, data: u32) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				<Sat as PropagatingSolver>::add_observed_var(&mut self.slv.oracle, lit.var());
				if let InitRef::Propagator(prop) = self.init_ref {
					self.slv
						.engine_mut()
						.state
						.bool_subscribers
						.entry(lit.var())
						.or_default()
						.push((prop, data))
				}
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32) {
		let mut subscribe_intref = |var, prop, event| {
			self.slv
				.engine_mut()
				.state
				.int_subscribers
				.entry(var)
				.or_default()
				.push((prop, event, data))
		};
		match (&self.init_ref, var.0) {
			(InitRef::Propagator(prop), IntViewInner::VarRef(var)) => {
				subscribe_intref(var, *prop, event);
			}
			(InitRef::Propagator(prop), IntViewInner::Linear { transformer, var }) => {
				let event = if transformer.positive_scale() {
					event
				} else {
					match event {
						IntEvent::LowerBound => IntEvent::UpperBound,
						IntEvent::UpperBound => IntEvent::LowerBound,
						_ => event,
					}
				};
				subscribe_intref(var, *prop, event);
			}
			(_, IntViewInner::Const(_)) => {} // ignore
			(_, IntViewInner::Bool { lit, .. }) => {
				self.subscribe_bool(BoolView(BoolViewInner::Lit(lit)), data)
			}
			(InitRef::Brancher, _) => {} // ignore: branchers don't receive notifications, and contained literals are already observed.
		}
	}
}

impl<'a, Sol, Sat> TrailingActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.slv.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
		}
		to self.slv.engine_mut().state {
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

impl<'a, Sol, Sat> InspectionActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.slv.engine().state {
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl<'a, Sol, Sat> DecisionActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.slv {
			fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;
		}
	}
}
