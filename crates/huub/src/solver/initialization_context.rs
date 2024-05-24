use delegate::delegate;
use pindakaas::{
	solver::{PropagatingSolver, PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use crate::{
	actions::{initialization::InitializationActions, inspection::InspectionActions},
	propagator::int_event::IntEvent,
	solver::{
		engine::{PropRef, TrailedInt},
		view::{BoolViewInner, IntViewInner},
		SatSolver,
	},
	BoolView, IntVal, IntView, Solver,
};

pub(crate) struct InitializationContext<'a, Sat: SatSolver + 'a>
where
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) prop: PropRef,
	pub(crate) slv: &'a mut Solver<Sat>,
}

impl<'a, Sol, Sat> InitializationActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	fn subscribe_bool(&mut self, var: BoolView, data: u32) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				<Sat as PropagatingSolver>::add_observed_var(&mut self.slv.oracle, lit.var());
				self.slv
					.engine_mut()
					.state
					.bool_subscribers
					.entry(lit.var())
					.or_default()
					.push((self.prop, data))
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32) {
		match var.0 {
			IntViewInner::VarRef(var) => self
				.slv
				.engine_mut()
				.state
				.int_subscribers
				.entry(var)
				.or_default()
				.push((self.prop, event, data)),
			IntViewInner::Const(_) => {}
			IntViewInner::Linear { transformer, var } => {
				if transformer.positive_scale() {
					self.subscribe_int(IntView(IntViewInner::VarRef(var)), event, data)
				} else {
					let reverse_event = match event {
						IntEvent::LowerBound => IntEvent::UpperBound,
						IntEvent::UpperBound => IntEvent::LowerBound,
						_ => event,
					};
					self.subscribe_int(IntView(IntViewInner::VarRef(var)), reverse_event, data)
				}
			}
			IntViewInner::Bool { lit, .. } => {
				self.subscribe_bool(BoolView(BoolViewInner::Lit(lit)), data)
			}
		}
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.slv.engine_mut().state.int_trail.track(init)
	}
}

impl<'a, Sol, Sat> InspectionActions for InitializationContext<'a, Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.slv.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}
