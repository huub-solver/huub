use pindakaas::{
	solver::{PropagatingSolver, PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use super::{
	engine::PropRef,
	view::{BoolViewInner, IntViewInner},
	SatSolver,
};
use crate::{
	propagator::{int_event::IntEvent, InitializationActions},
	BoolView, IntView, Solver,
};

pub(crate) struct InitializationContext<'a, Sat: SatSolver>
where
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) prop: PropRef,
	pub(crate) slv: &'a mut Solver<Sat>,
}

impl<'a, Sol: PropagatorAccess + SatValuation, Sat: SatSolver + SolverTrait<ValueFn = Sol>>
	InitializationActions for InitializationContext<'a, Sat>
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
			IntViewInner::Linear { var, scale, .. } => {
				if scale > 0 {
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
		}
	}
}
