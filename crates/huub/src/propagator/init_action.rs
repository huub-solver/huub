use pindakaas::solver::PropagatingSolver;

use crate::{
	propagator::int_event::IntEvent,
	solver::{engine::PropRef, BoolView, IntView, SatSolver},
	Solver,
};

pub struct InitializationActions<'a, Sat: SatSolver> {
	pub(crate) prop_ref: PropRef,
	pub(crate) slv: &'a mut Solver<Sat>,
}

impl<Sat: SatSolver> InitializationActions<'_, Sat> {
	#[allow(dead_code)] // TODO
	pub fn subscribe_bool(&mut self, var: BoolView, data: u32) {
		let var = var.0.var();
		<Sat as PropagatingSolver>::add_observed_var(&mut self.slv.core, var);
		self.slv
			.engine_mut()
			.bool_subscribers
			.entry(var)
			.or_default()
			.push((self.prop_ref, data))
	}

	pub fn subscribe_int(&mut self, var: IntView, event: IntEvent, data: u32) {
		use crate::solver::view::IntViewInner::*;

		match var.0 {
			VarRef(var) => self
				.slv
				.engine_mut()
				.int_subscribers
				.entry(var)
				.or_default()
				.push((self.prop_ref, event, data)),
			Const(_) => {}
		}
	}
}
