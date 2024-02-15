use pindakaas::solver::{cadical::Cadical, PropagatingSolver};

use crate::{
	propagator::int_event::IntEvent,
	solver::{engine::PropRef, BoolView, IntView},
	Solver,
};

pub struct InitializationActions<'a> {
	pub(crate) prop_ref: PropRef,
	pub(crate) slv: &'a mut Solver,
}

impl InitializationActions<'_> {
	#[allow(dead_code)] // TODO
	pub fn subscribe_bool(&mut self, var: BoolView, data: u32) {
		let var = var.0.var();
		<Cadical as PropagatingSolver>::add_observed_var(&mut self.slv.core, var);
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
		}
	}
}
