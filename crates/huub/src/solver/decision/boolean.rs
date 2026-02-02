//! Boolean decision variable definitions for the solver layer.

use std::ops::Not;

use pindakaas::Lit as RawLit;

use crate::{
	actions::BoolInspectionActions,
	solver::{
		Solver,
		decision::{Decision, DecisionReference, private},
		engine::State,
		trail::Trail,
	},
};

impl Decision<bool> {
	/// Return whether this decision represents a negated literal.
	pub(crate) fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
}

impl<Sat> BoolInspectionActions<Solver<Sat>> for Decision<bool> {
	fn val(&self, ctx: &Solver<Sat>) -> Option<bool> {
		self.val(&ctx.engine.borrow().state)
	}
}

impl BoolInspectionActions<State> for Decision<bool> {
	fn val(&self, ctx: &State) -> Option<bool> {
		self.val(&ctx.trail)
	}
}

impl BoolInspectionActions<Trail> for Decision<bool> {
	fn val(&self, ctx: &Trail) -> Option<bool> {
		ctx.sat_value(self.0)
	}
}

impl Not for Decision<bool> {
	type Output = Self;

	fn not(self) -> Self::Output {
		Decision(!self.0)
	}
}

impl DecisionReference for bool {
	type Ref = RawLit;
}
impl private::Sealed for bool {}
