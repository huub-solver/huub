use std::any::Any;

use pindakaas::solver::Propagator as IpasirPropagator;

#[derive(Default)]
pub struct PropagationLayer {}

impl IpasirPropagator for PropagationLayer {
	fn is_lazy(&self) -> bool {
		false
	}

	fn notify_assignment(&mut self, var: pindakaas::Var, val: bool, persistent: bool) {
		let _ = var;
		let _ = val;
		let _ = persistent;
	}

	fn notify_new_decision_level(&mut self) {}

	fn notify_backtrack(&mut self, new_level: usize) {
		let _ = new_level;
	}

	fn check_model(&mut self, value: &dyn pindakaas::Valuation) -> bool {
		let _ = value;
		true
	}

	fn decide(&mut self) -> Option<pindakaas::Lit> {
		None
	}

	fn propagate(
		&mut self,
		slv: &mut dyn pindakaas::solver::SolvingActions,
	) -> Vec<pindakaas::Lit> {
		let _ = slv;
		Vec::new()
	}

	fn add_reason_clause(&mut self, propagated_lit: pindakaas::Lit) -> Vec<pindakaas::Lit> {
		let _ = propagated_lit;
		Vec::new()
	}

	fn add_external_clause(&mut self) -> Option<Vec<pindakaas::Lit>> {
		None
	}

	fn as_any(&self) -> &dyn Any {
		self
	}

	fn as_mut_any(&mut self) -> &mut dyn Any {
		self
	}
}
