use crate::{
	propagator::{
		conflict::Conflict, init_action::InitializationActions, int_event::IntEvent,
		propagation_action::PropagationActions, reason::Reason, Propagator,
	},
	solver::{
		engine::{int_var::BoolVarMap, queue::PriorityLevel},
		IntView,
	},
};

#[derive(Debug)]
pub struct AllDifferentValue {
	vars: Vec<IntView>,
	action_list: Vec<u32>,
}

impl AllDifferentValue {
	pub fn new<V: Into<IntView>, I: IntoIterator<Item = V>>(vars: I) -> Self {
		Self {
			vars: vars.into_iter().map(Into::into).collect(),
			action_list: Vec::new(),
		}
	}
}

impl Propagator for AllDifferentValue {
	fn initialize(&mut self, actions: &mut InitializationActions<'_>) {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Fixed, i as u32)
		}
	}

	fn notify_event(&mut self, data: u32) -> Option<PriorityLevel> {
		self.action_list.push(data);
		Some(PriorityLevel::Low)
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear()
	}

	fn propagate(&mut self, actions: &mut PropagationActions<'_>) -> Result<(), Conflict> {
		while let Some(i) = self.action_list.pop() {
			let var = self.vars[i as usize];
			let val = actions.int_get_val(var).unwrap();
			let lit = actions.int_get_bool_lit(var, BoolVarMap::Eq(val));
			for (j, &v) in self.vars.iter().enumerate() {
				let j_val = actions.int_get_val(v);
				if (j as u32) != i && (j_val.is_none() || j_val.unwrap() == val) {
					actions.int_neq_val(v, val, Reason::Simple(lit))?
				}
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::SolveResult, Cnf};

	use super::*;
	use crate::solver::engine::int_var::IntVar;

	#[test]
	fn test_all_different_value_sat() {
		let mut slv = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]));
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]));
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]));

		slv.add_propagator(Box::new(AllDifferentValue::new(vec![a, b, c])));
		assert_eq!(
			slv.solve(|val| {
				assert_ne!(val(a.into()), val(b.into()));
				assert_ne!(val(b.into()), val(c.into()));
				assert_ne!(val(a.into()), val(c.into()));
			}),
			SolveResult::Sat
		)
	}

	#[test]
	fn test_all_different_value_unsat() {
		let mut slv = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]));
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]));
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]));

		slv.add_propagator(Box::new(AllDifferentValue::new(vec![a, b, c])));
		assert_eq!(slv.solve(|_| { assert!(false) }), SolveResult::Unsat)
	}
}
