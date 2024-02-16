use crate::{
	propagator::{
		init_action::InitializationActions, int_event::IntEvent,
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

	fn notify(&mut self, data: u32) -> Option<PriorityLevel> {
		self.action_list.push(data);
		Some(PriorityLevel::Low)
	}

	fn propagate(&mut self, actions: &mut PropagationActions<'_>) {
		while let Some(i) = self.action_list.pop() {
			let var = self.vars[i as usize];
			let val = actions.int_get_val(var).unwrap();
			let lit = actions.int_get_bool_lit(var, BoolVarMap::Eq(val));
			for (j, &v) in self.vars.iter().enumerate() {
				if (j as u32) != i && actions.int_get_val(v).is_none() {
					actions.int_neq_val(v, val, Reason::Simple(lit))
				}
			}
		}
	}
}

mod tests {
    #[test]
	fn test_all_different_value_sat() {
		use super::*; 
		use flatzinc_serde::RangeList;
		use crate::solver::engine::int_var::IntVar; 
		use pindakaas::Cnf;

		let mut slv = Cnf::default().into(); 
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4])); 
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4])); 
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4])); 

		slv.add_propagator(Box::new(AllDifferentValue::new(vec![a, b, c])));
		slv.solve(|val| {
			assert_ne!(val(a.into()), val(b.into()));
			assert_ne!(val(b.into()), val(c.into()));
			assert_ne!(val(a.into()), val(c.into()));
		})
	}

	#[test]
	fn test_all_different_value_unsat() {
		use super::*; 
		use flatzinc_serde::RangeList;
		use crate::solver::engine::int_var::IntVar; 
		use pindakaas::Cnf;

		let mut slv = Cnf::default().into(); 
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2])); 
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2])); 
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2])); 

		slv.add_propagator(Box::new(AllDifferentValue::new(vec![a, b, c])));
		slv.solve(|val| {
			assert_ne!(val(a.into()), val(b.into()));
			assert_ne!(val(b.into()), val(c.into()));
			assert_ne!(val(a.into()), val(c.into()));
		})
	}
}