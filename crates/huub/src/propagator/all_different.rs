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
