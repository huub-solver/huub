use super::{reason::ReasonBuilder, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{engine::queue::PriorityLevel, value::IntVal, view::IntView},
	LitMeaning,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArrayIntElementBounds {
	vars: Vec<IntView>,                // Variables to be selected
	y: IntView,                        // The selected variable
	idx: IntView,                      // Variable that stores the index of the selected variable
	action_list: Vec<(u32, IntEvent)>, // List of x variables that have been modified since the last propagation
}

impl ArrayIntElementBounds {
	pub(crate) fn new<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		y: IntView,
		idx: IntView,
	) -> Self {
		let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
		let sz = vars.len();
		Self {
			vars,
			y,
			idx,
			action_list: Vec::with_capacity(sz),
		}
	}
}

impl Propagator for ArrayIntElementBounds {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Bounds, i as u32);
		}
		actions.subscribe_int(self.y, IntEvent::Bounds, self.vars.len() as u32);
		actions.subscribe_int(self.idx, IntEvent::Domain, self.vars.len() as u32 + 1);
		true
	}

	fn notify_event(&mut self, _: u32, _: &IntEvent) -> bool {
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Low
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear();
	}

	#[tracing::instrument(name = "array_int_element", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		let idx_is_fixed =
			actions.get_int_lower_bound(self.idx) == actions.get_int_upper_bound(self.idx);
		if idx_is_fixed {
			let fixed_idx = actions.get_int_lower_bound(self.idx);
			// propagate only when the fixed index is not out of bound
			if fixed_idx >= 0 && fixed_idx < self.vars.len() as IntVal {
				let fixed_var = self.vars[fixed_idx as usize];
				actions.set_int_lower_bound(
					self.y,
					actions.get_int_lower_bound(fixed_var),
					&ReasonBuilder::Eager(vec![
						actions.get_int_lit(self.idx, LitMeaning::Eq(fixed_idx)),
						actions.get_int_lower_bound_lit(fixed_var),
					]),
				)?;
				actions.set_int_lower_bound(
					fixed_var,
					actions.get_int_lower_bound(self.y),
					&ReasonBuilder::Eager(vec![
						actions.get_int_lit(self.idx, LitMeaning::Eq(fixed_idx)),
						actions.get_int_lower_bound_lit(self.y),
					]),
				)?;
				actions.set_int_upper_bound(
					self.y,
					actions.get_int_upper_bound(self.y),
					&ReasonBuilder::Eager(vec![
						actions.get_int_lit(self.idx, LitMeaning::Eq(fixed_idx)),
						actions.get_int_upper_bound_lit(fixed_var),
					]),
				)?;
				actions.set_int_upper_bound(
					fixed_var,
					actions.get_int_upper_bound(self.y),
					&ReasonBuilder::Eager(vec![
						actions.get_int_lit(self.idx, LitMeaning::Eq(fixed_idx)),
						actions.get_int_upper_bound_lit(self.y),
					]),
				)?;
				return Ok(());
			}
		}

		// remove values from the index variable when:
		// 1. y.upper_bound < self.vars[i].lower_bound -> idx != i
		// 2. y.lower_bound > self.vars[i].upper_bound -> idx != i
		let y_lb = actions.get_int_lower_bound(self.y);
		let y_ub = actions.get_int_upper_bound(self.y);
		for (i, v) in self.vars.iter().enumerate() {
			if actions.check_int_in_domain(self.idx, i as IntVal) {
				let v_lb = actions.get_int_lower_bound(*v);
				let v_ub = actions.get_int_upper_bound(*v);
				if y_ub < v_lb {
					actions.set_int_not_eq(
						self.idx,
						i as IntVal,
						&ReasonBuilder::Eager(vec![
							actions.get_int_lit(self.y, LitMeaning::Less(v_lb)),
							actions.get_int_lower_bound_lit(*v),
						]),
					)?;
				}
				if v_ub < y_lb {
					actions.set_int_not_eq(
						self.idx,
						i as IntVal,
						&ReasonBuilder::Eager(vec![
							actions.get_int_lit(self.y, LitMeaning::GreaterEq(v_ub + 1)),
							actions.get_int_upper_bound_lit(*v),
						]),
					)?;
				}
			}
		}

		// propagate the lower bound of the selected variable y
		// y.lower_bound >= min(i in domain(x))(self.vars[i].lower_bound)
		let mut min_lb = IntVal::MAX;
		for (i, v) in self.vars.iter().enumerate() {
			if actions.check_int_in_domain(self.idx, i as IntVal) {
				let v_lb = actions.get_int_lower_bound(*v);
				if v_lb < min_lb {
					min_lb = v_lb;
					if min_lb <= y_lb {
						break;
					}
				}
			}
		}
		if min_lb > y_lb {
			actions.set_int_lower_bound(
				self.y,
				min_lb,
				&ReasonBuilder::Eager(
					self.vars
						.iter()
						.enumerate()
						.map(|(i, &v)| {
							if actions.check_int_in_domain(self.idx, i as IntVal) {
								actions.get_int_lit(v, LitMeaning::GreaterEq(min_lb))
							} else {
								actions.get_int_lit(self.idx, LitMeaning::NotEq(i as IntVal))
							}
						})
						.collect(),
				),
			)?;
		}

		// propagate the upper bound of the selected variable y
		// y.upper_bound <= max(i in domain(x))(self.vars[i].upper_bound)
		let mut max_ub = IntVal::MIN;
		for (i, v) in self.vars.iter().enumerate() {
			if actions.check_int_in_domain(self.idx, i as IntVal) {
				let v_ub = actions.get_int_upper_bound(*v);
				if v_ub > max_ub {
					max_ub = v_ub;
					if max_ub >= y_ub {
						break;
					}
				}
			}
		}
		if max_ub < y_ub {
			actions.set_int_upper_bound(
				self.y,
				max_ub,
				&ReasonBuilder::Eager(
					self.vars
						.iter()
						.enumerate()
						.map(|(i, &v)| {
							if actions.check_int_in_domain(self.idx, i as IntVal) {
								actions.get_int_lit(v, LitMeaning::Less(max_ub + 1))
							} else {
								actions.get_int_lit(self.idx, LitMeaning::NotEq(i as IntVal))
							}
						})
						.collect(),
				),
			)?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		propagator::array_int_element::ArrayIntElementBounds, solver::engine::int_var::IntVar,
		Constraint, Model, Solver,
	};

	#[test]
	fn test_element_bounds_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([3..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([2..=3]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([4..=5]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([3..=4]), true);
		let idx = IntVar::new_in(&mut slv, RangeList::from_iter([0..=2]), true);

		slv.add_propagator(ArrayIntElementBounds::new(vec![a, b, c], y, idx));
		slv.expect_solutions(
			&[idx, y, a, b, c],
			expect![[r#"
    0, 3, 3, 2, 4
    0, 3, 3, 2, 5
    0, 3, 3, 3, 4
    0, 3, 3, 3, 5
    0, 4, 4, 2, 4
    0, 4, 4, 2, 5
    0, 4, 4, 3, 4
    0, 4, 4, 3, 5
    1, 3, 3, 3, 4
    1, 3, 3, 3, 5
    1, 3, 4, 3, 4
    1, 3, 4, 3, 5
    2, 4, 3, 2, 4
    2, 4, 3, 3, 4
    2, 4, 4, 2, 4
    2, 4, 4, 3, 4"#]],
		);
	}

	#[test]
	fn test_element_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((1..=2).into());
		let idx = prb.new_int_var((0..=2).into());

		prb += Constraint::ArrayIntElement(vec![a, b, c], y, idx);
		prb.assert_unsatisfiable();
	}
}
