use super::{reason::ReasonBuilder, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{engine::queue::PriorityLevel, value::IntVal, view::IntView},
	LitMeaning,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Minimum {
	vars: Vec<IntView>,                // Variables in the minimum constraints
	y: IntView,                        // Variable that stores the minimum value
	action_list: Vec<(u32, IntEvent)>, // List of x variables that have been modified since the last propagation
	y_change: bool,                    // Whether the lower bound of y has been changed
}

impl Minimum {
	pub(crate) fn new<V: Into<IntView>, VI: IntoIterator<Item = V>>(vars: VI, y: IntView) -> Self {
		let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
		let sz = vars.len();
		Self {
			vars,
			y,
			action_list: Vec::with_capacity(sz),
			y_change: false,
		}
	}
}

impl Propagator for Minimum {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::UpperBound, i as u32);
			actions.subscribe_int(*v, IntEvent::LowerBound, i as u32);
		}
		actions.subscribe_int(self.y, IntEvent::LowerBound, self.vars.len() as u32);
		true
	}

	fn notify_event(&mut self, data: u32, event: &IntEvent) -> bool {
		if data == self.vars.len() as u32 {
			self.y_change = true;
		} else {
			self.action_list.push((data, event.clone()));
		}
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Low
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear();
		self.y_change = false;
	}

	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		if !self.action_list.is_empty() {
			let min_lb = self
				.vars
				.iter()
				.map(|&x| actions.get_int_lower_bound(x))
				.min()
				.unwrap();
			let (min_ub, min_ub_var) =
				self.vars
					.iter()
					.fold((IntVal::MAX, self.y), |(ub, var), &e| {
						let e_ub = actions.get_int_upper_bound(e);
						if e_ub < ub {
							(e_ub, e)
						} else {
							(ub, var)
						}
					});
			// set y to be less than or equal to the minimum of upper bounds of x_i
			actions.set_int_upper_bound(
				self.y,
				min_ub,
				&ReasonBuilder::Simple(actions.get_int_upper_bound_lit(min_ub_var)),
			)?;

			// set y to be greater than or equal to the minimum of lower bounds of x_i
			actions.set_int_lower_bound(
				self.y,
				min_lb,
				&ReasonBuilder::Eager(
					self.vars
						.iter()
						.map(|&x| actions.get_int_lit(x, LitMeaning::GreaterEq(min_lb)))
						.collect(),
				),
			)?;
		}

		// set x_i to be greater than or equal to y.lowerbound
		if self.y_change {
			let y_lb = actions.get_int_lower_bound(self.y);
			for &x in self.vars.iter() {
				actions.set_int_lower_bound(
					x,
					y_lb,
					&ReasonBuilder::Simple(actions.get_int_lower_bound_lit(self.y)),
				)?
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use std::ops::Neg;

	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		propagator::minimum::Minimum, solver::engine::int_var::IntVar, Constraint, Model, Solver,
	};

	#[test]
	fn test_minimum_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([3..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([2..=3]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([2..=3]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([3..=4]), true);

		slv.add_propagator(Minimum::new(vec![a, b, c], y));
		slv.expect_solutions(
			&[a, b, c, y],
			expect![[r#"
    3, 3, 3, 3
    4, 3, 3, 3"#]],
		);
	}

	#[test]
	fn test_minimum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((1..=2).into());

		prb += Constraint::Minimum(vec![a.into(), b.into(), c.into()], y.into());
		prb.assert_unsatisfiable();
	}

	#[test]
	fn test_maximum_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=6]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([3..=5]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([2..=5]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3]), true);

		slv.add_propagator(Minimum::new(vec![a.neg(), b.neg(), c.neg()], y.neg()));
		slv.expect_solutions(
			&[a, b, c, y],
			expect![[r#"
    1, 3, 2, 3
    1, 3, 3, 3
    2, 3, 2, 3
    2, 3, 3, 3
    3, 3, 2, 3
    3, 3, 3, 3"#]],
		);
	}

	#[test]
	fn test_maximum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((13..=20).into());

		prb += Constraint::Maximum(vec![a.into(), b.into(), c.into()], y.into());
		prb.assert_unsatisfiable();
	}
}
