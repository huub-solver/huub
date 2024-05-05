use super::{reason::ReasonBuilder, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{engine::queue::PriorityLevel, value::IntVal, view::IntView},
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
			let (min_upper_bound, min_lower_bound) =
				self.vars
					.iter()
					.fold((IntVal::MAX, IntVal::MAX), |(min_ub, min_lb), x| {
						let x_ub = actions.get_int_upper_bound(*x);
						let x_lb = actions.get_int_lower_bound(*x);
						(min_ub.min(x_ub), min_lb.min(x_lb))
					});
			// set y to be less than or equal to the minimum of upper bounds of x_i
			if actions.get_int_upper_bound(self.y) > min_upper_bound {
				actions.set_int_upper_bound(
					self.y,
					min_upper_bound,
					&ReasonBuilder::Eager(
						self.vars
							.iter()
							.map(|x| actions.get_int_less_than_equal_to_lit(*x, min_upper_bound))
							.collect(),
					),
				)?;
			}

			// set y to be greater than or equal to the minimum of lower bounds of x_i
			if actions.get_int_lower_bound(self.y) < min_lower_bound {
				actions.set_int_lower_bound(
					self.y,
					min_lower_bound,
					&ReasonBuilder::Eager(
						self.vars
							.iter()
							.map(|x| actions.get_int_greater_than_equal_to_lit(*x, min_lower_bound))
							.collect(),
					),
				)?;
			}
		}

		// set x_i to be greater than or equal to y.lowerbound
		if self.y_change {
			let y_lb = actions.get_int_lower_bound(self.y);
			for &x in self.vars.iter() {
				actions.set_int_lower_bound(
					x,
					y_lb,
					&ReasonBuilder::Simple(actions.get_int_upper_bound_lit(self.y)),
				)?
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use pindakaas::{
		solver::{cadical::Cadical, SolveResult},
		Cnf,
	};

	use crate::{propagator::minimum::Minimum, solver::engine::int_var::IntVar, Solver, Value};

	#[test]
	fn test_minimum_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(Minimum::new(vec![a, b, c], y));
		let result = slv.solve(|val| {
			let Value::Int(a_val) = val(a.into()).unwrap() else {
				panic!()
			};
			let Value::Int(b_val) = val(b.into()).unwrap() else {
				panic!()
			};
			let Value::Int(c_val) = val(c.into()).unwrap() else {
				panic!()
			};
			let Value::Int(y_val) = val(y.into()).unwrap() else {
				panic!()
			};

			assert!(a_val.min(b_val).min(c_val) == y_val)
		});
		assert_eq!(result, SolveResult::Sat)
	}

	#[test]
	fn test_minimum_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([3..=5]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([4..=5]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([4..=10]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(Minimum::new(vec![a, b, c], y));
		assert_eq!(slv.solve(|_| {}), SolveResult::Unsat)
	}

	#[test]
	fn test_maximum_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(Minimum::new(
			vec![a.negated(), b.negated(), c.negated()],
			y.negated(),
		));
		let result = slv.solve(|val| {
			let Value::Int(a_val) = val(a.into()).unwrap() else {
				panic!()
			};
			let Value::Int(b_val) = val(b.into()).unwrap() else {
				panic!()
			};
			let Value::Int(c_val) = val(c.into()).unwrap() else {
				panic!()
			};
			let Value::Int(y_val) = val(y.into()).unwrap() else {
				panic!()
			};

			assert!(a_val.max(b_val).max(c_val) == y_val)
		});
		assert_eq!(result, SolveResult::Sat)
	}

	#[test]
	fn test_maximum_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([3..=5]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([4..=5]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([4..=10]), true);
		let y = IntVar::new_in(&mut slv, RangeList::from_iter([13..=20]), true);

		slv.add_propagator(Minimum::new(
			vec![a.negated(), b.negated(), c.negated()],
			y.negated(),
		));
		assert_eq!(slv.solve(|_| {}), SolveResult::Unsat)
	}
}
