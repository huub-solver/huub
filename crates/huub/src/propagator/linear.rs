use core::panic;

use tracing::trace;

use super::{reason::ReasonBuilder, ExplainActions, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{
		engine::queue::PriorityLevel,
		view::{BoolViewInner, IntViewInner},
		IntView,
	},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LinearLE {
	vars: Vec<IntView>,    // Variables in the linear inequality
	rhs: i64,              // Lower bound of the linear inequality
	action_list: Vec<u32>, // List of variables that have been modified since the last propagation
}

impl LinearLE {
	pub(crate) fn new<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		coeffs: &[i64],
		vars: VI,
		rhs: &i64,
	) -> Self {
		let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
		let mut max_sum = *rhs;
		let scaled_vars: Vec<IntView> = vars
			.iter()
			.enumerate()
			.filter_map(|(i, v)| {
				match v.0 {
				IntViewInner::Const(c) => {
					max_sum -= coeffs[i] * c;
					None
				}
				IntViewInner::VarRef(iv) => {
					Some(IntView(IntViewInner::Linear { var: iv, scale: coeffs[i] as i32, offset: 0 }))
				}
				_ => panic!("Unexpected IntViewInner variant from default conversion of vars in LinearLE::new()"),
			}
			})
			.collect();
		Self {
			vars: scaled_vars,
			rhs: max_sum,
			action_list: Vec::new(),
		}
	}
}

impl Propagator for LinearLE {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::UpperBound, i as u32)
		}
		!self.action_list.is_empty()
	}

	fn notify_event(&mut self, _: u32) -> bool {
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Low
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear()
	}

	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].lower_bound
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		// sum the coefficients x var.lower_bound
		let max_sum = self
			.vars
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.rhs, |sum, val| sum - val);
		// propagate the upper bound of the variables
		for (j, &v) in self.vars.iter().enumerate() {
			trace!(
				int_var = ?v,
				value = max_sum + actions.get_int_lower_bound(v),
				"bounds propagation linear_le",
			);
			let reason = ReasonBuilder::Lazy(j as u64);
			actions.set_int_upper_bound(v, max_sum + actions.get_int_lower_bound(v), &reason)?
		}
		Ok(())
	}

	fn explain(&mut self, actions: &mut dyn ExplainActions, data: u64) -> Conjunction {
		let i = data as usize;
		self.vars
			.iter()
			.enumerate()
			.filter_map(|(j, v)| if j == i { None } else { Some(v) })
			.filter_map(|v| {
				if let BoolView(BoolViewInner::Lit(lit)) = actions.get_int_upper_bound_lit(*v) {
					Some(lit)
				} else {
					None
				}
			})
			.collect()
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use pindakaas::{
		solver::{cadical::Cadical, SolveResult},
		Cnf,
	};

	use crate::{propagator::linear::LinearLE, solver::engine::int_var::IntVar, Solver, Value};

	#[test]
	fn test_linear_le_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(LinearLE::new(&[2, 1, 1], vec![a, b, c], &10));
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
			assert!(a_val * 2 + b_val + c_val <= 10)
		});
		assert_eq!(result, SolveResult::Sat)
	}

	#[test]
	fn test_linear_le_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(LinearLE::new(&[2, 1, 1], vec![a, b, c], &3));
		assert_eq!(slv.solve(|_| {}), SolveResult::Unsat)
	}

	#[test]
	fn test_linear_ge_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(LinearLE::new(&[-2, -1, -1], vec![a, b, c], &-3));
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
			assert!(a_val * 2 + b_val + c_val >= 3)
		});
		assert_eq!(result, SolveResult::Sat)
	}

	#[test]
	fn test_linear_ge_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(LinearLE::new(&[-2, -1, -1], vec![a, b, c], &-10));
		assert_eq!(slv.solve(|_| {}), SolveResult::Unsat)
	}
}
