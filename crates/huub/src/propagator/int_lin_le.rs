use pindakaas::Lit as RawLit;
use tracing::trace;

use super::{reason::ReasonBuilder, ExplainActions, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{
		engine::queue::PriorityLevel,
		value::{IntVal, NonZeroIntVal},
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, Conjunction,
};

// todo: consider using template for reified version of linear propagation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LinearLE {
	vars: Vec<IntView>,    // Variables in the linear inequality
	rhs: IntVal,           // Lower bound of the linear inequality
	reified: BoolView,     // Reified variable
	action_list: Vec<u32>, // List of variables that have been modified since the last propagation
}

impl LinearLE {
	pub(crate) fn new<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		coeffs: &[IntVal],
		vars: VI,
		mut max_sum: IntVal,
	) -> Self {
		let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
		let scaled_vars: Vec<IntView> = vars
			.iter()
			.enumerate()
			.filter_map(|(i, v)| {
				if let IntViewInner::Const(c) = v.0 {
					max_sum -= coeffs[i] * c;
					None
				} else if coeffs[i] != 0 {
					Some(*v * NonZeroIntVal::new(coeffs[i]).unwrap())
				} else {
					None
				}
			})
			.collect();
		Self {
			vars: scaled_vars,
			rhs: max_sum,
			reified: BoolView(BoolViewInner::Const(true)),
			action_list: Vec::new(),
		}
	}

	pub(crate) fn reify<B: Into<BoolView>>(mut self, reified: B) -> Self {
		self.reified = reified.into();
		self
	}
}

impl Propagator for LinearLE {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::UpperBound, i as u32)
		}

		if let BoolView(BoolViewInner::Lit(_)) = self.reified {
			actions.subscribe_bool(self.reified, self.vars.len() as u32)
		}

		!self.action_list.is_empty()
	}

	fn notify_event(&mut self, _: u32, _: &IntEvent) -> bool {
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
		// if the reified variable is false, skip propagation
		if !actions.get_bool_val(self.reified).unwrap_or(true) {
			return Ok(());
		}

		// get the difference between the right-hand-side value and the sum of variable lower bounds
		let max_sum = self
			.vars
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.rhs, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the right-hand-side value
		if let BoolView(BoolViewInner::Lit(lit)) = self.reified {
			if max_sum < 0 {
				let clause = self
					.vars
					.iter()
					.map(|v| actions.get_int_lower_bound_lit(*v))
					.collect();
				actions.set_bool_val(
					BoolView(BoolViewInner::Lit(lit)),
					false,
					&ReasonBuilder::Eager(clause),
				)?
			}
		}

		// skip the remaining propagation if the reified variable is not assigned to true
		if !actions.get_bool_val(self.reified).unwrap_or(false) {
			return Ok(());
		}

		// propagate the upper bound of the variables
		for (j, &v) in self.vars.iter().enumerate() {
			trace!(
				int_var = ?v,
				value = max_sum + actions.get_int_lower_bound(v),
				"bounds propagation linear_le",
			);
			let reason = ReasonBuilder::Lazy(j as u64);
			let ub = max_sum + actions.get_int_lower_bound(v);
			actions.set_int_upper_bound(v, ub, &reason)?
		}
		Ok(())
	}

	fn explain(&mut self, actions: &mut dyn ExplainActions, data: u64) -> Conjunction {
		let i = data as usize;
		let mut var_lits: Vec<RawLit> = self
			.vars
			.iter()
			.enumerate()
			.filter_map(|(j, v)| {
				if j == i {
					return None;
				}
				if let BoolView(BoolViewInner::Lit(lit)) = actions.get_int_lower_bound_lit(*v) {
					Some(lit)
				} else {
					None
				}
			})
			.collect();
		if let BoolView(BoolViewInner::Lit(lit)) = self.reified {
			var_lits.push(lit)
		}
		var_lits
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		propagator::int_lin_le::LinearLE, solver::engine::int_var::IntVar, Constraint, Model,
		Solver, Variable,
	};

	#[test]
	fn test_linear_le_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(LinearLE::new(&[2, 1, 1], vec![a, b, c], 6));

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 1, 1
			1, 1, 2
			1, 2, 1
			1, 2, 2
			2, 1, 1"#]],
		);
	}

	#[test]
	fn test_linear_le_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(LinearLE::new(&[2, 1, 1], vec![a, b, c], 3));
		slv.assert_unsatisfiable()
	}

	#[test]
	fn test_linear_ge_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(LinearLE::new(&[-2, -1, -1], vec![a, b, c], -6));
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 2, 2
			2, 1, 1
			2, 1, 2
			2, 2, 1
			2, 2, 2"#]],
		);
	}

	#[test]
	fn test_linear_ge_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(LinearLE::new(&[-2, -1, -1], vec![a, b, c], -10));
		slv.assert_unsatisfiable()
	}

	#[test]
	fn test_reified_linear_le_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::ReifiedIntLinLessEq(
			vec![2, 1, 1],
			vec![a.into(), b.into(), c.into()],
			5,
			r.into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
		let a = map.get(&Variable::Int(a));
		let b = map.get(&Variable::Int(b));
		let c = map.get(&Variable::Int(c));
		let r = map.get(&Variable::Bool(r));
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
    false, 1, 1, 1
    false, 1, 1, 2
    false, 1, 2, 1
    false, 1, 2, 2
    false, 2, 1, 1
    false, 2, 1, 2
    false, 2, 2, 1
    false, 2, 2, 2
    true, 1, 1, 1
    true, 1, 1, 2
    true, 1, 2, 1"#]],
		);
	}

	#[test]
	fn test_reified_linear_ge_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::ReifiedIntLinLessEq(
			vec![-2, -1, -1],
			vec![a.into(), b.into(), c.into()],
			-7,
			r.into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
		let a = map.get(&Variable::Int(a));
		let b = map.get(&Variable::Int(b));
		let c = map.get(&Variable::Int(c));
		let r = map.get(&Variable::Bool(r));
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
    false, 1, 1, 1
    false, 1, 1, 2
    false, 1, 2, 1
    false, 1, 2, 2
    false, 2, 1, 1
    false, 2, 1, 2
    false, 2, 2, 1
    false, 2, 2, 2
    true, 2, 1, 2
    true, 2, 2, 1
    true, 2, 2, 2"#]],
		);
	}
}
