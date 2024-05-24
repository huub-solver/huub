use pindakaas::Lit as RawLit;

use super::{reason::ReasonBuilder, ExplanationActions, PropagationActions};
use crate::{
	actions::initialization::InitializationActions,
	helpers::opt_field::OptField,
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{
		engine::queue::PriorityLevel,
		poster::Poster,
		value::IntVal,
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct IntLinearLessEqBoundsImpl<const R: usize> {
	vars: Vec<IntView>,               // Variables in the linear inequality
	max: IntVal,                      // Lower bound of the linear inequality
	reification: OptField<R, RawLit>, // Reified variable
	action_list: Vec<u32>, // List of variables that have been modified since the last propagation
}

pub(crate) type IntLinearLessEqBounds = IntLinearLessEqBoundsImpl<0>;
pub(crate) type IntLinearLessEqImpBounds = IntLinearLessEqBoundsImpl<1>;

impl IntLinearLessEqBounds {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut max: IntVal,
	) -> impl Poster {
		IntLinearLessEqBoundsPoster::<0> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						max -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			max,
			reification: Default::default(),
		}
	}
}

impl IntLinearLessEqImpBounds {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut max: IntVal,
		r: RawLit,
	) -> impl Poster {
		IntLinearLessEqBoundsPoster::<1> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						max -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			max,
			reification: OptField::new(r),
		}
	}
}

impl<const B: usize> Propagator for IntLinearLessEqBoundsImpl<B> {
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
	#[tracing::instrument(name = "int_lin_le", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		// If the reified variable is false, skip propagation
		if let Some(r) = self.reification.get() {
			if !actions
				.get_bool_val(BoolView(BoolViewInner::Lit(*r)))
				.unwrap_or(true)
			{
				return Ok(());
			}
		}

		// get the difference between the right-hand-side value and the sum of variable lower bounds
		let sum = self
			.vars
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.max, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the right-hand-side value
		if let Some(r) = self.reification.get() {
			if sum < 0 {
				let clause = self
					.vars
					.iter()
					.map(|v| actions.get_int_lower_bound_lit(*v))
					.collect();
				actions.set_bool_val(
					BoolView(BoolViewInner::Lit(*r)),
					false,
					&ReasonBuilder::Eager(clause),
				)?
			}
		}

		// skip the remaining propagation if the reified variable is not assigned to true
		if let Some(r) = self.reification.get() {
			if !actions
				.get_bool_val(BoolView(BoolViewInner::Lit(*r)))
				.unwrap_or(false)
			{
				return Ok(());
			}
		}

		// propagate the upper bound of the variables
		for (j, &v) in self.vars.iter().enumerate() {
			let reason = ReasonBuilder::Lazy(j as u64);
			let ub = sum + actions.get_int_lower_bound(v);
			actions.set_int_upper_bound(v, ub, &reason)?
		}
		Ok(())
	}

	fn explain(&mut self, actions: &mut dyn ExplanationActions, data: u64) -> Conjunction {
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
		if let Some(r) = self.reification.get() {
			var_lits.push(*r)
		}
		var_lits
	}
}

struct IntLinearLessEqBoundsPoster<const R: usize> {
	vars: Vec<IntView>,
	max: IntVal,
	reification: OptField<R, RawLit>,
}
impl<const R: usize> Poster for IntLinearLessEqBoundsPoster<R> {
	fn post<I: InitializationActions>(self, actions: &mut I) -> (Box<dyn Propagator>, bool) {
		let prop = IntLinearLessEqBoundsImpl {
			vars: self.vars,
			max: self.max,
			reification: self.reification,
			action_list: Vec::new(),
		};
		for (i, v) in prop.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::UpperBound, i as u32)
		}
		if let Some(r) = prop.reification.get() {
			actions.subscribe_bool(BoolView(BoolViewInner::Lit(*r)), prop.vars.len() as u32)
		}
		(Box::new(prop), false)
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use super::IntLinearLessEqBounds;
	use crate::{solver::engine::int_var::IntVar, Constraint, Model, NonZeroIntVal, Solver};

	#[test]
	fn test_linear_le_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(IntLinearLessEqBounds::prepare(
			vec![a * NonZeroIntVal::new(2).unwrap(), b, c],
			6,
		));

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

		slv.add_propagator(IntLinearLessEqBounds::prepare(
			vec![a * NonZeroIntVal::new(2).unwrap(), b, c],
			3,
		));
		slv.assert_unsatisfiable()
	}

	#[test]
	fn test_linear_ge_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(IntLinearLessEqBounds::prepare(
			vec![a * NonZeroIntVal::new(-2).unwrap(), -b, -c],
			-6,
		));
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

		slv.add_propagator(IntLinearLessEqBounds::prepare(
			vec![a * NonZeroIntVal::new(-2).unwrap(), -b, -c],
			-10,
		));
		slv.assert_unsatisfiable()
	}

	#[test]
	fn test_reified_linear_le_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::IntLinLessEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(2).unwrap(),
				b.clone(),
				c.clone(),
			],
			5,
			r.clone().into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
		let a = map.get(&slv, &a.into());
		let b = map.get(&slv, &b.into());
		let c = map.get(&slv, &c.into());
		let r = map.get(&slv, &r.into());
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

		prb += Constraint::IntLinLessEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(-2).unwrap(),
				-b.clone(),
				-c.clone(),
			],
			-7,
			r.clone().into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
		let a = map.get(&slv, &a.into());
		let b = map.get(&slv, &b.into());
		let c = map.get(&slv, &c.into());
		let r = map.get(&slv, &r.into());
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
