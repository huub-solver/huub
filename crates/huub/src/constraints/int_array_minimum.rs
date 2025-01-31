//! Structures and algorithms for the integer array minimum constraint, which
//! enforces that a decision variable takes the minimum value of an array of
//! decision variables.

use itertools::Itertools;

use crate::{
	actions::{
		ConstraintInitActions, ExplanationActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
	IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_minimum_int` constraint within a model.
///
/// This constraint enforces that an integer decision variable takes the minimum
/// value of an array of integer decision variables.
pub struct IntArrayMinimum {
	/// Set of decision variables from which the mimimum must be taken
	pub(crate) vars: Vec<IntDecision>,
	/// Decision variable that represents the minimum value
	pub(crate) min: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds cosistent propagator for the `array_minimum_int` constraint.
pub struct IntArrayMinimumBounds {
	/// Set of decision variables from which the mimimum must be taken
	vars: Vec<IntView>,
	/// Decision variable that represents the minimum value
	min: IntView,
}

impl<S: SimplificationActions> Constraint<S> for IntArrayMinimum {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for v in &self.vars {
			actions.simplify_on_change_int(*v);
		}
		actions.simplify_on_change_int(self.min);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let min_lb = self
			.vars
			.iter()
			.map(|&v| actions.get_int_lower_bound(v))
			.min()
			.unwrap();
		let min_ub = self
			.vars
			.iter()
			.map(|&v| actions.get_int_upper_bound(v))
			.min()
			.unwrap();
		actions.set_int_lower_bound(self.min, min_lb)?;
		actions.set_int_upper_bound(self.min, min_ub)?;

		let lb = actions.get_int_lower_bound(self.min);
		for &v in &self.vars {
			actions.set_int_lower_bound(v, lb)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		let min = slv.get_solver_int(self.min);
		IntArrayMinimumBounds::new_in(slv, vars, min);
		Ok(())
	}
}

impl IntArrayMinimumBounds {
	/// Create a new [`ArrayIntMinimumBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(solver: &mut P, vars: Vec<IntView>, min: IntView)
	where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				vars: vars.clone(),
				min,
			}),
			PriorityLevel::Low,
		);
		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
		solver.enqueue_on_int_change(prop, min, IntPropCond::LowerBound);
		solver.enqueue_now(prop);
	}
}

impl<P, E> Propagator<P, E> for IntArrayMinimumBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "array_int_minimum", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let min_lb = self
			.vars
			.iter()
			.map(|&x| actions.get_int_lower_bound(x))
			.min()
			.unwrap();
		let (min_ub, min_ub_var) =
			self.vars
				.iter()
				.fold((IntVal::MAX, self.min), |(ub, var), &e| {
					let e_ub = actions.get_int_upper_bound(e);
					if e_ub < ub {
						(e_ub, e)
					} else {
						(ub, var)
					}
				});
		// set y to be less than or equal to the minimum of upper bounds of x_i
		let reason = actions.get_int_upper_bound_lit(min_ub_var);
		actions.set_int_upper_bound(self.min, min_ub, reason)?;

		// set y to be greater than or equal to the minimum of lower bounds of x_i
		actions.set_int_lower_bound(self.min, min_lb, |a: &mut P| {
			self.vars
				.iter()
				.map(|&x| a.get_int_lit(x, IntLitMeaning::GreaterEq(min_lb)))
				.collect_vec()
		})?;

		// set x_i to be greater than or equal to y.lowerbound
		let reason = actions.get_int_lower_bound_lit(self.min);
		let y_lb = actions.get_int_lower_bound(self.min);
		for &x in self.vars.iter() {
			actions.set_int_lower_bound(x, y_lb, reason)?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{array_maximum_int, array_minimum_int, reformulate::InitConfig, Decision, Model};

	#[test]
	#[traced_test]
	fn test_maximum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((1..=6).into());
		let b = prb.new_int_var((3..=5).into());
		let c = prb.new_int_var((2..=5).into());
		let y = prb.new_int_var((1..=3).into());

		prb += array_maximum_int(vec![a, b, c], y);
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
			.collect_vec();

		slv.expect_solutions(
			&vars,
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
	#[traced_test]
	fn test_maximum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((13..=20).into());

		prb += array_maximum_int(vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_minimum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=4).into());
		let b = prb.new_int_var((2..=3).into());
		let c = prb.new_int_var((2..=3).into());
		let y = prb.new_int_var((3..=4).into());

		prb += array_minimum_int(vec![a, b, c], y);
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		3, 3, 3, 3
		4, 3, 3, 3"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_minimum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((1..=2).into());

		prb += array_minimum_int(vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}
}
