//! Structures and algorithms for the integer array minimum constraint, which
//! enforces that a decision variable takes the minimum value of an array of
//! decision variables.

use std::ops::AddAssign;

use itertools::Itertools;

use crate::{
	actions::{PostingActions, ReasoningEngine, ReformulationActions},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `array_minimum_int` constraint.
pub struct IntArrayMinimumBounds<I1, I2> {
	/// Set of decision variables from which the minimum must be taken
	pub(crate) vars: Vec<I1>,
	/// Decision variable that represents the minimum value
	pub(crate) min: I2,
}

impl<E, I1, I2> Constraint<E> for IntArrayMinimumBounds<I1, I2>
where
	E: ReasoningEngine,
	I1: ModelIntView<E>,
	I2: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if self.min.get_val(ctx).is_some() && self.vars.iter().all(|v| v.get_val(ctx).is_some()) {
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self
			.vars
			.iter()
			.map(|v| slv.get_solver_int(v.clone().into()))
			.collect();
		let min = slv.get_solver_int(self.min.clone().into());
		IntArrayMinimumBounds::new_in(slv, vars, min);
		Ok(())
	}
}

impl IntArrayMinimumBounds<IntView, IntView> {
	/// Create a new [`ArrayIntMinimumBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(solver: &mut E, vars: Vec<IntView>, min: IntView)
	where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self {
			vars: vars.clone(),
			min,
		});
	}
}

impl<E, I1, I2> Propagator<E> for IntArrayMinimumBounds<I1, I2>
where
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		for v in &self.vars {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
		self.min.enqueue_when(ctx, IntPropCond::LowerBound);
	}

	#[tracing::instrument(name = "array_int_minimum", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// set y to be less than or equal to the minimum of upper bounds of x_i
		let (min_ub, min_ub_var) = self
			.vars
			.iter()
			.map(|x| (x.get_upper_bound(ctx), x))
			.min_by_key(|(ub, _)| *ub)
			.unwrap();
		let reason = min_ub_var.get_upper_bound_lit(ctx);
		self.min.set_upper_bound(ctx, min_ub, [reason])?;

		// set y to be greater than or equal to the minimum of lower bounds of x_i
		let min_lb = self
			.vars
			.iter()
			.map(|x| x.get_lower_bound(ctx))
			.min()
			.unwrap();
		self.min
			.set_lower_bound(ctx, min_lb, |ctx: &mut E::PropagationCtx<'_>| {
				self.vars
					.iter()
					.map(|x| x.get_lit(ctx, IntLitMeaning::GreaterEq(min_lb)))
					.collect_vec()
			})?;

		// set x_i to be greater than or equal to y.lowerbound
		let reason = &[self.min.get_lower_bound_lit(ctx)];
		let y_lb = self.min.get_lower_bound(ctx);
		for x in self.vars.iter() {
			x.set_lower_bound(ctx, y_lb, reason)?;
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
		let a = prb.new_int_var(1..=6);
		let b = prb.new_int_var(3..=5);
		let c = prb.new_int_var(2..=5);
		let y = prb.new_int_var(1..=3);

		array_maximum_int(&mut prb, vec![a, b, c], y);
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
		let a = prb.new_int_var(3..=5);
		let b = prb.new_int_var(4..=5);
		let c = prb.new_int_var(4..=10);
		let y = prb.new_int_var(13..=20);

		array_maximum_int(&mut prb, vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_minimum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_var(3..=4);
		let b = prb.new_int_var(2..=3);
		let c = prb.new_int_var(2..=3);
		let y = prb.new_int_var(3..=4);

		array_minimum_int(&mut prb, vec![a, b, c], y);
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
		let a = prb.new_int_var(3..=5);
		let b = prb.new_int_var(4..=5);
		let c = prb.new_int_var(4..=10);
		let y = prb.new_int_var(1..=2);

		array_minimum_int(&mut prb, vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}
}
