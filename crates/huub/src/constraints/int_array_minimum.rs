//! Structures and algorithms for the integer array minimum constraint, which
//! enforces that a decision variable takes the minimum value of an array of
//! decision variables.

use itertools::Itertools;

use crate::{
	actions::{InitActions, PostingActions, ReasoningEngine},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `array_minimum_int` constraint.
pub struct IntArrayMinimumBounds<I1, I2> {
	/// Set of decision variables from which the minimum must be taken
	pub(crate) vars: Vec<I1>,
	/// Decision variable that represents the minimum value
	pub(crate) min: I2,
}

impl<I1, I2> IntArrayMinimumBounds<I1, I2> {
	/// Create a new [`IntArrayMinimumBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I1>, min: I2)
	where
		E: PostingActions + ?Sized,
		I1: IntSolverActions<Engine>,
		I2: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self {
			vars: vars.clone(),
			min,
		}));
	}
}

impl<E, I1, I2> Constraint<E> for IntArrayMinimumBounds<I1, I2>
where
	E: ReasoningEngine,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if let Some(c) = self.min.val(ctx)
			&& self.vars.iter().any(|v| v.val(ctx) == Some(c))
		{
			for v in &self.vars {
				v.tighten_min(ctx, c, [self.min.min_lit(ctx)])?;
			}
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let vars: Vec<_> = self
			.vars
			.iter()
			.map(|v| slv.solver_view(v.clone().into()))
			.collect();
		let min = slv.solver_view(self.min.clone().into());
		IntArrayMinimumBounds::post(slv, vars, min);
		Ok(())
	}
}

impl<E, I1, I2> Propagator<E> for IntArrayMinimumBounds<I1, I2>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
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
			.map(|x| (x.max(ctx), x))
			.min_by_key(|(ub, _)| *ub)
			.unwrap();
		let reason = min_ub_var.max_lit(ctx);
		self.min.tighten_max(ctx, min_ub, [reason])?;

		// set y to be greater than or equal to the minimum of lower bounds of x_i
		let min_lb = self.vars.iter().map(|x| x.min(ctx)).min().unwrap();
		self.min
			.tighten_min(ctx, min_lb, |ctx: &mut E::PropagationCtx<'_>| {
				self.vars
					.iter()
					.map(|x| x.lit(ctx, IntLitMeaning::GreaterEq(min_lb)))
					.collect_vec()
			})?;

		// set x_i to be greater than or equal to y.lowerbound
		let reason = &[self.min.min_lit(ctx)];
		let y_lb = self.min.min(ctx);
		for x in self.vars.iter() {
			x.tighten_min(ctx, y_lb, reason)?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{Model, lower::InitConfig};

	#[test]
	#[traced_test]
	fn test_maximum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(1..=6);
		let b = prb.new_int_decision(3..=5);
		let c = prb.new_int_decision(2..=5);
		let y = prb.new_int_decision(1..=3);

		prb.maximum(vec![a, b, c]).result(y).post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, x))
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
		let a = prb.new_int_decision(3..=5);
		let b = prb.new_int_decision(4..=5);
		let c = prb.new_int_decision(4..=10);
		let y = prb.new_int_decision(13..=20);

		prb.maximum(vec![a, b, c]).result(y).post();
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_minimum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(3..=4);
		let b = prb.new_int_decision(2..=3);
		let c = prb.new_int_decision(2..=3);
		let y = prb.new_int_decision(3..=4);

		prb.minimum(vec![a, b, c]).result(y).post();
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, x))
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
		let a = prb.new_int_decision(3..=5);
		let b = prb.new_int_decision(4..=5);
		let c = prb.new_int_decision(4..=10);
		let y = prb.new_int_decision(1..=2);

		prb.minimum(vec![a, b, c]).result(y).post();
		prb.assert_unsatisfiable();
	}
}
