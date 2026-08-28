//! Structures and algorithms for the integer array minimum constraint, which
//! enforces that a decision variable takes the minimum value of an array of
//! decision variables.

use crate::{
	DeepClone,
	actions::{InitActions, IntPropCond, PostingActions, ReasonActions, ReasoningEngine},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	solver::{IntLitMeaning, engine::Engine, queue::PriorityLevel},
};

/// Bounds consistent propagator for the `array_minimum_int` constraint.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
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
	I2: IntModelActions<E> + Into<I1>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		// Filter out variables that are too large to be the minimum
		let max_min = self.min.max(ctx);
		self.vars.retain(|v| v.min(ctx) <= max_min);
		debug_assert!(!self.vars.is_empty());

		// If there is only one variable left, unify it with the minimum value and
		// subsume the constraint.
		if self.vars.len() == 1 {
			self.vars[0].unify(ctx, self.min.clone())?;
			return Ok(SimplificationStatus::Subsumed);
		}

		// If the minimum value is known and one of the variables is equal to it,
		// tighten the minimum bounds of the others and subsume the constraint.
		if let Some(c) = self.min.val(ctx)
			&& self.vars.iter().any(|v| v.val(ctx) == Some(c))
		{
			for v in &self.vars {
				v.tighten_min(ctx, c, |ctx, reason| reason.push(self.min.min_lit(ctx)))?;
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
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		for v in &self.vars {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
		self.min.enqueue_when(ctx, IntPropCond::LowerBound);
	}

	#[tracing::instrument(
		name = "int_array_minimum_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// set y to be less than or equal to the minimum of upper bounds of x_i
		let (min_ub, min_ub_var) = self
			.vars
			.iter()
			.map(|x| (x.max(ctx), x))
			.min_by_key(|(ub, _)| *ub)
			.unwrap();
		self.min.tighten_max(ctx, min_ub, |ctx, reason| {
			reason.push(min_ub_var.max_lit(ctx));
		})?;

		// set y to be greater than or equal to the minimum of lower bounds of x_i
		let min_lb = self.vars.iter().map(|x| x.min(ctx)).min().unwrap();
		self.min.tighten_min(ctx, min_lb, |ctx, reason| {
			reason.extend(
				self.vars
					.iter()
					.map(|x| x.lit(ctx, IntLitMeaning::GreaterEq(min_lb))),
			);
		})?;

		// set x_i to be greater than or equal to y.lowerbound
		let y_lb = self.min.min(ctx);
		for x in self.vars.iter() {
			x.tighten_min(ctx, y_lb, |ctx, reason| reason.push(self.min.min_lit(ctx)))?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::model::Model;

	#[test]
	#[traced_test]
	fn test_maximum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(1..=6);
		let b = prb.new_int_decision(3..=5);
		let c = prb.new_int_decision(2..=5);
		let y = prb.new_int_decision(1..=3);

		prb.maximum(vec![a, b, c]).result(y).post().unwrap();

		let (mut slv, map) = prb.lower().to_solver().unwrap();
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

		assert!(prb.maximum(vec![a, b, c]).result(y).post().is_err());
	}

	#[test]
	#[traced_test]
	fn test_minimum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(3..=4);
		let b = prb.new_int_decision(2..=3);
		let c = prb.new_int_decision(2..=3);
		let y = prb.new_int_decision(3..=4);

		prb.minimum(vec![a, b, c]).result(y).post().unwrap();
		let (mut slv, map) = prb.lower().to_solver().unwrap();
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

		assert!(prb.minimum(vec![a, b, c]).result(y).post().is_err());
	}
}
