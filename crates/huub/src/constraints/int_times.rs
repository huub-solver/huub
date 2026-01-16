//! Structures and algorithms for the integer times constraint, which enforces
//! that the product of two integer variables is equal to a third integer
//! variable.

use std::{
	num::NonZero,
	ops::{AddAssign, Mul},
};

use crate::{
	IntDecision, IntVal,
		InitActions, IntSimplificationActions, ReasoningEngine, ReformulationActions,
		TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	helpers::{div_ceil, div_floor},
	reformulate::ReformulationError,
	solver::{IntView, activation_list::IntPropCond, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// This propagator enforces that the product of the two integer decision
/// variables is equal to a third, i.e.`x * y = z`.
pub struct IntTimesBounds<I1, I2, I3> {
	/// First factor variable
	pub(crate) factor1: I1,
	/// Second factor variable
	pub(crate) factor2: I2,
	/// Product variable
	pub(crate) product: I3,
}

impl IntTimesBounds<IntView, IntView, IntView> {
	/// Create a new [`IntTimesBounds`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, factor1: IntView, factor2: IntView, product: IntView)
	where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self {
			factor1,
			factor2,
			product,
		});
	}
}

impl<E, I1, I2, I3> Constraint<E> for IntTimesBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: ModelIntView<E> + Mul<IntVal, Output = IntDecision>,
	I2: ModelIntView<E> + Mul<IntVal, Output = IntDecision>,
	I3: ModelIntView<E>,
	IntDecision: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		if let Some(f1) = self.factor1.val(ctx) {
			(self.factor2.clone() * f1).unify(ctx, self.product.clone())?;
			return Ok(SimplificationStatus::Subsumed);
		}
		if let Some(f2) = self.factor2.val(ctx) {
			(self.factor1.clone() * f2).unify(ctx, self.product.clone())?;
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(
		&self,
		ctx: &mut dyn ReformulationActions,
		_model_trail: &dyn TrailingActions,
	) -> Result<(), ReformulationError> {
		let f1 = ctx.solver_int(self.factor1.clone().into());
		let f2 = ctx.solver_int(self.factor2.clone().into());
		let p = ctx.solver_int(self.product.clone().into());
		IntTimesBounds::post(ctx, f1, f2, p);
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntTimesBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
	I3: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut <E as ReasoningEngine>::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);
		self.factor1.enqueue_when(ctx, IntPropCond::Bounds);
		self.factor2.enqueue_when(ctx, IntPropCond::Bounds);
		self.product.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_times", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (f1_lb, f1_ub) = self.factor1.bounds(ctx);
		let f1_lb_lit = self.factor1.lower_bound_lit(ctx);
		let f1_ub_lit = self.factor1.upper_bound_lit(ctx);
		let (f2_lb, f2_ub) = self.factor2.bounds(ctx);
		let f2_lb_lit = self.factor2.lower_bound_lit(ctx);
		let f2_ub_lit = self.factor2.upper_bound_lit(ctx);
		let (pr_lb, pr_ub) = self.product.bounds(ctx);
		let pr_lb_lit = self.product.lower_bound_lit(ctx);
		let pr_ub_lit = self.product.upper_bound_lit(ctx);

		// TODO: Filter possibilities based on whether variables can be both positive
		// and negative.

		// Calculate possible bounds for the product
		let bounds = [f1_lb * f2_lb, f1_lb * f2_ub, f1_ub * f2_lb, f1_ub * f2_ub];
		let reason = &[
			f1_lb_lit.clone(),
			f1_ub_lit.clone(),
			f2_lb_lit.clone(),
			f2_ub_lit.clone(),
		];
		// z >= x * y
		let min = bounds.iter().min().unwrap();
		self.product.set_lower_bound(ctx, *min, reason)?;
		// z <= x * y
		let max = bounds.iter().max().unwrap();
		self.product.set_upper_bound(ctx, *max, reason)?;

		// Propagate the bounds of the first factor if the second factor is known
		// positive or known negative.
		if f2_lb > 0 || f2_ub < 0 {
			// Calculate possible bounds for the first factor
			let bounds = [
				(pr_lb, f2_lb),
				(pr_lb, f2_ub),
				(pr_ub, f2_lb),
				(pr_ub, f2_ub),
			];
			let reason = &[pr_lb_lit.clone(), pr_ub_lit.clone(), f2_lb_lit, f2_ub_lit];
			// factor1 >= product / factor2
			let min = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZero::new(*y).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			self.factor1.set_lower_bound(ctx, min, reason)?;
			// factor1 <= product / factor2
			let max = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZero::new(*y).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			self.factor1.set_upper_bound(ctx, max, reason)?;
		}

		// Propagate the bounds of the second factor if the first factor is known
		// positive or known negative.
		if f1_lb > 0 || f1_ub < 0 {
			// Calculate possible bounds for the first factor `y`
			let bounds = [
				(pr_lb, f1_lb),
				(pr_lb, f1_ub),
				(pr_ub, f1_lb),
				(pr_ub, f1_ub),
			];
			let reason = &[pr_lb_lit, pr_ub_lit, f1_lb_lit, f1_ub_lit];
			// factor2 >= product / factor1
			let min = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZero::new(*x).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			self.factor2.set_lower_bound(ctx, min, reason)?;
			// factor2 <= product / factor1
			let max = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZero::new(*x).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			self.factor2.set_upper_bound(ctx, max, reason)?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_times::IntTimesBounds,
		solver::{
			Solver,
			int_var::{EncodingType, IntVar},
		},
	};

	#[test]
	#[traced_test]
	fn test_int_times_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(-2..=1).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			(-1..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			(-4..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntTimesBounds::post(&mut slv, a, b, c);
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
		-2, -1, 2
		-2, 0, 0
		-2, 1, -2
		-2, 2, -4
		-1, -1, 1
		-1, 0, 0
		-1, 1, -1
		-1, 2, -2
		0, -1, 0
		0, 0, 0
		0, 1, 0
		0, 2, 0
		1, -1, -1
		1, 0, 0
		1, 1, 1
		1, 2, 2"#]],
		);
	}
}
