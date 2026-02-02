//! Structures and algorithms for the integer times constraint, which enforces
//! that the product of two integer variables is equal to a third integer
//! variable.

use std::{marker::PhantomData, num::NonZero, ops::Mul};

use itertools::{Itertools, MinMaxResult, iproduct};

use crate::{
	IntVal,
	actions::{
		InitActions, IntInspectionActions, IntSimplificationActions, PostingActions,
		ReasoningContext, ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	helpers::{
		div_ceil, div_floor,
		overflow::{OverflowImpossible, OverflowMode, OverflowPossible},
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::{activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// This propagator enforces that the product of the two integer decision
/// variables is equal to a third, i.e.`x * y = z`.
pub struct IntMulBounds<OM: OverflowMode, I1, I2, I3> {
	/// First factor variable
	pub(crate) factor1: I1,
	/// Second factor variable
	pub(crate) factor2: I2,
	/// Product variable
	pub(crate) product: I3,
	/// Overflow mode
	pub(crate) overflow_mode: PhantomData<OM>,
}

impl<OM, I1, I2, I3> IntMulBounds<OM, I1, I2, I3>
where
	OM: OverflowMode,
{
	/// Internal multiplication function that if `OVERFLOW` is `true`, it will
	/// saturate the result when it overflows.
	fn mul(x: IntVal, y: IntVal) -> IntVal {
		if OM::HANDLE_OVERFLOW {
			x.saturating_mul(y)
		} else {
			x * y
		}
	}
}

impl<I1, I2, I3> IntMulBounds<OverflowPossible, I1, I2, I3> {
	/// Returns whether given the bounds of the factors, the result can
	/// overflow.
	///
	/// If this method returns `true`, then the propagator used should have
	/// `OVERFLOW` set to `true`.
	pub(crate) fn can_overflow<E>(ctx: &E, f1: &I1, f2: &I2) -> bool
	where
		E: ReasoningContext + ?Sized,
		I1: IntInspectionActions<E>,
		I2: IntInspectionActions<E>,
	{
		let (f1_lb, f1_ub) = f1.bounds(ctx);
		let (f2_lb, f2_ub) = f2.bounds(ctx);
		iproduct!([f1_lb, f1_ub], [f2_lb, f2_ub]).any(|(f1, f2)| f1.checked_mul(f2).is_none())
	}

	/// Create a new [`IntMulBounds`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, factor1: I1, factor2: I2, product: I3)
	where
		E: PostingActions + ?Sized,
		I1: IntInspectionActions<E> + IntSolverActions<Engine>,
		I2: IntInspectionActions<E> + IntSolverActions<Engine>,
		I3: IntSolverActions<Engine>,
	{
		if Self::can_overflow(solver, &factor1, &factor2) {
			solver.add_propagator(Box::new(IntMulBounds::<OverflowPossible, _, _, _> {
				factor1,
				factor2,
				product,
				overflow_mode: PhantomData,
			}));
		} else {
			solver.add_propagator(Box::new(IntMulBounds::<OverflowImpossible, _, _, _> {
				factor1,
				factor2,
				product,
				overflow_mode: PhantomData,
			}));
		}
	}
}

impl<OM, E, I1, I2, I3> Constraint<E> for IntMulBounds<OM, I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntModelActions<E> + Mul<IntVal, Output = View<IntVal>>,
	I2: IntModelActions<E> + Mul<IntVal, Output = View<IntVal>>,
	I3: IntModelActions<E>,
	View<IntVal>: IntModelActions<E>,
	OM: OverflowMode,
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

	fn to_solver(&self, ctx: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let f1 = ctx.solver_view(self.factor1.clone().into());
		let f2 = ctx.solver_view(self.factor2.clone().into());
		let p = ctx.solver_view(self.product.clone().into());
		IntMulBounds::post(ctx, f1, f2, p);
		Ok(())
	}
}

impl<OM, E, I1, I2, I3> Propagator<E> for IntMulBounds<OM, I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
	I3: IntSolverActions<E>,
	OM: OverflowMode,
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
		let f1_lb_lit = self.factor1.min_lit(ctx);
		let f1_ub_lit = self.factor1.max_lit(ctx);
		let (f2_lb, f2_ub) = self.factor2.bounds(ctx);
		let f2_lb_lit = self.factor2.min_lit(ctx);
		let f2_ub_lit = self.factor2.max_lit(ctx);
		let (pr_lb, pr_ub) = self.product.bounds(ctx);
		let pr_lb_lit = self.product.min_lit(ctx);
		let pr_ub_lit = self.product.max_lit(ctx);

		// TODO: Filter possibilities based on whether variables can be both positive
		// and negative.

		// Calculate possible bounds for the product
		let minmax = iproduct!([f1_lb, f1_ub], [f2_lb, f2_ub])
			.map(|(a, b)| Self::mul(a, b))
			.minmax();
		let (min, max) = match minmax {
			MinMaxResult::NoElements => unreachable!(),
			MinMaxResult::OneElement(b) => (b, b),
			MinMaxResult::MinMax(min, max) => (min, max),
		};
		let reason = &[
			f1_lb_lit.clone(),
			f1_ub_lit.clone(),
			f2_lb_lit.clone(),
			f2_ub_lit.clone(),
		];
		// z >= x * y
		self.product.tighten_min(ctx, min, reason)?;
		// z <= x * y
		self.product.tighten_max(ctx, max, reason)?;

		// Propagate the bounds of the first factor if the second factor is known
		// positive or known negative.
		if f2_lb > 0 || f2_ub < 0 {
			let reason = &[pr_lb_lit.clone(), pr_ub_lit.clone(), f2_lb_lit, f2_ub_lit];
			// factor1 >= product / factor2
			let min = iproduct!([pr_lb, pr_ub], [f2_lb, f2_ub])
				.map(|(pr, f2)| div_ceil(pr, NonZero::new(f2).unwrap()))
				.min()
				.unwrap();
			self.factor1.tighten_min(ctx, min, reason)?;
			// factor1 <= product / factor2
			let max = iproduct!([pr_lb, pr_ub], [f2_lb, f2_ub])
				.map(|(pr, f2)| div_floor(pr, NonZero::new(f2).unwrap()))
				.max()
				.unwrap();
			self.factor1.tighten_max(ctx, max, reason)?;
		}

		// Propagate the bounds of the second factor if the first factor is known
		// positive or known negative.
		if f1_lb > 0 || f1_ub < 0 {
			let reason = &[pr_lb_lit, pr_ub_lit, f1_lb_lit, f1_ub_lit];
			// factor2 >= product / factor1
			let min = iproduct!([pr_lb, pr_ub], [f1_lb, f1_ub])
				.map(|(pr, f1)| div_ceil(pr, NonZero::new(f1).unwrap()))
				.min()
				.unwrap();
			self.factor2.tighten_min(ctx, min, reason)?;
			// factor2 <= product / factor1
			let max = iproduct!([pr_lb, pr_ub], [f1_lb, f1_ub])
				.map(|(pr, f1)| div_floor(pr, NonZero::new(f1).unwrap()))
				.max()
				.unwrap();
			self.factor2.tighten_max(ctx, max, reason)?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		constraints::int_mul::IntMulBounds,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn overflow_intermediate_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(IntVal::MIN..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			(IntVal::MIN..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);

		IntMulBounds::post(&mut slv, a, b, 2);
		slv.expect_solutions(
			&[a, b],
			expect![[r#"
		-2, -1
		-1, -2
		1, 2
		2, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn overflow_unsat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(2..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			(IntVal::MIN..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);

		IntMulBounds::post(&mut slv, IntVal::MAX, a, b);
		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn simple_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(-2..=1).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			(-1..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntDecision::new_in(
			&mut slv,
			(-4..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntMulBounds::post(&mut slv, a, b, c);
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

	#[test]
	#[traced_test]
	fn underflow_unsat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(2..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			(IntVal::MIN..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);

		IntMulBounds::post(&mut slv, IntVal::MIN, a, b);
		slv.assert_unsatisfiable();
	}
}
