//! Structures and algorithms for the integer absolute value constraint, which
//! enforces that one variable is takes absolute value of another.

use std::{
	cmp,
	ops::{Neg, Not},
};

use crate::{
	actions::{InitActions, IntDecisionActions, PostingActions, ReasoningContext, ReasoningEngine},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, IntModelActions, IntSolverActions,
		Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	solver::{
		Decision, IntLitMeaning, View, activation_list::IntPropCond, engine::Engine,
		queue::PriorityLevel, view::boolean::BoolView,
	},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `int_abs` constraint within a model.
///
/// This constraint enforces that the second integer decision variable takes the
/// absolute value of the first integer decision variable.
pub struct IntAbsBounds<I1, I2, B> {
	/// The integer decision variable whose absolute value is being taken
	pub(crate) origin: I1,
	/// The integer decision variable representing the absolute value
	pub(crate) abs: I2,
	/// Boolean condition that is true if the origin is zero or positive, and
	/// false otherwise.
	pub(crate) origin_positive: B,
}

impl<I1, I2> IntAbsBounds<I1, I2, Decision<bool>> {
	/// Create a new [`IntAbsBounds`] propagator and post it in the solver.
	pub(crate) fn post<E, I2Neg>(solver: &mut E, origin: I1, abs: I2)
	where
		E: PostingActions + ReasoningContext<Atom = View<bool>> + ?Sized,
		I1: IntDecisionActions<E> + IntSolverActions<Engine>,
		I2: IntSolverActions<Engine> + Neg<Output = I2Neg> + Into<I1>,
		I2Neg: Into<I1>,
	{
		let BoolView::Lit(origin_positive) = origin.lit(solver, IntLitMeaning::GreaterEq(0)).0
		else {
			panic!("origin variable in absolute value constraint is known positive or negative");
		};
		solver.add_propagator(Box::new(Self {
			origin,
			abs,
			origin_positive,
		}));
	}
}

impl<B, E, I1, I2, I2Neg> Constraint<E> for IntAbsBounds<I1, I2, B>
where
	E: ReasoningEngine,
	I1: IntModelActions<E>,
	I2: IntModelActions<E> + Neg<Output = I2Neg> + Into<I1>,
	I2Neg: Into<I1>,
	B: BoolModelActions<E> + Not<Output = B>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		match self.origin_positive.val(ctx) {
			Some(true) => {
				self.origin.unify(ctx, self.abs.clone())?;
				Ok(SimplificationStatus::Subsumed)
			}
			Some(false) => {
				self.origin.unify(ctx, -self.abs.clone())?;
				Ok(SimplificationStatus::Subsumed)
			}
			None => {
				<Self as Propagator<E>>::propagate(self, ctx)?;
				Ok(SimplificationStatus::NoFixpoint)
			}
		}
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let origin = slv.solver_view(self.origin.clone().into());
		let abs = slv.solver_view(self.abs.clone().into());
		IntAbsBounds::post(slv, origin, abs);
		Ok(())
	}
}

impl<B, E, I1, I2> Propagator<E> for IntAbsBounds<I1, I2, B>
where
	B: BoolSolverActions<E> + Not<Output = B>,
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);
		self.origin.enqueue_when(ctx, IntPropCond::Bounds);
		self.abs.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_abs", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (lb, ub) = self.origin.bounds(ctx);

		match self.origin_positive.val(ctx) {
			Some(false) => {
				// If we know that the origin is negative, then just negate the bounds
				self.abs
					.tighten_min(ctx, -ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.origin.max_lit(ctx)]
					})?;
				self.abs
					.tighten_max(ctx, -lb, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.min_lit(ctx),
							(!self.origin_positive.clone()).into(),
						]
					})?;

				let (lb, ub) = self.abs.bounds(ctx);
				self.origin
					.tighten_min(ctx, -ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.abs.max_lit(ctx)]
					})?;
				self.origin
					.tighten_max(ctx, -lb, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.abs.min_lit(ctx),
							(!self.origin_positive.clone()).into(),
						]
					})?;
			}
			Some(true) => {
				// If we know that the origin is positive, then the bounds
				// are the same.
				self.abs
					.tighten_min(ctx, lb, |ctx: &mut E::PropagationCtx<'_>| {
						[self.origin.min_lit(ctx)]
					})?;
				self.abs
					.tighten_max(ctx, ub, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.max_lit(ctx),
							self.origin_positive.clone().into(),
						]
					})?;

				let (lb, ub) = self.abs.bounds(ctx);
				self.origin
					.tighten_min(ctx, lb, |ctx: &mut E::PropagationCtx<'_>| {
						[self.abs.min_lit(ctx), self.origin_positive.clone().into()]
					})?;
				self.origin
					.tighten_max(ctx, ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.abs.max_lit(ctx)]
					})?;
			}
			None => {
				// If the origin can be either positive or negative, then the bounds are
				// the maximum of the absolute values
				let abs_max = cmp::max(ub, -lb);
				self.abs
					.tighten_max(ctx, abs_max, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.lit(ctx, IntLitMeaning::GreaterEq(-abs_max)),
							self.origin.lit(ctx, IntLitMeaning::Less(abs_max + 1)),
						]
					})?;

				// If the upper bound of the absolute value variable have changed, we
				// propagate bounds of the origin variable
				let abs_ub = self.abs.max(ctx);
				let ub_lit = self.abs.max_lit(ctx);
				self.origin.tighten_min(ctx, -abs_ub, [ub_lit.clone()])?;
				self.origin.tighten_max(ctx, abs_ub, [ub_lit])?;
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_abs::IntAbsBounds,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn test_int_abs_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(-3..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([-3..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntAbsBounds::post(&mut slv, a, b);

		slv.expect_solutions(
			&[a, b],
			expect![[r#"
    -3, 3
    -2, 2
    -1, 1
    0, 0
    1, 1
    2, 2
    3, 3"#]],
		);
	}
}
