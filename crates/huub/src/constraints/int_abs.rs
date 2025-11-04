//! Structures and algorithms for the integer absolute value constraint, which
//! enforces that one variable is takes absolute value of another.

use std::{
	cmp,
	ops::{AddAssign, Neg},
};

use pindakaas::Lit as RawLit;

use crate::{
	actions::{
		InitializationActions, IntDecisionActions, PostingActions, ReasoningEngine,
		ReformulationActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelBoolView, ModelIntView, Propagator, SimplificationStatus,
		SolverBoolView, SolverIntView,
	},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, BoolView, BoolViewInner, IntLitMeaning,
		IntView,
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

impl IntAbsBounds<IntView, IntView, RawLit> {
	/// Create a new [`IntAbsBounds`] propagator and post it in the solver.
	pub(crate) fn new_in<E>(solver: &mut E, origin: IntView, abs: IntView)
	where
		E: AddAssign<BoxedPropagator> + InitializationActions + ?Sized,
		IntView: IntDecisionActions<E, Atom = BoolView>,
	{
		let BoolViewInner::Lit(origin_positive) =
			origin.get_lit(solver, IntLitMeaning::GreaterEq(0)).0
		else {
			panic!("origin variable in absolute value constraint is known positive or negative");
		};
		*solver += Box::new(Self {
			origin,
			abs,
			origin_positive,
		});
	}
}

impl<B, E, I1, I2, I2Neg> Constraint<E> for IntAbsBounds<I1, I2, B>
where
	E: ReasoningEngine,
	I1: ModelIntView<E>,
	I2: ModelIntView<E> + Neg<Output = I2Neg> + Into<I1>,
	I2Neg: Into<I1>,
	B: ModelBoolView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		match self.origin_positive.get_val(ctx) {
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

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let origin = slv.get_solver_int(self.origin.clone().into());
		let abs = slv.get_solver_int(self.abs.clone().into());
		IntAbsBounds::new_in(slv, origin, abs);
		Ok(())
	}
}

impl<B, E, I1, I2> Propagator<E> for IntAbsBounds<I1, I2, B>
where
	B: SolverBoolView<E>,
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);
		self.origin.enqueue_when(ctx, IntPropCond::Bounds);
		self.abs.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_abs", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (lb, ub) = self.origin.get_bounds(ctx);

		match self.origin_positive.get_val(ctx) {
			Some(false) => {
				// If we know that the origin is negative, then just negate the bounds
				self.abs
					.set_lower_bound(ctx, -ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.origin.get_upper_bound_lit(ctx)]
					})?;
				self.abs
					.set_upper_bound(ctx, -lb, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.get_lower_bound_lit(ctx),
							(!self.origin_positive.clone()).into(),
						]
					})?;

				let (lb, ub) = self.abs.get_bounds(ctx);
				self.origin
					.set_lower_bound(ctx, -ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.abs.get_upper_bound_lit(ctx)]
					})?;
				self.origin
					.set_upper_bound(ctx, -lb, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.abs.get_lower_bound_lit(ctx),
							(!self.origin_positive.clone()).into(),
						]
					})?;
			}
			Some(true) => {
				// If we know that the origin is positive, then the bounds
				// are the same.
				self.abs
					.set_lower_bound(ctx, lb, |ctx: &mut E::PropagationCtx<'_>| {
						[self.origin.get_lower_bound_lit(ctx)]
					})?;
				self.abs
					.set_upper_bound(ctx, ub, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.get_upper_bound_lit(ctx),
							self.origin_positive.clone().into(),
						]
					})?;

				let (lb, ub) = self.abs.get_bounds(ctx);
				self.origin
					.set_lower_bound(ctx, lb, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.abs.get_lower_bound_lit(ctx),
							self.origin_positive.clone().into(),
						]
					})?;
				self.origin
					.set_upper_bound(ctx, ub, |ctx: &mut E::PropagationCtx<'_>| {
						[self.abs.get_upper_bound_lit(ctx)]
					})?;
			}
			None => {
				// If the origin can be either positive or negative, then the bounds are
				// the maximum of the absolute values
				let abs_max = cmp::max(ub, -lb);
				self.abs
					.set_upper_bound(ctx, abs_max, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.origin.get_lit(ctx, IntLitMeaning::GreaterEq(-abs_max)),
							self.origin.get_lit(ctx, IntLitMeaning::Less(abs_max + 1)),
						]
					})?;

				// If the upper bound of the absolute value variable have changed, we
				// propagate bounds of the origin variable
				let abs_ub = self.abs.get_upper_bound(ctx);
				let ub_lit = self.abs.get_upper_bound_lit(ctx);
				self.origin
					.set_lower_bound(ctx, -abs_ub, [ub_lit.clone()])?;
				self.origin.set_upper_bound(ctx, abs_ub, [ub_lit])?;
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
		solver::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_int_abs_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(-3..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntAbsBounds::new_in(&mut slv, a, b);

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
