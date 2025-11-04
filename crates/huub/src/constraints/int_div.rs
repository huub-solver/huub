//! Structures and algorithms for the integer division constraint, which
//! enforces that a numerator, a denominator, and a result variable are
//! correctly related by integer division.

use std::{
	mem,
	ops::{AddAssign, Neg},
};

use pindakaas::{ClauseDatabase, ClauseDatabaseTools, Unsatisfiable};

use crate::{
	actions::{
		IntDecisionActions, IntInspectionActions, IntPropagationActions, PostingActions,
		ReasoningEngine, ReformulationActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	helpers::div_ceil,
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, BoolView, IntLitMeaning, IntView,
	},
	BoolDecision, BoolFormula, IntDecision, NonZeroIntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the division of two integer variables.
///
/// This propagator enforces truncating rounding on the result of the division,
/// and enforces that the denominator is non-zero.
pub struct IntDivBounds<I1, I2, I3> {
	/// The numerator of the division
	pub(crate) numerator: I1,
	/// The denominator of the division
	pub(crate) denominator: I2,
	/// Result of the division
	pub(crate) result: I3,
}

impl<E> Constraint<E> for IntDivBounds<IntDecision, IntDecision, IntDecision>
where
	E: ReasoningEngine<Atom = BoolDecision>,
	IntDecision: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		use pindakaas::propositional_logic::Formula::*;

		// Always exclude zero from the domain.
		self.denominator.set_not_eq(ctx, 0, [])?;

		// Channel the signs of the decision variables
		let num_pos = self.numerator.get_lit(ctx, IntLitMeaning::GreaterEq(0));
		let num_neg = self.numerator.get_lit(ctx, IntLitMeaning::Less(1));
		let denom_pos = self.denominator.get_lit(ctx, IntLitMeaning::GreaterEq(0));
		let denom_neg = !denom_pos;
		let res_pos = self.result.get_lit(ctx, IntLitMeaning::GreaterEq(0));
		let res_neg = self.result.get_lit(ctx, IntLitMeaning::Less(1));

		// num >= 0 /\ denom > 0 => res >= 0
		<BoolFormula as Propagator<E>>::propagate(
			&mut Or(vec![!Atom(num_pos), !Atom(denom_pos), Atom(res_pos)]),
			ctx,
		)?;
		// num <= 0 /\ denom < 0 => res >= 0
		<BoolFormula as Propagator<E>>::propagate(
			&mut Or(vec![!Atom(num_neg), !Atom(denom_neg), Atom(res_pos)]),
			ctx,
		)?;
		// num >= 0 /\ denom < 0 => res >= 0
		<BoolFormula as Propagator<E>>::propagate(
			&mut Or(vec![!Atom(num_pos), !Atom(denom_neg), Atom(res_neg)]),
			ctx,
		)?;
		// num <= 0 /\ denom > 0 => res <= 0
		<BoolFormula as Propagator<E>>::propagate(
			&mut Or(vec![!Atom(num_neg), !Atom(denom_pos), Atom(res_neg)]),
			ctx,
		)?;

		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let numerator = slv.get_solver_int(self.numerator);
		let denominator = slv.get_solver_int(self.denominator);
		let result = slv.get_solver_int(self.result);
		IntDivBounds::new_in(slv, numerator, denominator, result).unwrap();
		Ok(())
	}
}

impl IntDivBounds<IntView, IntView, IntView> {
	/// Create a new [`IntDivBounds`] propagator and post it in the solver.
	pub fn new_in<E>(
		engine: &mut E,
		numerator: IntView,
		denominator: IntView,
		result: IntView,
	) -> Result<(), Unsatisfiable>
	where
		E: AddAssign<BoxedPropagator> + ClauseDatabase + ?Sized,
		IntView: IntDecisionActions<E, Atom = BoolView>,
	{
		// Ensure the consistency of the signs of the three variables using the
		// following clauses.
		if numerator.get_lower_bound(engine) < 0
			|| denominator.get_lower_bound(engine) < 0
			|| result.get_lower_bound(engine) < 0
		{
			let num_pos = numerator.get_lit(engine, IntLitMeaning::GreaterEq(0));
			let num_neg = numerator.get_lit(engine, IntLitMeaning::Less(1));
			let denom_pos = denominator.get_lit(engine, IntLitMeaning::GreaterEq(0));
			let denom_neg = !denom_pos;
			let res_pos = result.get_lit(engine, IntLitMeaning::GreaterEq(0));
			let res_neg = result.get_lit(engine, IntLitMeaning::Less(1));

			// num >= 0 /\ denom > 0 => res >= 0
			engine.add_clause([!num_pos, !denom_pos, res_pos])?;
			// num <= 0 /\ denom < 0 => res >= 0
			engine.add_clause([!num_neg, !denom_neg, res_pos])?;
			// num >= 0 /\ denom < 0 => res < 0
			engine.add_clause([!num_pos, !denom_neg, res_neg])?;
			// num < 0 /\ denom >= 0 => res < 0
			engine.add_clause([!num_neg, !denom_pos, res_neg])?;
		}

		*engine += Box::new(Self {
			numerator,
			denominator,
			result,
		});

		Ok(())
	}
}

impl<I1, I2, I3> IntDivBounds<I1, I2, I3> {
	/// Propagate the result and numerator lower bounds, and the denominator
	/// bounds, assuming all lower bounds are positive.
	fn propagate_positive_domains<E, I4, I5, I6>(
		ctx: &mut E::PropagationCtx<'_>,
		numerator: &I4,
		denominator: &I5,
		result: &I6,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I4: SolverIntView<E>,
		I5: SolverIntView<E>,
		I6: SolverIntView<E>,
	{
		let (num_lb, num_ub) = numerator.get_bounds(ctx);
		let (denom_lb, denom_ub) = denominator.get_bounds(ctx);
		let (res_lb, res_ub) = result.get_bounds(ctx);

		let new_res_lb = num_lb / denom_ub;
		if new_res_lb > res_lb {
			result.set_lower_bound(ctx, new_res_lb, |ctx: &mut E::PropagationCtx<'_>| {
				[
					numerator.get_lower_bound_lit(ctx),
					denominator.get_lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.get_upper_bound_lit(ctx),
				]
			})?;
		}

		let new_num_lb = denom_lb * res_lb;
		if new_num_lb > num_lb {
			numerator.set_lower_bound(ctx, new_num_lb, |ctx: &mut E::PropagationCtx<'_>| {
				[
					denominator.get_lower_bound_lit(ctx),
					result.get_lower_bound_lit(ctx),
				]
			})?;
		}

		if res_lb > 0 {
			let new_denom_ub = num_ub / res_lb;
			if new_denom_ub < denom_ub {
				denominator.set_upper_bound(
					ctx,
					new_denom_ub,
					|ctx: &mut E::PropagationCtx<'_>| {
						[
							numerator.get_upper_bound_lit(ctx),
							numerator.get_lit(ctx, IntLitMeaning::GreaterEq(0)),
							result.get_lower_bound_lit(ctx),
							denominator.get_lit(ctx, IntLitMeaning::GreaterEq(1)),
						]
					},
				)?;
			}
		}

		if let Some(res_ub_inc) = NonZeroIntVal::new(res_ub + 1) {
			let new_denom_lb = div_ceil(num_lb + 1, res_ub_inc);
			if new_denom_lb > denom_lb {
				denominator.set_lower_bound(
					ctx,
					new_denom_lb,
					|ctx: &mut E::PropagationCtx<'_>| {
						[
							numerator.get_lower_bound_lit(ctx),
							result.get_upper_bound_lit(ctx),
							result.get_lit(ctx, IntLitMeaning::GreaterEq(0)),
							denominator.get_lit(ctx, IntLitMeaning::GreaterEq(1)),
						]
					},
				)?;
			}
		}

		Ok(())
	}

	/// Propagate the  upper bounds of the result and numerator, assuming the
	/// signs of the result and the numerator are positive.
	fn propagate_upper_bounds<E, I4, I5, I6>(
		ctx: &mut E::PropagationCtx<'_>,
		numerator: &I4,
		denominator: &I5,
		result: &I6,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I4: SolverIntView<E>,
		I5: SolverIntView<E>,
		I6: SolverIntView<E>,
	{
		let num_ub = numerator.get_upper_bound(ctx);
		let (denom_lb, denom_ub) = denominator.get_bounds(ctx);
		let res_ub = result.get_upper_bound(ctx);

		if denom_lb != 0 {
			let new_res_ub = num_ub / denom_lb;
			if new_res_ub < res_ub {
				result.set_upper_bound(ctx, new_res_ub, |ctx: &mut E::PropagationCtx<'_>| {
					[
						numerator.get_upper_bound_lit(ctx),
						denominator.get_lower_bound_lit(ctx),
					]
				})?;
			}
		}

		let new_num_ub = (res_ub + 1) * denom_ub - 1;
		if new_num_ub < num_ub {
			numerator.set_upper_bound(ctx, new_num_ub, |ctx: &mut E::PropagationCtx<'_>| {
				[
					denominator.get_lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.get_upper_bound_lit(ctx),
					result.get_upper_bound_lit(ctx),
				]
			})?;
		}
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntDivBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: SolverIntView<E> + Neg + Into<<I1 as Neg>::Output>,
	<I1 as Neg>::Output: SolverIntView<E>,
	I2: SolverIntView<E> + Neg + Into<<I2 as Neg>::Output>,
	<I2 as Neg>::Output: SolverIntView<E>,
	I3: SolverIntView<E> + Neg + Into<<I3 as Neg>::Output>,
	<I3 as Neg>::Output: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		self.numerator.enqueue_when(ctx, IntPropCond::Bounds);
		self.denominator.enqueue_when(ctx, IntPropCond::Bounds);
		self.result.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_div", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (denom_lb, denom_ub) = self.denominator.get_bounds(ctx);
		if denom_lb < 0 && denom_ub > 0 {
			// Wait until the sign of the denominator is known
			return Ok(());
		}

		// If the denominator is known negative, then we swap it and the numerator
		// with their negations.
		let mut denominator = self.denominator.clone().into();
		let mut neg_denom = -self.denominator.clone();
		let mut numerator = self.numerator.clone().into();
		let mut neg_num = -self.numerator.clone();
		let neg_res = -self.result.clone();
		if denom_ub <= 0 {
			mem::swap(&mut denominator, &mut neg_denom);
			mem::swap(&mut numerator, &mut neg_num);
		}

		// If both the upper bound of the numerator and the upper bound of the
		// right-hand side are positive, then propagate their upper bounds directly.
		if numerator.get_upper_bound(ctx) >= 0 && self.result.get_upper_bound(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &numerator, &denominator, &self.result)?;
		}
		// If their upper bounds are negative, then propagate the upper bounds of
		// the negated versions.
		if neg_num.get_upper_bound(ctx) >= 0 && neg_res.get_upper_bound(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &neg_num, &denominator, &neg_res)?;
		}

		// If the numerator and the results are known positive, then we can
		// propagate the remainder of the bounds under the assumption all values
		// must be positive.
		if numerator.get_lower_bound(ctx) >= 0 && self.result.get_lower_bound(ctx) >= 0 {
			Self::propagate_positive_domains(ctx, &numerator, &denominator, &self.result)?;
		}
		// If the domain of the numerator and the result are known negative, then
		// propagate their using their negations.
		if neg_num.get_lower_bound(ctx) >= 0 && neg_res.get_lower_bound(ctx) >= 0 {
			Self::propagate_positive_domains(ctx, &neg_num, &denominator, &neg_res)?;
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
		constraints::int_div::IntDivBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
	};

	#[test]
	#[traced_test]
	fn test_int_div_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(-7..=7).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=-1, 1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			(-7..=7).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntDivBounds::new_in(&mut slv, a, b, c).unwrap();

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    -7, -3, 2
    -7, -2, 3
    -7, -1, 7
    -7, 1, -7
    -7, 2, -3
    -7, 3, -2
    -6, -3, 2
    -6, -2, 3
    -6, -1, 6
    -6, 1, -6
    -6, 2, -3
    -6, 3, -2
    -5, -3, 1
    -5, -2, 2
    -5, -1, 5
    -5, 1, -5
    -5, 2, -2
    -5, 3, -1
    -4, -3, 1
    -4, -2, 2
    -4, -1, 4
    -4, 1, -4
    -4, 2, -2
    -4, 3, -1
    -3, -3, 1
    -3, -2, 1
    -3, -1, 3
    -3, 1, -3
    -3, 2, -1
    -3, 3, -1
    -2, -3, 0
    -2, -2, 1
    -2, -1, 2
    -2, 1, -2
    -2, 2, -1
    -2, 3, 0
    -1, -3, 0
    -1, -2, 0
    -1, -1, 1
    -1, 1, -1
    -1, 2, 0
    -1, 3, 0
    0, -3, 0
    0, -2, 0
    0, -1, 0
    0, 1, 0
    0, 2, 0
    0, 3, 0
    1, -3, 0
    1, -2, 0
    1, -1, -1
    1, 1, 1
    1, 2, 0
    1, 3, 0
    2, -3, 0
    2, -2, -1
    2, -1, -2
    2, 1, 2
    2, 2, 1
    2, 3, 0
    3, -3, -1
    3, -2, -1
    3, -1, -3
    3, 1, 3
    3, 2, 1
    3, 3, 1
    4, -3, -1
    4, -2, -2
    4, -1, -4
    4, 1, 4
    4, 2, 2
    4, 3, 1
    5, -3, -1
    5, -2, -2
    5, -1, -5
    5, 1, 5
    5, 2, 2
    5, 3, 1
    6, -3, -2
    6, -2, -3
    6, -1, -6
    6, 1, 6
    6, 2, 3
    6, 3, 2
    7, -3, -2
    7, -2, -3
    7, -1, -7
    7, 1, 7
    7, 2, 3
    7, 3, 2"#]],
		);
	}
}
