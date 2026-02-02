//! Structures and algorithms for the integer division constraint, which
//! enforces that a numerator, a denominator, and a result variable are
//! correctly related by integer division.

use std::{mem, num::NonZero, ops::Neg};

use crate::{
	IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, IntPropagationActions,
		PostingActions, ReasoningEngine, SimplificationActions,
	},
	constraints::{
		BoolModelActions, Constraint, IntModelActions, IntSolverActions, Propagator,
		SimplificationStatus,
	},
	helpers::div_ceil,
	lower::{LoweringContext, LoweringError},
	model::{expressions::bool_formula::BoolFormula, view::View},
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
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

impl<I1, I2, I3> IntDivBounds<I1, I2, I3> {
	/// Create a new [`IntDivBounds`] propagator and post it in the solver.
	pub fn post<E>(
		solver: &mut E,
		numerator: I1,
		denominator: I2,
		result: I3,
	) -> Result<(), E::Conflict>
	where
		E: PostingActions + ?Sized,
		I1: IntSolverActions<Engine> + Neg + Into<<I1 as Neg>::Output> + IntDecisionActions<E>,
		<I1 as Neg>::Output: IntSolverActions<Engine>,
		I2: IntSolverActions<Engine> + Neg + Into<<I2 as Neg>::Output> + IntDecisionActions<E>,
		<I2 as Neg>::Output: IntSolverActions<Engine>,
		I3: IntSolverActions<Engine> + Neg + Into<<I3 as Neg>::Output> + IntDecisionActions<E>,
		<I3 as Neg>::Output: IntSolverActions<Engine>,
	{
		// Ensure the consistency of the signs of the three variables using the
		// following clauses.
		if numerator.min(solver) < 0 || denominator.min(solver) < 0 || result.min(solver) < 0 {
			let num_pos = numerator.lit(solver, IntLitMeaning::GreaterEq(0));
			let num_neg = numerator.lit(solver, IntLitMeaning::Less(1));
			let denom_pos = denominator.lit(solver, IntLitMeaning::GreaterEq(0));
			let denom_neg = !denom_pos.clone();
			let res_pos = result.lit(solver, IntLitMeaning::GreaterEq(0));
			let res_neg = result.lit(solver, IntLitMeaning::Less(1));

			// num >= 0 /\ denom > 0 => res >= 0
			solver.add_clause([!num_pos.clone(), !denom_pos.clone(), res_pos.clone()])?;
			// num <= 0 /\ denom < 0 => res >= 0
			solver.add_clause([!num_neg.clone(), !denom_neg.clone(), res_pos])?;
			// num >= 0 /\ denom < 0 => res < 0
			solver.add_clause([!num_pos, !denom_neg, res_neg.clone()])?;
			// num < 0 /\ denom >= 0 => res < 0
			solver.add_clause([!num_neg, !denom_pos, res_neg])?;
		}

		solver.add_propagator(Box::new(Self {
			numerator,
			denominator,
			result,
		}));

		Ok(())
	}

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
		I4: IntSolverActions<E>,
		I5: IntSolverActions<E>,
		I6: IntSolverActions<E>,
	{
		let (num_lb, num_ub) = numerator.bounds(ctx);
		let (denom_lb, denom_ub) = denominator.bounds(ctx);
		let (res_lb, res_ub) = result.bounds(ctx);

		let new_res_lb = num_lb / denom_ub;
		if new_res_lb > res_lb {
			result.tighten_min(ctx, new_res_lb, |ctx: &mut E::PropagationCtx<'_>| {
				[
					numerator.min_lit(ctx),
					denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.max_lit(ctx),
				]
			})?;
		}

		let new_num_lb = denom_lb * res_lb;
		if new_num_lb > num_lb {
			numerator.tighten_min(ctx, new_num_lb, |ctx: &mut E::PropagationCtx<'_>| {
				[denominator.min_lit(ctx), result.min_lit(ctx)]
			})?;
		}

		if res_lb > 0 {
			let new_denom_ub = num_ub / res_lb;
			if new_denom_ub < denom_ub {
				denominator.tighten_max(ctx, new_denom_ub, |ctx: &mut E::PropagationCtx<'_>| {
					[
						numerator.max_lit(ctx),
						numerator.lit(ctx, IntLitMeaning::GreaterEq(0)),
						result.min_lit(ctx),
						denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					]
				})?;
			}
		}

		if let Some(res_ub_inc) = NonZero::new(res_ub + 1) {
			let new_denom_lb = div_ceil(num_lb + 1, res_ub_inc);
			if new_denom_lb > denom_lb {
				denominator.tighten_min(ctx, new_denom_lb, |ctx: &mut E::PropagationCtx<'_>| {
					[
						numerator.min_lit(ctx),
						result.max_lit(ctx),
						result.lit(ctx, IntLitMeaning::GreaterEq(0)),
						denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					]
				})?;
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
		I4: IntSolverActions<E>,
		I5: IntSolverActions<E>,
		I6: IntSolverActions<E>,
	{
		let num_ub = numerator.max(ctx);
		let (denom_lb, denom_ub) = denominator.bounds(ctx);
		let res_ub = result.max(ctx);

		if denom_lb != 0 {
			let new_res_ub = num_ub / denom_lb;
			if new_res_ub < res_ub {
				result.tighten_max(ctx, new_res_ub, |ctx: &mut E::PropagationCtx<'_>| {
					[numerator.max_lit(ctx), denominator.min_lit(ctx)]
				})?;
			}
		}

		let new_num_ub = (res_ub + 1) * denom_ub - 1;
		if new_num_ub < num_ub {
			numerator.tighten_max(ctx, new_num_ub, |ctx: &mut E::PropagationCtx<'_>| {
				[
					denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.max_lit(ctx),
					result.max_lit(ctx),
				]
			})?;
		}
		Ok(())
	}
}

impl<E> Constraint<E> for IntDivBounds<View<IntVal>, View<IntVal>, View<IntVal>>
where
	E: ReasoningEngine<Atom = View<bool>>,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	View<IntVal>: IntModelActions<E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		use pindakaas::propositional_logic::Formula::*;

		// Always exclude zero from the domain.
		self.denominator.remove_val(ctx, 0, [])?;

		// Channel the signs of the decision variables
		let num_pos = self.numerator.lit(ctx, IntLitMeaning::GreaterEq(0));
		let num_neg = self.numerator.lit(ctx, IntLitMeaning::Less(1));
		let denom_pos = self.denominator.lit(ctx, IntLitMeaning::GreaterEq(0));
		let denom_neg = !denom_pos;
		let res_pos = self.result.lit(ctx, IntLitMeaning::GreaterEq(0));
		let res_neg = self.result.lit(ctx, IntLitMeaning::Less(1));

		// num >= 0 /\ denom > 0 => res >= 0
		<BoolFormula as Constraint<E>>::simplify(
			&mut Or(vec![!Atom(num_pos), !Atom(denom_pos), Atom(res_pos)]),
			ctx,
		)?;
		// num <= 0 /\ denom < 0 => res >= 0
		<BoolFormula as Constraint<E>>::simplify(
			&mut Or(vec![!Atom(num_neg), !Atom(denom_neg), Atom(res_pos)]),
			ctx,
		)?;
		// num >= 0 /\ denom < 0 => res >= 0
		<BoolFormula as Constraint<E>>::simplify(
			&mut Or(vec![!Atom(num_pos), !Atom(denom_neg), Atom(res_neg)]),
			ctx,
		)?;
		// num <= 0 /\ denom > 0 => res <= 0
		<BoolFormula as Constraint<E>>::simplify(
			&mut Or(vec![!Atom(num_neg), !Atom(denom_pos), Atom(res_neg)]),
			ctx,
		)?;

		self.propagate(ctx)?;

		if self.numerator.val(ctx).is_some()
			&& self.denominator.val(ctx).is_some()
			&& self.result.val(ctx).is_some()
		{
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let numerator = slv.solver_view(self.numerator);
		let denominator = slv.solver_view(self.denominator);
		let result = slv.solver_view(self.result);
		IntDivBounds::post(slv, numerator, denominator, result).unwrap();
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntDivBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E> + Neg + Into<<I1 as Neg>::Output>,
	<I1 as Neg>::Output: IntSolverActions<E>,
	I2: IntSolverActions<E> + Neg + Into<<I2 as Neg>::Output>,
	<I2 as Neg>::Output: IntSolverActions<E>,
	I3: IntSolverActions<E> + Neg + Into<<I3 as Neg>::Output>,
	<I3 as Neg>::Output: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		self.numerator.enqueue_when(ctx, IntPropCond::Bounds);
		self.denominator.enqueue_when(ctx, IntPropCond::Bounds);
		self.result.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_div", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (denom_lb, denom_ub) = self.denominator.bounds(ctx);
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
		if numerator.max(ctx) >= 0 && self.result.max(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &numerator, &denominator, &self.result)?;
		}
		// If their upper bounds are negative, then propagate the upper bounds of
		// the negated versions.
		if neg_num.max(ctx) >= 0 && neg_res.max(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &neg_num, &denominator, &neg_res)?;
		}

		// If the numerator and the results are known positive, then we can
		// propagate the remainder of the bounds under the assumption all values
		// must be positive.
		if numerator.min(ctx) >= 0 && self.result.min(ctx) >= 0 {
			Self::propagate_positive_domains(ctx, &numerator, &denominator, &self.result)?;
		}
		// If the domain of the numerator and the result are known negative, then
		// propagate their using their negations.
		if neg_num.min(ctx) >= 0 && neg_res.min(ctx) >= 0 {
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
		Model,
		constraints::int_div::IntDivBounds,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn test_int_div_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(-7..=7).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([-3..=-1, 1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntDecision::new_in(
			&mut slv,
			(-7..=7).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntDivBounds::post(&mut slv, a, b, c).unwrap();

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

	#[test]
	#[traced_test]
	fn test_int_div_simplify() {
		let mut prb = Model::default();
		let num = prb.new_int_decision(-20..=-10);
		let den = prb.new_int_decision(0..=4);
		let res = prb.new_int_decision(-20..=20);

		prb.div(num, den).result(res).post();

		prb.expect_solutions(
			&[num, den, res],
			expect![[r#"
    -20, 1, -20
    -20, 2, -10
    -20, 3, -6
    -20, 4, -5
    -19, 1, -19
    -19, 2, -9
    -19, 3, -6
    -19, 4, -4
    -18, 1, -18
    -18, 2, -9
    -18, 3, -6
    -18, 4, -4
    -17, 1, -17
    -17, 2, -8
    -17, 3, -5
    -17, 4, -4
    -16, 1, -16
    -16, 2, -8
    -16, 3, -5
    -16, 4, -4
    -15, 1, -15
    -15, 2, -7
    -15, 3, -5
    -15, 4, -3
    -14, 1, -14
    -14, 2, -7
    -14, 3, -4
    -14, 4, -3
    -13, 1, -13
    -13, 2, -6
    -13, 3, -4
    -13, 4, -3
    -12, 1, -12
    -12, 2, -6
    -12, 3, -4
    -12, 4, -3
    -11, 1, -11
    -11, 2, -5
    -11, 3, -3
    -11, 4, -2
    -10, 1, -10
    -10, 2, -5
    -10, 3, -3
    -10, 4, -2"#]],
		);
	}
}
