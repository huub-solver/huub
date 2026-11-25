//! Structures and algorithms for the integer division constraint, which
//! enforces that a numerator, a denominator, and a result variable are
//! correctly related by integer division.

use std::{marker::PhantomData, mem, num::NonZero, ops::Neg};

use crate::{
	DeepClone, IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, IntPropCond, IntPropagationActions,
		PostingActions, ReasoningContext, ReasoningEngine, SimplificationActions,
	},
	constraints::{
		BoolModelActions, Constraint, IntModelActions, IntSolverActions, NO_REASON, Propagator,
		SimplificationStatus,
	},
	helpers::{
		div_ceil,
		overflow::{DoubleIntVal, OverflowImpossible, OverflowMode, OverflowPossible},
	},
	lower::{LoweringContext, LoweringError},
	model::{expressions::proposition::PropositionConstraint, view::View},
	solver::{IntLitMeaning, engine::Engine, queue::PriorityLevel},
};

/// Bounds propagator for the division of two integer variables.
///
/// This propagator enforces truncating rounding on the result of the division,
/// and enforces that the denominator is non-zero.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub struct IntDivBounds<OM: OverflowMode, I1, I2, I3> {
	/// The numerator of the division.
	pub(crate) numerator: I1,
	/// The denominator of the division.
	pub(crate) denominator: I2,
	/// The result of the division.
	pub(crate) result: I3,
	/// The overflow mode of the propagator.
	pub(crate) overflow_mode: PhantomData<OM>,
}

impl<OM: OverflowMode, I1, I2, I3> IntDivBounds<OM, I1, I2, I3> {
	/// Returns `x + 1`, or `None` if it overflows.
	///
	/// In [`OverflowImpossible`] mode, [`IntDivBounds::can_overflow`] has
	/// ruled out overflow, so the addition is not checked.
	fn checked_inc(x: IntVal) -> Option<IntVal> {
		if OM::HANDLE_OVERFLOW {
			x.checked_add(1)
		} else {
			Some(x + 1)
		}
	}

	/// Returns `x * y`, or `None` if it overflows.
	///
	/// In [`OverflowImpossible`] mode, [`IntDivBounds::can_overflow`] has
	/// ruled out overflow, so the multiplication is not checked.
	fn checked_mul(x: IntVal, y: IntVal) -> Option<IntVal> {
		if OM::HANDLE_OVERFLOW {
			x.checked_mul(y)
		} else {
			Some(x * y)
		}
	}

	/// Propagate the lower bounds of the result and the numerator, and the
	/// bounds of the denominator, if all three are non-negative.
	fn propagate_positive_domains<E, I4, I5, I6>(
		ctx: &mut E::PropagationContext<'_>,
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
			result.tighten_min(ctx, new_res_lb, |ctx, reason| {
				reason.extend([
					numerator.min_lit(ctx),
					denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.max_lit(ctx),
				]);
			})?;
		}

		// An overflow means that the numerator must exceed `IntVal::MAX`, so
		// `IntVal::MAX` is still a sound lower bound.
		let new_num_lb = Self::checked_mul(denom_lb, res_lb).unwrap_or(IntVal::MAX);
		if new_num_lb > num_lb {
			numerator.tighten_min(ctx, new_num_lb, |ctx, reason| {
				reason.extend([denominator.min_lit(ctx), result.min_lit(ctx)]);
			})?;
		}

		if res_lb > 0 {
			let new_denom_ub = num_ub / res_lb;
			if new_denom_ub < denom_ub {
				denominator.tighten_max(ctx, new_denom_ub, |ctx, reason| {
					reason.extend([
						numerator.max_lit(ctx),
						numerator.lit(ctx, IntLitMeaning::GreaterEq(0)),
						result.min_lit(ctx),
						denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					]);
				})?;
			}
		}

		// Skipping this rule on overflow is sound. When the numerator and the
		// denominator are fixed, the result bound rules fix the result.
		if let Some(num_lb_inc) = Self::checked_inc(num_lb)
			&& let Some(res_ub_inc) = Self::checked_inc(res_ub).and_then(NonZero::new)
		{
			let new_denom_lb = div_ceil(num_lb_inc, res_ub_inc);
			if new_denom_lb > denom_lb {
				denominator.tighten_min(ctx, new_denom_lb, |ctx, reason| {
					reason.extend([
						numerator.min_lit(ctx),
						result.max_lit(ctx),
						result.lit(ctx, IntLitMeaning::GreaterEq(0)),
						denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					]);
				})?;
			}
		}

		Ok(())
	}

	/// Propagate the upper bounds of the result and the numerator, if both
	/// upper bounds are non-negative.
	fn propagate_upper_bounds<E, I4, I5, I6>(
		ctx: &mut E::PropagationContext<'_>,
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
				result.tighten_max(ctx, new_res_ub, |ctx, reason| {
					reason.extend([numerator.max_lit(ctx), denominator.min_lit(ctx)]);
				})?;
			}
		}

		// An overflow means that the new upper bound is at least `IntVal::MAX`,
		// so there is nothing to propagate.
		if let Some(res_ub_inc) = Self::checked_inc(res_ub)
			&& let Some(new_num_ub) = Self::checked_mul(res_ub_inc, denom_ub).map(|x| x - 1)
			&& new_num_ub < num_ub
		{
			numerator.tighten_max(ctx, new_num_ub, |ctx, reason| {
				reason.extend([
					denominator.lit(ctx, IntLitMeaning::GreaterEq(1)),
					denominator.max_lit(ctx),
					result.max_lit(ctx),
				]);
			})?;
		}
		Ok(())
	}
}

impl<I1, I2, I3> IntDivBounds<OverflowPossible, I1, I2, I3> {
	/// Returns whether the propagation can overflow [`IntVal`] for the current
	/// bounds of the numerator, the denominator, and the result.
	pub(crate) fn can_overflow<Ctx>(
		ctx: &Ctx,
		numerator: &I1,
		denominator: &I2,
		result: &I3,
	) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntInspectionActions<Ctx>,
		I2: IntInspectionActions<Ctx>,
		I3: IntInspectionActions<Ctx>,
	{
		let abs_max = |(lb, ub): (IntVal, IntVal)| {
			DoubleIntVal::from(lb.unsigned_abs().max(ub.unsigned_abs()))
		};
		let num = abs_max(numerator.bounds(ctx));
		let denom = abs_max(denominator.bounds(ctx));
		let res = abs_max(result.bounds(ctx));
		// The absolute values also cover the negated views in `propagate`.
		[num + 1, res + 1, (res + 1) * denom]
			.into_iter()
			.any(|x| IntVal::try_from(x).is_err())
	}

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
		// Enforce the consistency of the signs of the three variables.
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
			// num >= 0 /\ denom < 0 => res <= 0
			solver.add_clause([!num_pos, !denom_neg, res_neg.clone()])?;
			// num <= 0 /\ denom > 0 => res <= 0
			solver.add_clause([!num_neg, !denom_pos, res_neg])?;
		}

		if Self::can_overflow(solver, &numerator, &denominator, &result) {
			solver.add_propagator(Box::new(IntDivBounds::<OverflowPossible, _, _, _> {
				numerator,
				denominator,
				result,
				overflow_mode: PhantomData,
			}));
		} else {
			solver.add_propagator(Box::new(IntDivBounds::<OverflowImpossible, _, _, _> {
				numerator,
				denominator,
				result,
				overflow_mode: PhantomData,
			}));
		}

		Ok(())
	}
}

impl<OM, E> Constraint<E> for IntDivBounds<OM, View<IntVal>, View<IntVal>, View<IntVal>>
where
	OM: OverflowMode,
	E: ReasoningEngine<Atom = View<bool>>,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	View<IntVal>: IntModelActions<E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		use pindakaas::constraint::propositional_logic::Formula::*;

		// Exclude zero from the domain of the denominator.
		self.denominator.remove_val(ctx, 0, NO_REASON)?;

		// Channel the signs of the decisions.
		let num_pos = self.numerator.lit(ctx, IntLitMeaning::GreaterEq(0));
		let num_neg = self.numerator.lit(ctx, IntLitMeaning::Less(1));
		let denom_pos = self.denominator.lit(ctx, IntLitMeaning::GreaterEq(0));
		let denom_neg = !denom_pos;
		let res_pos = self.result.lit(ctx, IntLitMeaning::GreaterEq(0));
		let res_neg = self.result.lit(ctx, IntLitMeaning::Less(1));

		// num >= 0 /\ denom > 0 => res >= 0
		<PropositionConstraint as Constraint<E>>::simplify(
			&mut PropositionConstraint(Or(vec![!Atom(num_pos), !Atom(denom_pos), Atom(res_pos)])),
			ctx,
		)?;
		// num <= 0 /\ denom < 0 => res >= 0
		<PropositionConstraint as Constraint<E>>::simplify(
			&mut PropositionConstraint(Or(vec![!Atom(num_neg), !Atom(denom_neg), Atom(res_pos)])),
			ctx,
		)?;
		// num >= 0 /\ denom < 0 => res <= 0
		<PropositionConstraint as Constraint<E>>::simplify(
			&mut PropositionConstraint(Or(vec![!Atom(num_pos), !Atom(denom_neg), Atom(res_neg)])),
			ctx,
		)?;
		// num <= 0 /\ denom > 0 => res <= 0
		<PropositionConstraint as Constraint<E>>::simplify(
			&mut PropositionConstraint(Or(vec![!Atom(num_neg), !Atom(denom_pos), Atom(res_neg)])),
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

impl<OM, E, I1, I2, I3> Propagator<E> for IntDivBounds<OM, I1, I2, I3>
where
	OM: OverflowMode,
	E: ReasoningEngine,
	I1: IntSolverActions<E> + Neg + Into<<I1 as Neg>::Output>,
	<I1 as Neg>::Output: IntSolverActions<E>,
	I2: IntSolverActions<E> + Neg + Into<<I2 as Neg>::Output>,
	<I2 as Neg>::Output: IntSolverActions<E>,
	I3: IntSolverActions<E> + Neg + Into<<I3 as Neg>::Output>,
	<I3 as Neg>::Output: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		self.numerator.enqueue_when(ctx, IntPropCond::Bounds);
		self.denominator.enqueue_when(ctx, IntPropCond::Bounds);
		self.result.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(
		name = "int_div_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let (denom_lb, denom_ub) = self.denominator.bounds(ctx);
		if denom_lb < 0 && denom_ub > 0 {
			// Wait until the sign of the denominator is known.
			return Ok(());
		}

		// If the denominator is negative, then swap it and the numerator with
		// their negations.
		let mut denominator = self.denominator.clone().into();
		let mut neg_denom = -self.denominator.clone();
		let mut numerator = self.numerator.clone().into();
		let mut neg_num = -self.numerator.clone();
		let neg_res = -self.result.clone();
		if denom_ub <= 0 {
			mem::swap(&mut denominator, &mut neg_denom);
			mem::swap(&mut numerator, &mut neg_num);
		}

		// If the upper bounds of the numerator and the result are non-negative,
		// then propagate their upper bounds directly.
		if numerator.max(ctx) >= 0 && self.result.max(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &numerator, &denominator, &self.result)?;
		}
		// If their lower bounds are non-positive, then propagate the upper
		// bounds of their negations.
		if neg_num.max(ctx) >= 0 && neg_res.max(ctx) >= 0 {
			Self::propagate_upper_bounds(ctx, &neg_num, &denominator, &neg_res)?;
		}

		// If the numerator and the result are non-negative, then propagate the
		// remaining bounds.
		if numerator.min(ctx) >= 0 && self.result.min(ctx) >= 0 {
			Self::propagate_positive_domains(ctx, &numerator, &denominator, &self.result)?;
		}
		// If the numerator and the result are non-positive, then propagate the
		// remaining bounds of their negations.
		if neg_num.min(ctx) >= 0 && neg_res.min(ctx) >= 0 {
			Self::propagate_positive_domains(ctx, &neg_num, &denominator, &neg_res)?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		constraints::int_div::IntDivBounds,
		model::Model,
		solver::{LiteralStrategy, Solver},
	};

	#[test]
	#[traced_test]
	fn test_int_div_near_max() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(IntVal::MAX - 1..=IntVal::MAX)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(IntVal::MAX..=IntVal::MAX)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(0..=IntVal::MAX)
			.order_literals(LiteralStrategy::Lazy)
			.view();

		IntDivBounds::post(&mut slv, a, b, c).unwrap();

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    9223372036854775806, 9223372036854775807, 0
    9223372036854775807, 9223372036854775807, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_int_div_near_min() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(-IntVal::MAX..=-IntVal::MAX + 2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(-IntVal::MAX..=-IntVal::MAX)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(0..=IntVal::MAX)
			.order_literals(LiteralStrategy::Lazy)
			.view();

		IntDivBounds::post(&mut slv, a, b, c).unwrap();

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    -9223372036854775807, -9223372036854775807, 1
    -9223372036854775806, -9223372036854775807, 0
    -9223372036854775805, -9223372036854775807, 0"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_int_div_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(-7..=7)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(IntSet::from_iter([-3..=-1, 1..=3]))
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(-7..=7)
			.order_literals(LiteralStrategy::Eager)
			.view();

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

		prb.div(num, den).result(res).post().unwrap();

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

	#[test]
	#[traced_test]
	fn test_int_div_unbounded_result() {
		let mut prb = Model::default();
		let num = prb.new_int_decision(7..=7);
		let den = prb.new_int_decision(2..=IntVal::MAX);
		let res = prb.new_int_decision(3..=IntVal::MAX);

		prb.div(num, den).result(res).post().unwrap();

		prb.expect_solutions(
			&[num, den, res],
			expect![[r#"
    7, 2, 3"#]],
		);
	}
}
