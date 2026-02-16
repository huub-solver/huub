//! Structures and algorithms for the integer power constraint, which enforces
//! that the result of exponentiation of two integer variables is equal to a
//! third integer variable.

use std::marker::PhantomData;

use itertools::{Itertools, MinMaxResult};

use crate::{
	IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, PostingActions, ReasoningContext,
		ReasoningEngine,
	},
	constraints::{
		CachedReason, Constraint, IntModelActions, IntSolverActions, Propagator,
		SimplificationStatus,
	},
	helpers::overflow::{OverflowImpossible, OverflowMode, OverflowPossible},
	lower::{LoweringContext, LoweringError},
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the constraint `result = base^exponent`.
///
/// This constraint enforces that a base integer decision variable
/// exponentiation by an exponent integer decision variable is equal to a result
/// integer decision variable.
///
/// Note that the exponentiation with negative exponents has similar behaviour
/// to integer division, including the fact the constraint will remove any
/// (semi-)division by zero.
///
/// The OVERFLOW parameter determines whether the propagator will expect
/// possible integer overflows.
pub struct IntPowBounds<OM: OverflowMode, I1, I2, I3> {
	/// The base in the exponentiation
	pub(crate) base: I1,
	/// The exponent in the exponentiation
	pub(crate) exponent: I2,
	/// The result of exponentiation
	pub(crate) result: I3,
	/// Phantom data for the overflow mode
	pub(crate) overflow_mode: PhantomData<OM>,
}

/// Calculate the power of a base to an exponent according to the rules of
/// integer arithmetic (matching the MiniZinc semantics), returning whether
/// the result can overflow.
///
/// If the result has overflowed, the function returns the saturated result
/// ([`IntVal::MIN`] or [`IntVal::MAX`] depending on the sign of the base).
///
/// # Panics
/// The function panics when the exponent is negative and the base
/// is zero.
fn overflowing_pow(base: IntVal, exponent: IntVal) -> (IntVal, bool) {
	if exponent < 1 {
		return (pow(base, exponent), false);
	}

	let mut result: IntVal = 1;
	for i in 0..exponent {
		match result.checked_mul(base) {
			Some(v) => result = v,
			None if base.is_negative() && i % 2 == 1 => return (IntVal::MIN, true),
			None => return (IntVal::MAX, true),
		}
	}
	(result, false)
}

/// Calculate the power of a base to an exponent according to the rules of
/// integer arithmetic (matching the MiniZinc semantics).
///
/// # Panics
/// The function panics when the exponent is negative and the base
/// is zero.
fn pow(base: IntVal, exponent: IntVal) -> IntVal {
	match exponent {
		0 => 1,
		1 => base,
		exp if exp < 0 => match base {
			0 => panic!("pow: division by zero"),
			1 => 1,
			-1 if exp % 2 == 0 => 1,
			-1 => -1,
			_ => 0,
		},
		_ => {
			let mut result = 1;
			for _ in 0..exponent {
				result *= base;
			}
			result
		}
	}
}

impl<OM, I1, I2, I3> IntPowBounds<OM, I1, I2, I3>
where
	OM: OverflowMode,
{
	/// Helper function that functions as [`pow`], but uses [`overflowing_pow`]
	/// if `OVERFLOW` is `true`.
	fn pow(base: IntVal, exponent: IntVal) -> IntVal {
		if OM::HANDLE_OVERFLOW {
			overflowing_pow(base, exponent).0
		} else {
			pow(base, exponent)
		}
	}

	/// Propagates the bounds of the base and exponent to the result.
	fn propagate_base<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
	{
		let (base_lb, base_ub) = self.base.bounds(ctx);
		let (res_lb, res_ub) = self.result.bounds(ctx);
		let (exp_lb, exp_ub) = self.exponent.bounds(ctx);
		let exp_pos_even = match exp_lb {
			_ if exp_lb % 2 == 1 && exp_lb > 0 => exp_lb + 1,
			_ if exp_lb < 0 && exp_ub >= 2 => 2,
			_ => exp_lb,
		};
		let exp_pos_uneven = match exp_lb {
			_ if exp_lb % 2 == 0 && exp_lb > 0 => exp_lb + 1,
			_ if exp_lb < 0 && exp_ub >= 1 => 1,
			_ => exp_lb,
		};

		if (exp_lb..=exp_ub).contains(&0) && (res_lb..=res_ub).contains(&1) {
			return Ok(());
		}
		// The following logic does not work for for negative values
		if exp_lb <= 0 || res_lb <= 0 || base_lb <= 0 {
			return Ok(());
		}

		let mut reason = CachedReason::new(|ctx: &mut E::PropagationCtx<'_>| {
			[
				self.result.min_lit(ctx),
				self.result.max_lit(ctx),
				self.exponent.min_lit(ctx),
				self.exponent.max_lit(ctx),
			]
		});

		// Propagate lower bound
		let mut min = [
			(res_lb as f64).powf(1_f64 / (exp_ub as f64)),
			(res_ub as f64).powf(1_f64 / (exp_pos_uneven as f64)),
			(res_lb as f64).powf(1_f64 / (exp_pos_uneven as f64)),
		]
		.into_iter()
		.reduce(|a, b| a.min(b))
		.unwrap()
		.ceil() as IntVal;

		if min > base_lb {
			// Correct possible numerical error
			if (min - 1 != 0 || exp_lb > 0)
				&& res_lb <= Self::pow(min - 1, if min < 0 { exp_pos_uneven } else { exp_ub })
			{
				min -= 1;
			}
			self.base.tighten_min(ctx, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = [
			(res_ub as f64).powf(1_f64 / (exp_lb as f64)),
			(res_ub as f64).powf(1_f64 / (exp_pos_uneven as f64)),
			(res_lb as f64).powf(1_f64 / (exp_pos_even as f64)),
			-((res_lb as f64).powf(1_f64 / (exp_pos_even as f64))),
		]
		.into_iter()
		.reduce(|a, b| a.max(b))
		.unwrap()
		.floor() as IntVal;

		if max < base_ub {
			// Correct possible numerical error
			if res_ub >= Self::pow(max + 1, if min < 0 { exp_pos_even } else { exp_lb }) {
				max += 1;
			}
			self.base.tighten_max(ctx, max, &mut reason)?;
		}
		Ok(())
	}

	/// Filter the bounds of the exponent based on the bounds of the base and
	/// the result.
	fn propagate_exponent<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
	{
		let (base_lb, base_ub) = self.base.bounds(ctx);
		let (res_lb, res_ub) = self.result.bounds(ctx);

		if base_lb <= 1 || res_lb <= 1 {
			// TODO: It seems there should be propagation possible, but log2() certainly
			// won't work.
			return Ok(());
		}

		let (exp_lb, exp_ub) = self.exponent.bounds(ctx);
		let mut reason = CachedReason::new(|ctx: &mut E::PropagationCtx<'_>| {
			[
				self.result.min_lit(ctx),
				self.result.max_lit(ctx),
				self.base.min_lit(ctx),
				self.base.max_lit(ctx),
			]
		});

		// Propagate lower bound
		let mut min = ((res_lb as f64).log2() / (base_ub as f64).log2()).ceil() as IntVal;
		if min > exp_lb {
			// Correct possible numerical error
			if res_lb <= Self::pow(base_lb, min - 1) {
				min -= 1;
			}
			self.exponent.tighten_min(ctx, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = ((res_ub as f64).log2() / (base_lb as f64).log2()).floor() as IntVal;
		if max < exp_ub {
			// Correct possible numerical error
			if res_ub <= Self::pow(base_ub, max + 1) {
				max += 1;
			}
			self.exponent.tighten_max(ctx, max, &mut reason)?;
		}

		Ok(())
	}

	/// Propagates bounds for integer power constraints (`x^y`) over integer
	/// intervals.
	///
	/// This implementation analyzes the extrema of S = { x^y | x ∈ [a, b], y ∈
	/// [c, d] }, where (a, b, c, d) are integer bounds. The main idea is that
	/// the global min/max of S always occur at a small set of candidate (x, y)
	/// pairs, constructed as follows:
	/// - For the base: X = {a, b} ∪ ({0, 1, -1} ∩ [a, b])
	/// - For the exponent: Y = {c, d} ∪ ({0} ∩ [c, d]) ∪ {one even y, one odd y
	///   if both parities appear in [c, d]}
	///
	/// Case-by-case analysis:
	/// 1. For fixed y, extrema of x ↦ x^y on [a, b] are at endpoints, 0 (if
	///    present), ±1 (if present).
	/// 2. For fixed x, extrema of y ↦ x^y on [c, d] are at endpoints, and for x
	///    = ±1, at both an even and odd y (if both exist).
	/// 3. Any global extremum must be an extremum in at least one direction, so
	///    the product of these candidate sets suffices.
	/// 4. Special care is taken for undefined cases (e.g., 0^0 or negative
	///    exponents with base 0).
	///
	/// Thus, by evaluating x^y for all (x, y) in X × Y (excluding undefined
	/// cases), we find the true min and max of S.
	fn propagate_result<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
	{
		let (base_lb, base_ub) = self.base.bounds(ctx);
		let (exp_lb, exp_ub) = self.exponent.bounds(ctx);

		let bounds = base_lb..=base_ub;
		let base_candidates = [
			Some(base_lb),
			Some(base_ub),
			// Add 0, 1, -1 if they are within bounds
			if bounds.contains(&0) { Some(0) } else { None },
			if bounds.contains(&1) { Some(1) } else { None },
			if bounds.contains(&-1) { Some(-1) } else { None },
		];

		let exp_largest_even = if exp_ub % 2 == 0 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_largest_odd = if exp_ub % 2 == 1 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_candidates = [exp_lb, exp_ub, exp_largest_even, exp_largest_odd];

		// Compute the extrema candidates from from `base_candidates` and
		// `exp_candidates`
		let (lb, ub) = match base_candidates
			.iter()
			.flatten()
			.flat_map(|&b| {
				exp_candidates
					.iter()
					.filter(move |&&e| b != 0 || e >= 0)
					.map(move |&e| Self::pow(b, e))
			})
			.minmax()
		{
			MinMaxResult::NoElements => unreachable!(),
			MinMaxResult::OneElement(b) => (b, b),
			MinMaxResult::MinMax(lb, ub) => (lb, ub),
		};

		let mut reason = CachedReason::new(|ctx: &mut E::PropagationCtx<'_>| {
			[
				self.base.min_lit(ctx),
				self.base.max_lit(ctx),
				self.exponent.min_lit(ctx),
				self.exponent.max_lit(ctx),
			]
		});
		self.result.tighten_min(ctx, lb, &mut reason)?;
		self.result.tighten_max(ctx, ub, &mut reason)?;
		Ok(())
	}
}

impl<I1, I2, I3> IntPowBounds<OverflowPossible, I1, I2, I3> {
	/// Returns whether given the bounds of the base and exponent, the result
	/// can overflow.
	///
	/// If this method returns `true`, then the propagator used should have
	/// `OVERFLOW` set to `true`.
	pub(crate) fn can_overflow<Ctx>(ctx: &Ctx, base: &I1, exponent: &I2) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntInspectionActions<Ctx>,
		I2: IntInspectionActions<Ctx>,
	{
		let (base_lb, base_ub) = base.bounds(ctx);
		let exp_ub = exponent.max(ctx);
		if exp_ub <= 0 {
			return false;
		}

		let worst_base = if base_lb.abs() >= base_ub {
			base_lb
		} else {
			base_ub
		};

		let mut acc: IntVal = 1;
		for _ in 0..exp_ub {
			match acc.checked_mul(worst_base) {
				Some(v) => acc = v,
				None => return true,
			}
		}
		false
	}

	/// Create a new [`IntPowBounds`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, base: I1, exponent: I2, result: I3) -> Result<(), E::Conflict>
	where
		E: PostingActions + ?Sized,
		I1: IntDecisionActions<E> + IntSolverActions<Engine>,
		I2: IntDecisionActions<E> + IntSolverActions<Engine>,
		I3: IntDecisionActions<E> + IntSolverActions<Engine>,
	{
		// Ensure that if the base is negative, then the exponent cannot be zero
		let (exp_lb, exp_ub) = exponent.bounds(solver);
		let (base_lb, base_ub) = base.bounds(solver);
		if exp_lb < 0 || (base_lb..=base_ub).contains(&0) {
			// (exp < 0) -> (base != 0)
			let clause = [
				exponent.lit(solver, IntLitMeaning::GreaterEq(0)),
				base.lit(solver, IntLitMeaning::NotEq(0)),
			];
			solver.add_clause(clause)?;
		}

		// Ensure that if the exponent is zero, then the result is one
		if (exp_lb..=exp_ub).contains(&0) {
			// (exp == 0) -> (res == 1)
			let clause = [
				exponent.lit(solver, IntLitMeaning::NotEq(0)),
				result.lit(solver, IntLitMeaning::Eq(1)),
			];
			solver.add_clause(clause)?;
		}

		if Self::can_overflow(solver, &base, &exponent) {
			solver.add_propagator(Box::new(IntPowBounds::<OverflowPossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			}));
		} else {
			solver.add_propagator(Box::new(IntPowBounds::<OverflowImpossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			}));
		}
		Ok(())
	}
}

impl<OM, E, I1, I2, I3> Constraint<E> for IntPowBounds<OM, I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
	I3: IntModelActions<E>,
	OM: OverflowMode,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// If the base is negative, then the exponent cannot be zero
		if self.base.max(ctx) < 0 {
			self.base.remove_val(ctx, 0, [self.base.max_lit(ctx)])?;
		}
		// If the exponent is zero, then the result is one
		if self.exponent.val(ctx) == Some(0) {
			self.result.fix(ctx, 1, |ctx: &mut E::PropagationCtx<'_>| {
				[self.exponent.val_lit(ctx).unwrap()]
			})?;
		}

		self.propagate(ctx)?;

		// Subsume if all variables are fixed.
		if self.base.val(ctx).is_some()
			&& self.exponent.val(ctx).is_some()
			&& self.result.val(ctx).is_some()
		{
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let base = slv.solver_view(self.base.clone().into());
		let exponent = slv.solver_view(self.exponent.clone().into());
		let result = slv.solver_view(self.result.clone().into());
		IntPowBounds::post(slv, base, exponent, result).unwrap();
		Ok(())
	}
}

impl<OM, E, I1, I2, I3> Propagator<E> for IntPowBounds<OM, I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
	I3: IntSolverActions<E>,
	OM: OverflowMode,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		self.base.enqueue_when(ctx, IntPropCond::Bounds);
		self.exponent.enqueue_when(ctx, IntPropCond::Bounds);
		self.result.enqueue_when(ctx, IntPropCond::Bounds);
	}

	#[tracing::instrument(name = "int_pow", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.propagate_result(ctx)?;
		self.propagate_base(ctx)?;
		self.propagate_exponent(ctx)?;

		// Protect against saturation inaccuracy: if `pow(base, exp)` causes
		// overflow, then the `base` and `exp` should be disallowed, but
		// because of the internal saturation used, it will instead allow `IntVal::MAX`
		// or `IntVal::MIN` to be used as the result.
		if OM::HANDLE_OVERFLOW
			&& let Some(base) = self.base.val(ctx)
			&& let Some(exp) = self.exponent.val(ctx)
			&& overflowing_pow(base, exp).1
		{
			self.exponent
				.tighten_max(ctx, exp - 1, |ctx: &mut E::PropagationCtx<'_>| {
					[if base.is_positive() {
						self.base.min_lit(ctx)
					} else {
						self.base.max_lit(ctx)
					}]
				})?;
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
		constraints::int_pow::IntPowBounds,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn test_int_pow_overflow() {
		let mut slv = Solver::default();
		let base = IntDecision::new_in(
			&mut slv,
			(10..=10).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let exponent = IntDecision::new_in(
			&mut slv,
			(18..=19).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let result = IntDecision::new_in(
			&mut slv,
			(0..=IntVal::MAX).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);

		IntPowBounds::post(&mut slv, base, exponent, result)
			.expect("int_pow(a,b,c) was found to be unsatisfiable");

		slv.expect_solutions(
			&[base, exponent, result],
			expect!["10, 18, 1000000000000000000"],
		);
	}

	#[test]
	#[traced_test]
	fn test_int_pow_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			(-2..=3).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntDecision::new_in(
			&mut slv,
			(-2..=2).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntDecision::new_in(
			&mut slv,
			(-2..=9).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntPowBounds::post(&mut slv, a, b, c)
			.expect("int_pow(a,b,c) was found to be unsatisfiable");
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			-2, -2, 0
			-2, -1, 0
			-2, 0, 1
			-2, 1, -2
			-2, 2, 4
			-1, -2, 1
			-1, -1, -1
			-1, 0, 1
			-1, 1, -1
			-1, 2, 1
			0, 0, 1
			0, 1, 0
			0, 2, 0
			1, -2, 1
			1, -1, 1
			1, 0, 1
			1, 1, 1
			1, 2, 1
			2, -2, 0
			2, -1, 0
			2, 0, 1
			2, 1, 2
			2, 2, 4
			3, -2, 0
			3, -1, 0
			3, 0, 1
			3, 1, 3
			3, 2, 9"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_int_pow_underflow() {
		let mut slv = Solver::default();
		let base = IntDecision::new_in(
			&mut slv,
			(-10..=-10).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let exponent = IntDecision::new_in(
			&mut slv,
			(19..=19).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let result = IntDecision::new_in(
			&mut slv,
			(IntVal::MIN..=0).into(),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);

		IntPowBounds::post(&mut slv, base, exponent, result)
			.expect("int_pow(a,b,c) was found to be unsatisfiable");

		slv.assert_unsatisfiable();
	}
}
