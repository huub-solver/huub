//! Structures and algorithms for the integer power constraint, which enforces
//! that the result of exponentiation of two integer variables is equal to a
//! third integer variable.

use std::ops::AddAssign;

use pindakaas::{ClauseDatabase, ClauseDatabaseTools, Unsatisfiable};

use crate::{
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, ReasoningEngine,
		ReformulationActions, TrailingActions,
	},
	constraints::{
		BoxedPropagator, CachedReason, Constraint, ModelIntView, Propagator, SimplificationStatus,
		SolverIntView,
	},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, BoolView, IntLitMeaning, IntView,
	},
	IntVal,
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
pub struct IntPowBounds<I1, I2, I3> {
	/// The base in the exponentiation
	pub(crate) base: I1,
	/// The exponent in the exponentiation
	pub(crate) exponent: I2,
	/// The result of exponentiation
	pub(crate) result: I3,
}

/// Calculate the power of a base to an exponent according to the rules of
/// integer arithmetic (matching the MiniZinc semantics).
fn pow(base: IntVal, exponent: IntVal) -> Option<IntVal> {
	Some(match exponent {
		0 => 1,
		1 => base,
		exp if exp < 0 => match base {
			0 => return None,
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
	})
}

impl<I1, I2, I3> IntPowBounds<I1, I2, I3> {
	/// Propagates the bounds of the base and exponent to the result.
	fn propagate_base<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: SolverIntView<E>,
		I2: SolverIntView<E>,
		I3: SolverIntView<E>,
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
			vec![
				self.result.lower_bound_lit(ctx),
				self.result.upper_bound_lit(ctx),
				self.exponent.lower_bound_lit(ctx),
				self.exponent.upper_bound_lit(ctx),
			]
		});

		// Propagate lower bound
		let mut min = vec![
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
				&& res_lb <= pow(min - 1, if min < 0 { exp_pos_uneven } else { exp_ub }).unwrap()
			{
				min -= 1;
			}
			self.base.set_lower_bound(ctx, min, &mut reason)?;
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
			if res_ub >= pow(max + 1, if min < 0 { exp_pos_even } else { exp_lb }).unwrap() {
				max += 1;
			}
			self.base.set_upper_bound(ctx, max, &mut reason)?;
		}
		Ok(())
	}

	/// Filter the bounds of the exponent based on the bounds of the base and
	/// the result.
	fn propagate_exponent<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: SolverIntView<E>,
		I2: SolverIntView<E>,
		I3: SolverIntView<E>,
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
			vec![
				self.result.lower_bound_lit(ctx),
				self.result.upper_bound_lit(ctx),
				self.base.lower_bound_lit(ctx),
				self.base.upper_bound_lit(ctx),
			]
		});

		// Propagate lower bound
		let mut min = ((res_lb as f64).log2() / (base_ub as f64).log2()).ceil() as IntVal;
		if min > exp_lb {
			// Correct possible numerical error
			if res_lb <= pow(base_lb, min - 1).unwrap() {
				min -= 1;
			}
			self.exponent.set_lower_bound(ctx, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = ((res_ub as f64).log2() / (base_lb as f64).log2()).floor() as IntVal;
		if max < exp_ub {
			// Correct possible numerical error
			if res_ub <= pow(base_ub, max + 1).unwrap() {
				max += 1;
			}
			self.exponent.set_upper_bound(ctx, max, &mut reason)?;
		}

		Ok(())
	}

	/// Propagate the bounds of result variable based on the bounds of base and
	/// exponent variables.
	fn propagate_result<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: SolverIntView<E>,
		I2: SolverIntView<E>,
		I3: SolverIntView<E>,
	{
		let (base_lb, base_ub) = self.base.bounds(ctx);
		let (exp_lb, exp_ub) = self.exponent.bounds(ctx);
		let exp_largest_even = if exp_ub % 2 == 0 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_smallest_even = if exp_lb % 2 == 0 || exp_lb == exp_ub {
			exp_lb
		} else {
			exp_lb + 1
		};
		let exp_largest_uneven = if exp_ub % 2 == 1 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_smallest_uneven = if exp_lb % 2 == 1 || exp_lb == exp_ub {
			exp_lb
		} else {
			exp_lb + 1
		};

		let mut reason = CachedReason::new(|ctx: &mut E::PropagationCtx<'_>| {
			vec![
				self.base.lower_bound_lit(ctx),
				self.base.upper_bound_lit(ctx),
				self.exponent.lower_bound_lit(ctx),
				self.exponent.upper_bound_lit(ctx),
			]
		});

		let base_bnd = base_lb..=base_ub;
		let min: IntVal = [
			pow(base_lb, exp_lb),             // base and exp always both positive
			pow(base_lb, exp_largest_uneven), // base maybe negative
			pow(base_ub, exp_smallest_even),  // negative base, but forced even exponent
			if base_bnd.contains(&-1) && exp_lb != exp_ub {
				Some(-1)
			} else if base_bnd.contains(&0)
				|| (base_bnd != (1..=1) && base_bnd != (-1..=-1) && exp_lb < 0)
			{
				Some(0)
			} else {
				None
			},
		]
		.into_iter()
		.flatten()
		.min()
		.unwrap();
		self.result.set_lower_bound(ctx, min, &mut reason)?;

		let max: IntVal = vec![
			pow(base_ub, exp_ub),              // base and exp have positive upper bounds
			pow(base_lb, exp_largest_even),    // base maybe negative
			pow(base_ub, exp_smallest_uneven), // negative base, but forced uneven exponent
			if base_bnd.contains(&-1) && exp_lb != exp_ub {
				Some(1)
			} else if base_bnd.contains(&0)
				|| (base_bnd != (1..=1) && base_bnd != (-1..=-1) && exp_lb < 0)
			{
				Some(0)
			} else {
				None
			},
		]
		.into_iter()
		.flatten()
		.max()
		.unwrap();

		self.result.set_upper_bound(ctx, max, &mut reason)?;
		Ok(())
	}
}

impl IntPowBounds<IntView, IntView, IntView> {
	/// Create a new [`IntPowBounds`] propagator and post it in the solver.
	pub fn post<E>(
		solver: &mut E,
		base: IntView,
		exponent: IntView,
		result: IntView,
	) -> Result<(), Unsatisfiable>
	where
		E: AddAssign<BoxedPropagator> + ClauseDatabase + ?Sized,
		IntView: IntDecisionActions<E, Atom = BoolView>,
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

		*solver += Box::new(Self {
			base,
			exponent,
			result,
		});
		Ok(())
	}
}

impl<E, I1, I2, I3> Constraint<E> for IntPowBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: ModelIntView<E>,
	I2: ModelIntView<E>,
	I3: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// If the base is negative, then the exponent cannot be zero
		if self.base.upper_bound(ctx) < 0 {
			self.base
				.set_not_eq(ctx, 0, [self.base.upper_bound_lit(ctx)])?;
		}
		// If the exponent is zero, then the result is one
		if self.exponent.val(ctx) == Some(0) {
			self.result
				.set_val(ctx, 1, |ctx: &mut E::PropagationCtx<'_>| {
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

	fn to_solver(
		&self,
		slv: &mut dyn ReformulationActions,
		_model_trail: &dyn TrailingActions,
	) -> Result<(), ReformulationError> {
		let base = slv.solver_int(self.base.clone().into());
		let exponent = slv.solver_int(self.exponent.clone().into());
		let result = slv.solver_int(self.result.clone().into());
		IntPowBounds::post(slv, base, exponent, result).unwrap();
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntPowBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
	I3: SolverIntView<E>,
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

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_pow::IntPowBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
	};

	#[test]
	#[traced_test]
	fn test_int_pow_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(-2..=3).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			(-2..=2).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
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
}
