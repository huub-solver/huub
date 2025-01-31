//! Structures and algorithms for the integer power constraint, which enforces
//! that the result of exponentiation of two integer variables is equal to a
//! third integer variable.

use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{CachedReason, Conflict, Constraint, PropagationActions, Propagator},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
	IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `pow_int` constraint within a model.
///
/// This constraint enforces that a base integer decision variable
/// exponentiated by an exponent integer decision variable is equal to a result
/// integer decision variable.
///
/// Note that the exponentiation with negative exponents has similar behaviour
/// to integer division, including the fact the constraint will remove any
/// (semi-)division by zero.
pub struct IntPow {
	/// The base in the exponentiation
	pub(crate) base: IntDecision,
	/// The exponent in the exponentiation
	pub(crate) exponent: IntDecision,
	/// The result of exponentiation
	pub(crate) result: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the constraint `result = base^exponent`.
pub struct IntPowBounds {
	/// The base in the exponentiation
	base: IntView,
	/// The exponent in the exponentiation
	exponent: IntView,
	/// The result of exponentiation
	result: IntView,
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

impl<S: SimplificationActions> Constraint<S> for IntPow {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let base = slv.get_solver_int(self.base);
		let exponent = slv.get_solver_int(self.exponent);
		let result = slv.get_solver_int(self.result);
		IntPowBounds::new_in(slv, base, exponent, result)
	}
}

impl IntPowBounds {
	/// Create a new [`IntPowBounds`] propagator and post it in the solver.
	pub fn new_in<P>(
		solver: &mut P,
		base: IntView,
		exponent: IntView,
		result: IntView,
	) -> Result<(), ReformulationError>
	where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				base,
				exponent,
				result,
			}),
			PriorityLevel::Highest,
		);

		// Subscribe to bounds changes for each of the variables
		solver.enqueue_on_int_change(prop, base, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, exponent, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, result, IntPropCond::Bounds);

		// Ensure that if the base is negative, then the exponent cannot be zero
		let (exp_lb, exp_ub) = solver.get_int_bounds(exponent);
		let (base_lb, base_ub) = solver.get_int_bounds(base);
		if exp_lb < 0 || (base_lb..=base_ub).contains(&0) {
			// (exp < 0) -> (base != 0)
			let clause = [
				solver.get_int_lit(exponent, IntLitMeaning::GreaterEq(0)),
				solver.get_int_lit(base, IntLitMeaning::NotEq(0)),
			];
			solver.add_clause(clause)?;
		}

		// Ensure that if the exponent is zero, then the result is one
		if (exp_lb..=exp_ub).contains(&0) {
			// (exp == 0) -> (res == 1)
			let clause = [
				solver.get_int_lit(exponent, IntLitMeaning::NotEq(0)),
				solver.get_int_lit(result, IntLitMeaning::Eq(1)),
			];
			solver.add_clause(clause)?;
		}

		Ok(())
	}

	/// Propagates the bounds of the base and exponent to the result.
	fn propagate_base<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (res_lb, res_ub) = actions.get_int_bounds(self.result);
		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
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

		let mut reason = CachedReason::new(|actions: &mut P| {
			let res_lb_lit = actions.get_int_lower_bound_lit(self.result);
			let res_ub_lit = actions.get_int_upper_bound_lit(self.result);
			let exp_lb_lit = actions.get_int_lower_bound_lit(self.exponent);
			let exp_ub_lit = actions.get_int_upper_bound_lit(self.exponent);
			vec![res_lb_lit, res_ub_lit, exp_lb_lit, exp_ub_lit]
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
			actions.set_int_lower_bound(self.base, min, &mut reason)?;
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
			actions.set_int_upper_bound(self.base, max, &mut reason)?;
		}
		Ok(())
	}

	/// Filter the bounds of the exponent based on the bounds of the base and the
	/// result.
	fn propagate_exponent<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (res_lb, res_ub) = actions.get_int_bounds(self.result);

		if base_lb <= 1 || res_lb <= 1 {
			// TODO: It seems there should be propagation possible, but log2() certainly won't work.
			return Ok(());
		}

		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
		let mut reason = CachedReason::new(|actions: &mut P| {
			let res_lb_lit = actions.get_int_lit(self.base, IntLitMeaning::GreaterEq(1));
			let res_ub_lit = actions.get_int_upper_bound_lit(self.result);
			let base_lb_lit = actions.get_int_lit(self.base, IntLitMeaning::GreaterEq(1));
			let base_ub_lit = actions.get_int_upper_bound_lit(self.base);
			vec![res_lb_lit, res_ub_lit, base_lb_lit, base_ub_lit]
		});

		// Propagate lower bound
		let mut min = ((res_lb as f64).log2() / (base_ub as f64).log2()).ceil() as IntVal;
		if min > exp_lb {
			// Correct possible numerical error
			if res_lb <= pow(base_lb, min - 1).unwrap() {
				min -= 1;
			}
			actions.set_int_lower_bound(self.base, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = ((res_ub as f64).log2() / (base_lb as f64).log2()).floor() as IntVal;
		if max < exp_ub {
			// Correct possible numerical error
			if res_ub <= pow(base_ub, max + 1).unwrap() {
				max += 1;
			}
			actions.set_int_upper_bound(self.base, max, &mut reason)?;
		}

		Ok(())
	}

	/// Propagate the bounds of result variale based on the bounds of base and
	/// exponent variables.
	fn propagate_result<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
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

		let mut reason = CachedReason::new(|actions: &mut P| {
			let base_lb_lit = actions.get_int_lower_bound_lit(self.base);
			let base_ub_lit = actions.get_int_upper_bound_lit(self.base);
			let exp_lb_lit = actions.get_int_lower_bound_lit(self.exponent);
			let exp_ub_lit = actions.get_int_upper_bound_lit(self.exponent);
			vec![base_lb_lit, base_ub_lit, exp_lb_lit, exp_ub_lit]
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

		actions.set_int_lower_bound(self.result, min, &mut reason)?;

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

		actions.set_int_upper_bound(self.result, max, &mut reason)?;

		Ok(())
	}
}

impl<P, E> Propagator<P, E> for IntPowBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_pow", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		self.propagate_result(actions)?;
		self.propagate_base(actions)?;
		self.propagate_exponent(actions)?;

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
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
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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

		IntPowBounds::new_in(&mut slv, a, b, c)
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
