//! Structures and algorithms for the integer division constraint, which
//! enforces that a numerator, a denominator, and a result variable are
//! correctly related by integer division.

use std::mem;

use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus},
	helpers::div_ceil,
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
	IntDecision, NonZeroIntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `div_int` constraint within a model.
///
/// This constraint enforces that a numerator decision integer variable divided
/// by a denominator integer decision variable is equal to a result integer
/// decision variable.
///
/// Note that the division is integer division, i.e. the result is rounded
/// towards zero.
pub struct IntDiv {
	/// The numerator of the division
	pub(crate) numerator: IntDecision,
	/// The denominator of the division
	pub(crate) denominator: IntDecision,
	/// Result of the division
	pub(crate) result: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the division of two integer variables.
///
/// This propagator enforces truncating rounding on the result of the division,
/// and enforces that the denominator is non-zero.
pub struct IntDivBounds {
	/// The numerator of the division
	numerator: IntView,
	/// The denominator of the division
	denominator: IntView,
	/// Result of the division
	result: IntView,
}

impl<S: SimplificationActions> Constraint<S> for IntDiv {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		actions.set_int_not_eq(self.denominator, 0)?;
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let numerator = slv.get_solver_int(self.numerator);
		let denominator = slv.get_solver_int(self.denominator);
		let result = slv.get_solver_int(self.result);
		IntDivBounds::new_in(slv, numerator, denominator, result)
	}
}

impl IntDivBounds {
	/// Create a new [`IntDivBounds`] propagator and post it in the solver.
	pub fn new_in<P>(
		solver: &mut P,
		numerator: IntView,
		denominator: IntView,
		result: IntView,
	) -> Result<(), ReformulationError>
	where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				numerator,
				denominator,
				result,
			}),
			PriorityLevel::Highest,
		);
		// Subscribe to bounds changes on each of the variables.
		solver.enqueue_on_int_change(prop, numerator, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, denominator, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, result, IntPropCond::Bounds);

		// Ensure the consistency of the signs of the three variables using the following clauses.
		if solver.get_int_lower_bound(numerator) < 0
			|| solver.get_int_lower_bound(denominator) < 0
			|| solver.get_int_lower_bound(result) < 0
		{
			let num_pos = solver.get_int_lit(numerator, IntLitMeaning::GreaterEq(0));
			let num_neg = solver.get_int_lit(numerator, IntLitMeaning::Less(1));
			let denom_pos = solver.get_int_lit(denominator, IntLitMeaning::GreaterEq(0));
			let denom_neg = !denom_pos;
			let res_pos = solver.get_int_lit(result, IntLitMeaning::GreaterEq(0));
			let res_neg = solver.get_int_lit(result, IntLitMeaning::Less(1));

			// num >= 0 /\ denom > 0 => res >= 0
			solver.add_clause([!num_pos, !denom_pos, res_pos])?;
			// num <= 0 /\ denom < 0 => res >= 0
			solver.add_clause([!num_neg, !denom_neg, res_pos])?;
			// num >= 0 /\ denom < 0 => res < 0
			solver.add_clause([!num_pos, !denom_neg, res_neg])?;
			// num < 0 /\ denom >= 0 => res < 0
			solver.add_clause([!num_neg, !denom_pos, res_neg])?;
		}

		Ok(())
	}

	/// Propagate the result and numerator lower bounds, and the denominator
	/// bounds, assuming all lower bounds are positive.
	fn propagate_positive_domains<P: PropagationActions>(
		actions: &mut P,
		numerator: IntView,
		denominator: IntView,
		result: IntView,
	) -> Result<(), Conflict> {
		let (num_lb, num_ub) = actions.get_int_bounds(numerator);
		let (denom_lb, denom_ub) = actions.get_int_bounds(denominator);
		let (res_lb, res_ub) = actions.get_int_bounds(result);

		let new_res_lb = num_lb / denom_ub;
		if new_res_lb > res_lb {
			actions.set_int_lower_bound(result, new_res_lb, |a: &mut P| {
				[
					a.get_int_lower_bound_lit(numerator),
					a.get_int_lit(denominator, IntLitMeaning::GreaterEq(1)),
					a.get_int_upper_bound_lit(denominator),
				]
			})?;
		}

		let new_num_lb = denom_lb * res_lb;
		if new_num_lb > num_lb {
			actions.set_int_lower_bound(numerator, new_num_lb, |a: &mut P| {
				[
					a.get_int_lower_bound_lit(denominator),
					a.get_int_lower_bound_lit(result),
				]
			})?;
		}

		if res_lb > 0 {
			let new_denom_ub = num_ub / res_lb;
			if new_denom_ub < denom_ub {
				actions.set_int_upper_bound(denominator, new_denom_ub, |a: &mut P| {
					[
						a.get_int_upper_bound_lit(numerator),
						a.get_int_lit(numerator, IntLitMeaning::GreaterEq(0)),
						a.get_int_lower_bound_lit(result),
						a.get_int_lit(denominator, IntLitMeaning::GreaterEq(1)),
					]
				})?;
			}
		}

		if let Some(res_ub_inc) = NonZeroIntVal::new(res_ub + 1) {
			let new_denom_lb = div_ceil(num_lb + 1, res_ub_inc);
			if new_denom_lb > denom_lb {
				actions.set_int_lower_bound(denominator, new_denom_lb, |a: &mut P| {
					[
						a.get_int_lower_bound_lit(numerator),
						a.get_int_upper_bound_lit(result),
						a.get_int_lit(result, IntLitMeaning::GreaterEq(0)),
						a.get_int_lit(denominator, IntLitMeaning::GreaterEq(1)),
					]
				})?;
			}
		}

		Ok(())
	}

	/// Propagate the  upper bounds of the result and numerator, assuming the
	/// signs of the result and the numerator are positive.
	fn propagate_upper_bounds<P: PropagationActions>(
		actions: &mut P,
		numerator: IntView,
		denominator: IntView,
		result: IntView,
	) -> Result<(), Conflict> {
		let num_ub = actions.get_int_upper_bound(numerator);
		let (denom_lb, denom_ub) = actions.get_int_bounds(denominator);
		let res_ub = actions.get_int_upper_bound(result);

		if denom_lb != 0 {
			let new_res_ub = num_ub / denom_lb;
			if new_res_ub < res_ub {
				actions.set_int_upper_bound(result, new_res_ub, |a: &mut P| {
					[
						a.get_int_upper_bound_lit(numerator),
						a.get_int_lower_bound_lit(denominator),
					]
				})?;
			}
		}

		let new_num_ub = (res_ub + 1) * denom_ub - 1;
		if new_num_ub < num_ub {
			actions.set_int_upper_bound(numerator, new_num_ub, |a: &mut P| {
				[
					a.get_int_lit(denominator, IntLitMeaning::GreaterEq(1)),
					a.get_int_upper_bound_lit(denominator),
					a.get_int_upper_bound_lit(result),
				]
			})?;
		}
		Ok(())
	}
}

impl<P, E> Propagator<P, E> for IntDivBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_div", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut denominator = self.denominator;
		let (denom_lb, denom_ub) = actions.get_int_bounds(denominator);
		if denom_lb < 0 && denom_ub > 0 {
			// Wait until the sign of the denominator is known
			return Ok(());
		}

		let mut neg_denom = denominator * NonZeroIntVal::new(-1).unwrap();
		let mut numerator = self.numerator;
		let mut neg_num = numerator * NonZeroIntVal::new(-1).unwrap();
		let neg_res = self.result * NonZeroIntVal::new(-1).unwrap();

		// If the denominator is known negative, then we swap it and the numerator
		// with their negations.
		if denom_ub <= 0 {
			mem::swap(&mut denominator, &mut neg_denom);
			mem::swap(&mut numerator, &mut neg_num);
		}

		// If both the upper bound of the numerator and the upper bound of the
		// right-hand side are positive, then propagate their upper bounds directly.
		if actions.get_int_upper_bound(numerator) >= 0
			&& actions.get_int_upper_bound(self.result) >= 0
		{
			Self::propagate_upper_bounds(actions, numerator, denominator, self.result)?;
		}
		// If their upper bounds are negative, then propagate the upper bounds of
		// the negated versions.
		if actions.get_int_upper_bound(neg_num) >= 0 && actions.get_int_upper_bound(neg_res) >= 0 {
			Self::propagate_upper_bounds(actions, neg_num, denominator, neg_res)?;
		}

		// If the numerator and the results are known positive, then we can
		// propagate the remainder of the bounds under the assumption all values
		// must be positive.
		if actions.get_int_lower_bound(numerator) >= 0
			&& actions.get_int_lower_bound(self.result) >= 0
		{
			Self::propagate_positive_domains(actions, numerator, denominator, self.result)?;
		}
		// If the domain of the numerator and the result are known negative, then
		// propagate their using their negations.
		if actions.get_int_lower_bound(neg_num) >= 0 && actions.get_int_lower_bound(neg_res) >= 0 {
			Self::propagate_positive_domains(actions, neg_num, denominator, neg_res)?;
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
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
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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
