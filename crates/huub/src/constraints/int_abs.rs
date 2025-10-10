//! Structures and algorithms for the integer absolute value constraint, which
//! enforces that one variable is takes absolute value of another.

use std::cmp;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{
		ConstraintInitActions, ExplanationActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, BoolViewInner, IntLitMeaning, IntView,
	},
	IntDecision,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `int_abs` constraint within a model.
///
/// This constraint enforces that the second integer decision variable takes the
/// absolute value of the first integer decision variable.
pub struct IntAbs {
	/// The integer decision variable whose absolute value is being taken
	pub(crate) origin: IntDecision,
	/// The integer decision variable representing the absolute value
	pub(crate) abs: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for one integer variable being the absolute value of
/// another
pub struct IntAbsBounds {
	/// The integer variable whose absolute value is being taken
	origin: IntView,
	/// The integer variable representing the absolute value
	abs: IntView,
	/// Literal that will be true if the origin is zero or positive, and false
	/// otherwise.
	origin_positive: RawLit,
}

impl<S: SimplificationActions> Constraint<S> for IntAbs {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		actions.simplify_on_change_int(self.origin);
		actions.simplify_on_change_int(self.abs);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// Propagate information from the absolute value to the origin.
		let ub = actions.get_int_upper_bound(self.abs);
		actions.set_int_lower_bound(self.origin, -ub)?;
		actions.set_int_upper_bound(self.abs, ub)?;

		// Propagate information from the origin to the absolute value.
		let (lb, ub) = actions.get_int_bounds(self.origin);
		if ub < 0 {
			actions.unify_int(self.abs, -self.origin)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		if lb >= 0 {
			actions.unify_int(self.origin, self.abs)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		actions.set_int_lower_bound(self.abs, 0)?;
		let abs_max = cmp::max(ub, -lb);
		actions.set_int_upper_bound(self.abs, abs_max)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let origin = slv.get_solver_int(self.origin);
		let abs = slv.get_solver_int(self.abs);
		IntAbsBounds::new_in(slv, origin, abs);
		Ok(())
	}
}

impl IntAbsBounds {
	/// Create a new [`IntAbsBounds`] propagator and post it in the solver.
	pub fn new_in<P>(solver: &mut P, origin: IntView, abs: IntView)
	where
		P: PropagatorInitActions + ?Sized,
	{
		let BoolViewInner::Lit(origin_positive) =
			solver.get_int_lit(origin, IntLitMeaning::GreaterEq(0)).0
		else {
			panic!("int_abs constraint cannot be placed on a variable that is known positive or negative");
		};
		let prop = solver.add_propagator(
			Box::new(Self {
				origin,
				abs,
				origin_positive,
			}),
			PriorityLevel::Highest,
		);
		// Subscribe to the bounds of the both variables
		solver.enqueue_on_int_change(prop, origin, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, abs, IntPropCond::Bounds);
	}
}

impl<P, E> Propagator<P, E> for IntAbsBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_abs", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (lb, ub) = actions.get_int_bounds(self.origin);

		match actions.get_bool_val(self.origin_positive.into()) {
			Some(false) => {
				// If we know that the origin is negative, then just negate the bounds
				actions.set_int_lower_bound(self.abs, -ub, |a: &mut P| {
					[a.get_int_upper_bound_lit(self.origin)]
				})?;
				actions.set_int_upper_bound(self.abs, -lb, |a: &mut P| {
					[
						a.get_int_lower_bound_lit(self.origin),
						(!self.origin_positive).into(),
					]
				})?;

				let (lb, ub) = actions.get_int_bounds(self.abs);
				actions.set_int_lower_bound(self.origin, -ub, |a: &mut P| {
					[a.get_int_upper_bound_lit(self.abs)]
				})?;
				actions.set_int_upper_bound(self.origin, -lb, |a: &mut P| {
					[
						a.get_int_lower_bound_lit(self.abs),
						(!self.origin_positive).into(),
					]
				})?;
			}
			Some(true) => {
				// If we know that the origin is positive, then the bounds are the same
				actions.set_int_lower_bound(self.abs, lb, |a: &mut P| {
					[a.get_int_lower_bound_lit(self.origin)]
				})?;
				actions.set_int_upper_bound(self.abs, ub, |a: &mut P| {
					[
						a.get_int_upper_bound_lit(self.origin),
						self.origin_positive.into(),
					]
				})?;

				let (lb, ub) = actions.get_int_bounds(self.abs);
				actions.set_int_upper_bound(self.origin, ub, |a: &mut P| {
					[a.get_int_upper_bound_lit(self.abs)]
				})?;
				actions.set_int_lower_bound(self.origin, lb, |a: &mut P| {
					[
						a.get_int_lower_bound_lit(self.abs),
						self.origin_positive.into(),
					]
				})?;
			}
			None => {
				// If the origin can be either positive or negative, then the bounds are
				// the maximum of the absolute values
				let abs_max = cmp::max(ub, -lb);
				actions.set_int_upper_bound(self.abs, abs_max, |a: &mut P| {
					[
						a.get_int_lit(self.origin, IntLitMeaning::GreaterEq(-abs_max)),
						a.get_int_lit(self.origin, IntLitMeaning::Less(abs_max + 1)),
					]
				})?;

				// If the upper bound of the absolute value variable have changed, we
				// propagate bounds of the origin variable
				let abs_ub = actions.get_int_upper_bound(self.abs);
				let ub_lit = actions.get_int_upper_bound_lit(self.abs);
				actions.set_int_lower_bound(self.origin, -abs_ub, ub_lit)?;
				actions.set_int_upper_bound(self.origin, abs_ub, ub_lit)?;
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
