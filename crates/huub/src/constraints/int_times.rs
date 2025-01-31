//! Structures and algorithms for the integer times constraint, which enforces
//! that the product of two integer variables is equal to a third integer
//! variable.

use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{
		CachedReason, Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus,
	},
	helpers::{div_ceil, div_floor},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntView},
	IntDecision, NonZeroIntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `times_int` constraint within a model.
///
/// This constraint enforces that the product of the two integer decision
/// variables is equal to a third.
pub struct IntTimes {
	/// First factor variable
	pub(crate) factor1: IntDecision,
	/// Second factor variable
	pub(crate) factor2: IntDecision,
	/// Product variable
	pub(crate) product: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the constraint `z = x * y`.
pub struct IntTimesBounds {
	/// First factor variable
	factor1: IntView,
	/// Second factor variable
	factor2: IntView,
	/// Product variable
	product: IntView,
}

impl<S: SimplificationActions> Constraint<S> for IntTimes {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let (f1_lb, f1_ub) = actions.get_int_bounds(self.factor1);
		let (f2_lb, f2_ub) = actions.get_int_bounds(self.factor2);
		let (prd_lb, prd_ub) = actions.get_int_bounds(self.product);

		let bounds = [f1_lb * f2_lb, f1_lb * f2_ub, f1_ub * f2_lb, f1_ub * f2_ub];
		actions.set_int_lower_bound(self.product, *bounds.iter().min().unwrap())?;
		actions.set_int_upper_bound(self.product, *bounds.iter().max().unwrap())?;

		if f2_lb > 0 || f2_ub < 0 {
			let bounds = [
				(prd_lb, f2_lb),
				(prd_lb, f2_ub),
				(prd_ub, f2_lb),
				(prd_ub, f2_ub),
			];
			let min = bounds
				.iter()
				.filter_map(|(z, y)| {
					let y = NonZeroIntVal::new(*y)?;
					Some(div_ceil(*z, y))
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.factor1, min)?;

			let max = bounds
				.iter()
				.filter_map(|(z, y)| {
					let y = NonZeroIntVal::new(*y)?;
					Some(div_floor(*z, y))
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.factor1, max)?;
		}

		if f1_lb > 0 || f1_ub < 0 {
			let bounds = [
				(prd_lb, f1_lb),
				(prd_lb, f1_ub),
				(prd_ub, f1_lb),
				(prd_ub, f1_ub),
			];
			let min = bounds
				.iter()
				.filter_map(|(z, x)| {
					let x = NonZeroIntVal::new(*x)?;
					Some(div_ceil(*z, x))
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.factor2, min)?;

			let max = bounds
				.iter()
				.filter_map(|(z, x)| {
					let x = NonZeroIntVal::new(*x)?;
					Some(div_floor(*z, x))
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.factor2, max)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let factor1 = slv.get_solver_int(self.factor1);
		let factor2 = slv.get_solver_int(self.factor2);
		let product = slv.get_solver_int(self.product);
		IntTimesBounds::new_in(slv, factor1, factor2, product);
		Ok(())
	}
}

impl IntTimesBounds {
	/// Create a new [`IntTimesBounds`] propagator and post it in the solver.
	pub fn new_in<P>(solver: &mut P, factor1: IntView, factor2: IntView, product: IntView)
	where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				factor1,
				factor2,
				product,
			}),
			PriorityLevel::Highest,
		);

		// Subscribe to bounds changes for each of the variables
		solver.enqueue_on_int_change(prop, factor1, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, factor2, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, product, IntPropCond::Bounds);
	}
}

impl<P, E> Propagator<P, E> for IntTimesBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_times", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (f1_lb, f1_ub) = actions.get_int_bounds(self.factor1);
		let f1_lb_lit = actions.get_int_lower_bound_lit(self.factor1);
		let f1_ub_lit = actions.get_int_upper_bound_lit(self.factor1);
		let (f2_lb, f2_ub) = actions.get_int_bounds(self.factor2);
		let f2_lb_lit = actions.get_int_lower_bound_lit(self.factor2);
		let f2_ub_lit = actions.get_int_upper_bound_lit(self.factor2);
		let (pr_lb, pr_ub) = actions.get_int_bounds(self.product);
		let pr_lb_lit = actions.get_int_lower_bound_lit(self.product);
		let pr_ub_lit = actions.get_int_upper_bound_lit(self.product);

		// TODO: Filter possibilities based on whether variables can be both positive and negative.

		// Calculate possible bounds for the product
		let bounds = [f1_lb * f2_lb, f1_lb * f2_ub, f1_ub * f2_lb, f1_ub * f2_ub];
		let reason_storage = [f1_lb_lit, f1_ub_lit, f2_lb_lit, f2_ub_lit];
		let mut reason = CachedReason::new(&reason_storage[..]);
		// z >= x * y
		let min = bounds.iter().min().unwrap();
		actions.set_int_lower_bound(self.product, *min, &mut reason)?;
		// z <= x * y
		let max = bounds.iter().max().unwrap();
		actions.set_int_upper_bound(self.product, *max, &mut reason)?;

		// Propagate the bounds of the first factor if the second factor is known
		// positive or known negative.
		if f2_lb > 0 || f2_ub < 0 {
			// Calculate possible bounds for the first factor
			let bounds = [
				(pr_lb, f2_lb),
				(pr_lb, f2_ub),
				(pr_ub, f2_lb),
				(pr_ub, f2_ub),
			];
			let reason_storage = [pr_lb_lit, pr_ub_lit, f2_lb_lit, f2_ub_lit];
			let mut reason = CachedReason::new(&reason_storage[..]);
			// factor1 >= product / factor2
			let min = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.factor1, min, &mut reason)?;
			// factor1 <= product / factor2
			let max = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.factor1, max, &mut reason)?;
		}

		// Propagate the bounds of the second factor if the first factor is known
		// positive or known negative.
		if f1_lb > 0 || f1_ub < 0 {
			// Calculate possible bounds for the first factor `y`
			let bounds = [
				(pr_lb, f1_lb),
				(pr_lb, f1_ub),
				(pr_ub, f1_lb),
				(pr_ub, f1_ub),
			];
			let reason_storage = [pr_lb_lit, pr_ub_lit, f1_lb_lit, f1_ub_lit];
			let mut reason = CachedReason::new(&reason_storage[..]);
			// factor2 >= product / factor1
			let min = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.factor2, min, &mut reason)?;
			// factor2 <= product / factor1
			let max = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.factor2, max, &mut reason)?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		constraints::int_times::IntTimesBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
	};

	#[test]
	#[traced_test]
	fn test_int_times_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			(-2..=1).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			(-1..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			(-4..=2).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntTimesBounds::new_in(&mut slv, a, b, c);
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
		-2, -1, 2
		-2, 0, 0
		-2, 1, -2
		-2, 2, -4
		-1, -1, 1
		-1, 0, 0
		-1, 1, -1
		-1, 2, -2
		0, -1, 0
		0, 0, 0
		0, 1, 0
		0, 2, 0
		1, -1, -1
		1, 0, 0
		1, 1, 1
		1, 2, 2"#]],
		);
	}
}
