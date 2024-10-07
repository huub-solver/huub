use crate::{
	actions::{explanation::ExplanationActions, initialization::InitializationActions},
	helpers::{div_ceil, div_floor},
	propagator::{conflict::Conflict, reason::CachedReason, PropagationActions, Propagator},
	solver::{
		engine::{activation_list::IntPropCond, queue::PriorityLevel},
		poster::{BoxedPropagator, Poster, QueuePreferences},
	},
	IntView, NonZeroIntVal, ReformulationError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the constraint `z = x * y`.
pub(crate) struct IntTimesBounds {
	/// First variable in the product
	x: IntView,
	/// Second variable in the product
	y: IntView,
	/// Result of the product
	z: IntView,
}

impl IntTimesBounds {
	pub(crate) fn prepare(x: IntView, y: IntView, z: IntView) -> impl Poster {
		IntTimesBoundsPoster { x, y, z }
	}
}

impl<P, E> Propagator<P, E> for IntTimesBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_times", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (x_lb, x_ub) = actions.get_int_bounds(self.x);
		let x_lb_lit = actions.get_int_lower_bound_lit(self.x);
		let x_ub_lit = actions.get_int_upper_bound_lit(self.x);
		let (y_lb, y_ub) = actions.get_int_bounds(self.y);
		let y_lb_lit = actions.get_int_lower_bound_lit(self.y);
		let y_ub_lit = actions.get_int_upper_bound_lit(self.y);
		let (z_lb, z_ub) = actions.get_int_bounds(self.z);
		let z_lb_lit = actions.get_int_lower_bound_lit(self.z);
		let z_ub_lit = actions.get_int_upper_bound_lit(self.z);

		// TODO: Filter possibilities based on whether variables can be both positive and negative.

		// Calculate possible bounds for the product `z`
		let bounds = [x_lb * y_lb, x_lb * y_ub, x_ub * y_lb, x_ub * y_ub];
		let reason_storage = [x_lb_lit, x_ub_lit, y_lb_lit, y_ub_lit];
		let mut reason = CachedReason::new(&reason_storage[..]);
		// z >= x * y
		let min = bounds.iter().min().unwrap();
		actions.set_int_lower_bound(self.z, *min, &mut reason)?;
		// z <= x * y
		let max = bounds.iter().max().unwrap();
		actions.set_int_upper_bound(self.z, *max, &mut reason)?;

		if y_lb > 0 || y_ub < 0 {
			// Calculate possible bounds for the first factor `x`
			let bounds = [(z_lb, y_lb), (z_lb, y_ub), (z_ub, y_lb), (z_ub, y_ub)];
			let reason_storage = [z_lb_lit, z_ub_lit, y_lb_lit, y_ub_lit];
			let mut reason = CachedReason::new(&reason_storage[..]);
			// x >= z / y
			let min = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.x, min, &mut reason)?;
			// x <= z / y
			let max = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.x, max, &mut reason)?;
		}

		if x_lb > 0 || x_ub < 0 {
			// Calculate possible bounds for the first factor `y`
			let bounds = [(z_lb, x_lb), (z_lb, x_ub), (z_ub, x_lb), (z_ub, x_ub)];
			let reason_storage = [z_lb_lit, z_ub_lit, x_lb_lit, x_ub_lit];
			let mut reason = CachedReason::new(&reason_storage[..]);
			// y >= z / x
			let min = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.y, min, &mut reason)?;
			// y <= z / x
			let max = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.y, max, &mut reason)?;
		}
		Ok(())
	}
}

struct IntTimesBoundsPoster {
	x: IntView,
	y: IntView,
	z: IntView,
}
impl Poster for IntTimesBoundsPoster {
	fn post<I: InitializationActions + ?Sized>(
		self,
		actions: &mut I,
	) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
		actions.enqueue_on_int_change(self.x, IntPropCond::Bounds);
		actions.enqueue_on_int_change(self.y, IntPropCond::Bounds);
		actions.enqueue_on_int_change(self.z, IntPropCond::Bounds);
		Ok((
			Box::new(IntTimesBounds {
				x: self.x,
				y: self.y,
				z: self.z,
			}),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Highest,
			},
		))
	}

	fn name(&self) -> &'static str {
		"IntTimesBounds"
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		propagator::int_times::IntTimesBounds,
		solver::engine::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_int_times_sat() {
		let mut slv = Solver::<Cadical>::from(&Cnf::default());
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

		slv.add_propagator(IntTimesBounds::prepare(a, b, c), false)
			.unwrap();
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
