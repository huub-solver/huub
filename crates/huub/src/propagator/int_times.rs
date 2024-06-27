use crate::{
	actions::{
		explanation::ExplanationActions, initialization::InitializationActions,
		trailing::TrailingActions,
	},
	helpers::{div_ceil, div_floor},
	propagator::{
		conflict::Conflict, int_event::IntEvent, reason::ReasonBuilder, PropagationActions,
		Propagator,
	},
	solver::{
		engine::queue::PriorityLevel,
		poster::{BoxedPropagator, Poster, QueuePreferences},
	},
	IntView, NonZeroIntVal,
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

impl<P, E, T> Propagator<P, E, T> for IntTimesBounds
where
	P: PropagationActions,
	E: ExplanationActions,
	T: TrailingActions,
{
	fn notify_event(&mut self, _: u32, _: &IntEvent, _: &mut T) -> bool {
		true
	}

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
		let reason = ReasonBuilder::Eager(vec![x_lb_lit, x_ub_lit, y_lb_lit, y_ub_lit]);
		// z >= x * y
		let min = bounds.iter().min().unwrap();
		actions.set_int_lower_bound(self.z, *min, &reason)?;
		// z <= x * y
		let max = bounds.iter().max().unwrap();
		actions.set_int_upper_bound(self.z, *max, &reason)?;

		if y_lb > 0 || y_ub < 0 {
			// Calculate possible bounds for the first factor `x`
			let bounds = [(z_lb, y_lb), (z_lb, y_ub), (z_ub, y_lb), (z_ub, y_ub)];
			let reason = ReasonBuilder::Eager(vec![z_lb_lit, z_ub_lit, y_lb_lit, y_ub_lit]);
			// x >= z / y
			let min = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.x, min, &reason)?;
			// x <= z / y
			let max = bounds
				.iter()
				.map(|(z, y)| {
					let y = NonZeroIntVal::new(*y).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.x, max, &reason)?;
		}

		if x_lb > 0 || x_ub < 0 {
			// Calculate possible bounds for the first factor `y`
			let bounds = [(z_lb, x_lb), (z_lb, x_ub), (z_ub, x_lb), (z_ub, x_ub)];
			let reason = ReasonBuilder::Eager(vec![z_lb_lit, z_ub_lit, x_lb_lit, x_ub_lit]);
			// y >= z / x
			let min = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_ceil(*z, y)
				})
				.min()
				.unwrap();
			actions.set_int_lower_bound(self.y, min, &reason)?;
			// y <= z / x
			let max = bounds
				.iter()
				.map(|(z, x)| {
					let y = NonZeroIntVal::new(*x).unwrap();
					div_floor(*z, y)
				})
				.max()
				.unwrap();
			actions.set_int_upper_bound(self.y, max, &reason)?;
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
	) -> (BoxedPropagator, QueuePreferences) {
		actions.subscribe_int(self.x, IntEvent::Bounds, 1);
		actions.subscribe_int(self.y, IntEvent::Bounds, 2);
		actions.subscribe_int(self.z, IntEvent::Bounds, 3);
		(
			Box::new(IntTimesBounds {
				x: self.x,
				y: self.y,
				z: self.z,
			}),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Highest,
			},
		)
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
		let mut slv: Solver<Cadical> = Cnf::default().into();
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

		slv.add_propagator(IntTimesBounds::prepare(a, b, c));
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
