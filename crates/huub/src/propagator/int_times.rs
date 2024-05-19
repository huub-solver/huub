use itertools::Itertools;

use super::{
	conflict::Conflict, int_event::IntEvent, reason::ReasonBuilder, InitializationActions,
	PropagationActions, Propagator,
};
use crate::{
	helpers::{div_ceil, div_floor},
	solver::engine::queue::PriorityLevel,
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
	pub(crate) fn new(x: IntView, y: IntView, z: IntView) -> Self {
		Self { x, y, z }
	}
}

impl Propagator for IntTimesBounds {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		actions.subscribe_int(self.x, IntEvent::Bounds, 1);
		actions.subscribe_int(self.y, IntEvent::Bounds, 2);
		actions.subscribe_int(self.z, IntEvent::Bounds, 3);

		false
	}

	fn notify_event(&mut self, _data: u32, _event: &IntEvent) -> bool {
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Highest
	}

	fn notify_backtrack(&mut self, _new_level: usize) {}

	#[tracing::instrument(name = "int_times", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		let x_lb = actions.get_int_lower_bound(self.x);
		let x_lb_lit = actions.get_int_lower_bound_lit(self.x);
		let x_ub = actions.get_int_upper_bound(self.x);
		let x_ub_lit = actions.get_int_upper_bound_lit(self.x);
		let y_lb = actions.get_int_lower_bound(self.y);
		let y_lb_lit = actions.get_int_lower_bound_lit(self.y);
		let y_ub = actions.get_int_upper_bound(self.y);
		let y_ub_lit = actions.get_int_upper_bound_lit(self.y);
		let z_lb = actions.get_int_lower_bound(self.z);
		let z_lb_lit = actions.get_int_lower_bound_lit(self.z);
		let z_ub = actions.get_int_upper_bound(self.z);
		let z_ub_lit = actions.get_int_upper_bound_lit(self.z);

		// Calculate possible bounds for the product `z`
		let bounds = [x_lb * y_lb, x_lb * y_ub, x_ub * y_lb, x_ub * y_ub];
		let bounds_reason = |pos| {
			ReasonBuilder::Eager(match pos {
				0 => vec![x_lb_lit, y_lb_lit],
				1 => vec![x_lb_lit, y_ub_lit],
				2 => vec![x_ub_lit, y_lb_lit],
				3 => vec![x_ub_lit, y_ub_lit],
				_ => unreachable!(),
			})
		};
		// z >= x * y
		let pos_min = bounds.iter().position_min().unwrap();
		actions.set_int_lower_bound(self.z, bounds[pos_min], &bounds_reason(pos_min))?;
		// z <= x * y
		let pos_max = bounds.iter().position_max().unwrap();
		actions.set_int_upper_bound(self.z, bounds[pos_max], &bounds_reason(pos_max))?;

		if y_lb > 0 || y_ub < 0 {
			// Calculate possible bounds for the first factor `x`
			let bounds = [(z_lb, y_lb), (z_lb, y_ub), (z_ub, y_lb), (z_ub, y_ub)];
			let bounds_reason = |pos| {
				ReasonBuilder::Eager(match pos {
					0 => vec![z_lb_lit, y_lb_lit],
					1 => vec![z_lb_lit, y_ub_lit],
					2 => vec![z_ub_lit, y_lb_lit],
					3 => vec![z_ub_lit, y_ub_lit],
					_ => unreachable!(),
				})
			};
			// x >= z / y
			let pos_min = bounds
				.iter()
				.enumerate()
				.filter_map(|(i, (z, y))| {
					let y = NonZeroIntVal::new(*y)?;
					Some((i, div_ceil(*z, y)))
				})
				.min_by_key(|(_, v)| *v)
				.unwrap();
			actions.set_int_lower_bound(self.x, pos_min.1, &bounds_reason(pos_min.0))?;
			// x <= z / y
			let pos_max = bounds
				.iter()
				.enumerate()
				.filter_map(|(i, (z, y))| {
					let y = NonZeroIntVal::new(*y)?;
					Some((i, div_floor(*z, y)))
				})
				.max_by_key(|(_, v)| *v)
				.unwrap();
			actions.set_int_upper_bound(self.x, pos_max.1, &bounds_reason(pos_max.0))?;
		}

		if x_lb > 0 || x_ub < 0 {
			// Calculate possible bounds for the first factor `y`
			let bounds = [(z_lb, x_lb), (z_lb, x_ub), (z_ub, x_lb), (z_ub, x_ub)];
			let bounds_reason = |pos| {
				ReasonBuilder::Eager(match pos {
					0 => vec![z_lb_lit, x_lb_lit],
					1 => vec![z_lb_lit, x_ub_lit],
					2 => vec![z_ub_lit, x_lb_lit],
					3 => vec![z_ub_lit, x_ub_lit],
					_ => unreachable!(),
				})
			};
			// y >= z / x
			let pos_min = bounds
				.iter()
				.enumerate()
				.filter_map(|(i, (z, x))| {
					let x = NonZeroIntVal::new(*x)?;
					Some((i, div_ceil(*z, x)))
				})
				.min_by_key(|(_, v)| *v)
				.unwrap();
			actions.set_int_lower_bound(self.y, pos_min.1, &bounds_reason(pos_min.0))?;
			// y <= z / x
			let pos_max = bounds
				.iter()
				.enumerate()
				.filter_map(|(i, (z, x))| {
					let x = NonZeroIntVal::new(*x)?;
					Some((i, div_floor(*z, x)))
				})
				.max_by_key(|(_, v)| *v)
				.unwrap();
			actions.set_int_upper_bound(self.y, pos_max.1, &bounds_reason(pos_max.0))?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use super::IntTimesBounds;
	use crate::{solver::engine::int_var::IntVar, Solver};

	#[test]
	fn test_int_times_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, (-2..=1).into(), true);
		let b = IntVar::new_in(&mut slv, (-1..=2).into(), true);
		let c = IntVar::new_in(&mut slv, (-4..=4).into(), true);

		slv.add_propagator(IntTimesBounds::new(a, b, c));
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    -2, 2, -4
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
