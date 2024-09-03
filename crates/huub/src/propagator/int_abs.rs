use std::iter::once;

use crate::{
	actions::{
		explanation::ExplanationActions, initialization::InitializationActions,
		trailing::TrailingActions,
	},
	propagator::{conflict::Conflict, int_event::IntEvent, PropagationActions, Propagator},
	solver::{
		engine::queue::PriorityLevel,
		poster::{BoxedPropagator, Poster, QueuePreferences},
	},
	IntView, LitMeaning, ReformulationError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for one integer variable being the absolute value of another
pub(crate) struct IntAbsBounds {
	/// The integer variable whose absolute value is being taken
	origin: IntView,
	/// Whether the bounds of the origin variable have changed since the last propagation
	orig_changed: bool,
	/// The integer variable representing the absolute value
	abs: IntView,
	/// Whether the upper bound of the absolute value has changed since the last propagation
	abs_changed: bool,
}

struct IntAbsBoundsPoster {
	origin: IntView,
	abs: IntView,
}

impl IntAbsBounds {
	pub(crate) fn prepare(origin: IntView, abs: IntView) -> impl Poster {
		IntAbsBoundsPoster { origin, abs }
	}
}

impl<P, E, T> Propagator<P, E, T> for IntAbsBounds
where
	P: PropagationActions,
	E: ExplanationActions,
	T: TrailingActions,
{
	fn notify_event(&mut self, data: u32, _: &IntEvent, _: &mut T) -> bool {
		match data {
			1 => self.orig_changed = true,
			2 => self.abs_changed = true,
			_ => unreachable!("unexpected event data"),
		};
		true
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.orig_changed = false;
		self.abs_changed = false;
	}

	#[tracing::instrument(name = "int_abs", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (lb, ub) = actions.get_int_bounds(self.origin);

		if self.orig_changed {
			self.orig_changed = false;
			// If we know that the origin is negative, then just negate the bounds
			if ub < 0 {
				actions.set_int_upper_bound(self.abs, -lb, |a: &mut P| {
					vec![
						a.get_int_lower_bound_lit(self.origin),
						a.get_int_lit(self.origin, LitMeaning::Less(0)),
					]
				})?;
				actions.set_int_lower_bound(self.abs, -ub, |a: &mut P| {
					once(a.get_int_upper_bound_lit(self.origin))
				})?;
			} else if lb >= 0 {
				// If we know that the origin is positive, then the bounds are the same
				actions.set_int_lower_bound(self.abs, lb, |a: &mut P| {
					once(a.get_int_lower_bound_lit(self.origin))
				})?;
				actions.set_int_upper_bound(self.abs, ub, |a: &mut P| {
					vec![
						a.get_int_upper_bound_lit(self.origin),
						a.get_int_lit(self.origin, LitMeaning::GreaterEq(0)),
					]
				})?;
			} else {
				// If the origin can be either positive or negative, then the bounds are the maximum of the absolute values
				let abs_max = ub.max(-lb);
				actions.set_int_upper_bound(self.abs, abs_max, |a: &mut P| {
					vec![
						a.get_int_lit(self.origin, LitMeaning::GreaterEq(-abs_max)),
						a.get_int_lit(self.origin, LitMeaning::Less(abs_max + 1)),
					]
				})?;
			}
		}

		if self.abs_changed {
			self.abs_changed = false;
			let ub = actions.get_int_upper_bound(self.abs);
			let ub_lit = actions.get_int_upper_bound_lit(self.abs);
			actions.set_int_lower_bound(self.origin, -ub, ub_lit)?;
			actions.set_int_upper_bound(self.origin, ub, ub_lit)?;
		}

		Ok(())
	}
}

impl Poster for IntAbsBoundsPoster {
	fn post<I: InitializationActions + ?Sized>(
		self,
		actions: &mut I,
	) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
		// Subscribe to both bounds of the origin variable
		actions.subscribe_int(self.origin, IntEvent::Bounds, 1);
		// Subscribe only to the upper bound of the absolute value variable
		actions.subscribe_int(self.abs, IntEvent::UpperBound, 2);

		Ok((
			Box::new(IntAbsBounds {
				origin: self.origin,
				orig_changed: false,
				abs: self.abs,
				abs_changed: false,
			}),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Highest,
			},
		))
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		propagator::int_abs::IntAbsBounds,
		solver::engine::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_int_abs_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
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
		slv.add_propagator(IntAbsBounds::prepare(a, b)).unwrap();
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
