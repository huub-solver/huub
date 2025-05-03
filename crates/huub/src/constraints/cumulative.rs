//! Structure and algorithms for the cumulative constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
//!
use tracing::trace;
use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, BoolView, IntView},
	IntDecision, IntLitMeaning, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `cumulative` constraint within a model.
///
/// This constraint enforces that all k-dimensional rectangles does no overlap
/// given their starting position `box_posn` and their sizes `box_sizes`.
pub struct Cumulative {
	pub(crate) start: Vec<IntDecision>,
	pub(crate) duration: Vec<IntDecision>,
	pub(crate) resource: Vec<IntDecision>,
	pub(crate) bound: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `cumulative` constraint.
pub struct CumulativeProfile {
	start: Vec<IntView>,
	duration: Vec<IntView>,
	resource: Vec<IntView>,
	bound: IntView,
}

impl<S: SimplificationActions> Constraint<S> for Cumulative {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let start = self.start.iter().map(|v| slv.get_solver_int(*v)).collect();
		let duration = self
			.duration
			.iter()
			.map(|v| slv.get_solver_int(*v))
			.collect();
		let resource = self
			.resource
			.iter()
			.map(|v| slv.get_solver_int(*v))
			.collect();
		let bound = slv.get_solver_int(self.bound);

		CumulativeProfile::new_in(slv, start, duration, resource, bound);
		Ok(())
	}
}

#[derive(Debug, PartialOrd, Ord, Clone, PartialEq, Eq, Hash)]
struct EventPoint {
	time: IntVal,
	height: IntVal,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Rectangle {
	start: IntVal,
	end: IntVal,
	duration: IntVal,
	resource: IntVal,
}

impl Rectangle {
	fn new(start: IntVal, end: IntVal, resource: IntVal) -> Self {
		Self {
			start,
			end,
			duration: end - start,
			resource,
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Profile {
	rectangles: Vec<Rectangle>,
}

impl Profile {
	fn new(rectangles: Vec<Rectangle>) -> Self {
		let mut profile: Vec<Rectangle> = Vec::new();
		let mut event_points: Vec<EventPoint> = Vec::new();

		for i in 0..rectangles.len() {
			let r: &Rectangle = &rectangles[i];
			event_points.push(EventPoint {
				time: r.start,
				height: r.resource,
			});
			event_points.push(EventPoint {
				time: r.start + r.duration,
				height: -r.resource,
			});
		}

		event_points.push(EventPoint {
			time: i32::MIN as i64,
			height: 0,
		});
		event_points.push(EventPoint {
			time: i32::MAX as i64,
			height: 0,
		});

		event_points.sort_by(|a, b| a.time.cmp(&b.time));

		let mut sweep_height = 0;
		let mut sweep_time = event_points[0].time;
		for e in event_points {
			let time = e.time;
			let height = e.height;

			if time != sweep_time {
				profile.push(Rectangle::new(sweep_time, time, sweep_height));
				sweep_time = time;
			}
			sweep_height += height;
		}

        trace!("{:?}\n", profile);

		Self {
			rectangles: profile,
		}
	}

	fn rectangle_index(&self, time: IntVal) -> Option<usize> {
		for i in 0..self.rectangles.len() {
			if self.rectangles[i].start <= time && self.rectangles[i].end > time {
				return Some(i);
			}
		}
		None
	}
}

impl CumulativeProfile {
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
		solver: &mut P,
		start: Vec<IntView>,
		duration: Vec<IntView>,
		resource: Vec<IntView>,
		bound: IntView,
	) {
		let prop = solver.add_propagator(
			Box::new(Self {
				start: start.clone(),
				duration: duration.clone(),
				resource: resource.clone(),
				bound,
			}),
			PriorityLevel::Low,
		);

		for v in start {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}
}

impl<P, E> Propagator<P, E> for CumulativeProfile
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "cumulative", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut mandatory_parts: Vec<Rectangle> = Vec::new();
		for i in 0..self.start.len() {
			if actions.get_int_lower_bound(self.start[i])
				+ actions.get_int_lower_bound(self.duration[i])
				> actions.get_int_upper_bound(self.start[i])
			{
				mandatory_parts.push(Rectangle::new(
					actions.get_int_upper_bound(self.start[i]),
					actions.get_int_lower_bound(self.start[i])
						+ actions.get_int_lower_bound(self.duration[i]),
					actions.get_int_lower_bound(self.resource[i]),
				))
			}
		}

		let profile = Profile::new(mandatory_parts);

		for i in 0..profile.rectangles.len() {
			if profile.rectangles[i].resource > actions.get_int_upper_bound(self.bound) {
				let mut reason = Vec::new();
				for i in 0..self.start.len() {
                    reason.push(actions.get_int_lower_bound_lit(self.start[i]));
                    reason.push(actions.get_int_upper_bound_lit(self.start[i]));
				}
				return Err(Conflict::new(actions, None, reason));
			}
		}

		for i in 0..self.start.len() {
			if actions.get_int_val(self.start[i]).is_none() {
				// Get the index of the profile rectangle overlapping at time start[i])
                let mut min_start = actions.get_int_lower_bound(self.start[i]);
                let mut mandatory_start = -1;
                let mut mandatory_end = -1;
                if actions.get_int_lower_bound(self.start[i])
                    + actions.get_int_lower_bound(self.duration[i])
                    > actions.get_int_upper_bound(self.start[i])
                {
                    mandatory_start = actions.get_int_upper_bound(self.start[i]);
                    mandatory_end = min_start + actions.get_int_lower_bound(self.duration[i]);
                }

                // Iterate through rectangle profiles
                for t in min_start..min_start + actions.get_int_lower_bound(self.duration[i]) {
                    // Make sure the summed up height is larger than the bound
                    //
                    if let Some(j) = profile.rectangle_index(t) {
                        if t < mandatory_start || t >= mandatory_end {
                            if actions.get_int_lower_bound(self.resource[i]) + profile.rectangles[j].resource > actions.get_int_upper_bound(self.bound) {
                                min_start = t + 1;

                            }
                        }

                    }
                }
                let mut reason = Vec::new();
                for i in 0..self.start.len() {
                    reason.push(actions.get_int_lower_bound_lit(self.start[i]));
                    reason.push(actions.get_int_upper_bound_lit(self.start[i]));

                }
                actions.set_int_lower_bound(
                    self.start[i],
                    min_start,
                    reason,
                )?;
            }
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::cumulative::CumulativeProfile,
		cumulative,
		reformulate::InitConfig,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		Decision, Model,
	};

	#[test]
	#[traced_test]
	fn test_cumulative_unsat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let start_1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=8]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let start_2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=8]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let start_3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=8]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let start_4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=8]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		CumulativeProfile::new_in(
			&mut slv,
			vec![start_1, start_2, start_3, start_4],
			vec![2.into(), 2.into(), 2.into(), 2.into()],
			vec![2.into(), 2.into(), 2.into(), 2.into()],
			2.into(),
		);

		slv.assert_all_solutions(&[start_1, start_2, start_3, start_4], |sol| {
			sol.iter().all_unique()
		});
	}
}
