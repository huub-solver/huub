//! Structure and algorithms for the cumulative constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
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
	pub(crate) duration: Vec<IntVal>,
	pub(crate) resource: Vec<IntVal>,
	pub(crate) bound: IntVal,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `cumulative` constraint.
pub struct CumulativeSweep {
	start: Vec<IntView>,
	duration: Vec<IntVal>,
	resource: Vec<IntVal>,
	bound: IntVal,
}

impl<S: SimplificationActions> Constraint<S> for Cumulative {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let start = self.start.iter().map(|v| slv.get_solver_int(*v)).collect();

		CumulativeSweep::new_in(
			slv,
			start,
			self.duration.clone(),
			self.resource.clone(),
			self.bound,
		);
		Ok(())
	}
}

#[derive(PartialOrd, Ord, Clone, PartialEq, Eq, Hash)]
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
			time: IntVal::MIN,
			height: 0,
		});
		event_points.push(EventPoint {
			time: IntVal::MAX,
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

impl CumulativeSweep {
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
		solver: &mut P,
		start: Vec<IntView>,
		duration: Vec<IntVal>,
		resource: Vec<IntVal>,
		bound: IntVal,
	) {
		let prop = solver.add_propagator(
			Box::new(Self {
				start: start.clone(),
				duration,
				resource,
				bound,
			}),
			PriorityLevel::Low,
		);

		for v in start {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}
}

impl<P, E> Propagator<P, E> for CumulativeSweep
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut mandatory_parts: Vec<Rectangle> = Vec::new();
		for i in 0..self.start.len() {
			if actions.get_int_lower_bound(self.start[i]) + self.duration[i]
				> actions.get_int_upper_bound(self.start[i])
			{
				mandatory_parts.push(Rectangle::new(
					actions.get_int_upper_bound(self.start[i]),
					actions.get_int_lower_bound(self.start[i]) + self.duration[i],
					self.resource[i],
				))
			}
		}

		let profile = Profile::new(mandatory_parts);

		for i in 0..profile.rectangles.len() {
			if profile.rectangles[i].resource > self.bound {
				// return Err(Conflict::new(actions, None, 0));
			}
		}

		for i in 0..self.start.len() {
			if actions.get_int_val(self.start[i]).is_none() {
				// Get the index of the profile rectangle overlapping at time start[i])
				if let Some(r_idx) =
					profile.rectangle_index(actions.get_int_lower_bound(self.start[i]))
				{
					// Iterate through rectangle profiles
					for r_profile in r_idx..profile.rectangles.len() {
						let r_profile_height = profile.rectangles[r_profile].resource;
						// Check if activity i has a mandatory part that overlaps with the profile
						if profile.rectangles[r_profile].end
							>= actions.get_int_lower_bound(self.start[i])
							&& profile.rectangles[r_profile].start
								< actions.get_int_lower_bound(self.start[i]) + self.duration[i]
						{
							// Make sure the summed up height is larger than the bound
							if r_profile_height + self.resource[i] > self.bound {
								if profile.rectangles[r_profile].end
									>= actions.get_int_lower_bound(self.start[i])
								{
									// actions.set_int_lower_bound(self.start[i], profile.rectangles[r_profile].end, reason);
								}
							}
						}
					}
				}
			}
		}

		Ok(())
	}
}
