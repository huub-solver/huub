//! Structures and algorithms for the `cumulative` constraint.
//! This constraint ensures that the sum of resource usages of all tasks
//! running at any time does not exceed the resource capacity.
//! It uses a time-table propagation approach to efficiently manage the scheduling of tasks.
//!

use itertools::Itertools;
use tracing::trace;

use crate::{
	actions::{
		ExplanationActions, InspectionActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions,
	},
	constraints::{
		Conflict, Constraint, PropagationActions, Propagator, ReasonBuilder, SimplificationStatus,
	},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
	IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `cumulative` constraint within a model.
/// This constraint enforces that the sum of resource usages of all tasks
/// running at any time does not exceed the resource capacity.
pub struct Cumulative {
	/// Start time variables of each task.
	pub(crate) start_times: Vec<IntDecision>,
	/// Durations of each task.
	pub(crate) durations: Vec<IntDecision>,
	/// Resource usages of each task.
	pub(crate) usages: Vec<IntDecision>,
	/// Resource capacity.
	pub(crate) capacity: IntDecision,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum CumulativePropagationRule {
	/// The forward shifting propagation rule.
	ForwardShift,
	/// The backward shifting propagation rule.
	BackwardShift,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `cumulative` constraint using time-table propagation.
/// TODO: update duration, usages and capacity to `IntView`
pub struct CumulativeTimeTable {
	/// Start time variables of each task.
	start_times: Vec<IntView>,
	/// Durations of each task.
	durations: Vec<IntVal>,
	/// Resource usages of each task.
	usages: Vec<IntVal>,
	/// Resource capacity.
	capacity: IntVal,

	// Time Table Profile
	/// Bounds of the time intervals where tasks are active.
	bounds: Vec<i64>,
	/// Heights of the time intervals, representing the total resource usage at that time.
	heights: Vec<IntVal>,
}

impl<S: SimplificationActions> Constraint<S> for Cumulative {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// Check if the cumulative constraint is trivially unsatisfiable
		let mut earliest_start = IntVal::MAX;
		let mut latest_completion = IntVal::MIN;
		let capacity = actions.get_int_lower_bound(self.capacity);
		let mut total_energy = 0;
		for i in 0..self.start_times.len() {
			let duration = actions.get_int_lower_bound(self.durations[i]);
			let usage = actions.get_int_lower_bound(self.usages[i]);
			let est_i = actions.get_int_lower_bound(self.start_times[i]);
			let lst_i = actions.get_int_upper_bound(self.start_times[i]);
			earliest_start = i64::min(earliest_start, est_i);
			latest_completion = i64::max(latest_completion, lst_i + duration);
			if lst_i < est_i + duration {
				total_energy += usage * (est_i + duration - lst_i);
			}
		}
		if total_energy > capacity * (latest_completion - earliest_start) {
			println!(
				"Unsatisfiable {} {} {}",
				total_energy,
				capacity,
				(latest_completion - earliest_start)
			);
			return Err(ReformulationError::TrivialUnsatisfiable);
		}
		// Reformulate the cumulative constraint into a propagator
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let start_times = self
			.start_times
			.iter()
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		let durations = self
			.durations
			.iter()
			.map(|&v| {
				let v = slv.get_solver_int(v);
				// Ensure that durations are fixed to a single value
				let bounds = slv.get_int_bounds(v);
				assert_eq!(
					bounds.0, bounds.1,
					"Cumulative durations must be fixed to a single value."
				);
				bounds.0
			})
			.collect_vec();
		let usages = self
			.usages
			.iter()
			.map(|&v| {
				let v = slv.get_solver_int(v);
				// Ensure that usages are fixed to a single value
				let bounds = slv.get_int_bounds(v);
				assert_eq!(
					bounds.0, bounds.1,
					"Cumulative usages must be fixed to a single value."
				);
				bounds.0
			})
			.collect_vec();
		let capacity = {
			let v = slv.get_solver_int(self.capacity);
			// Ensure that capacity is fixed to a single value
			let bounds = slv.get_int_bounds(v);
			assert_eq!(
				bounds.0, bounds.1,
				"Cumulative capacity must be fixed to a single value."
			);
			bounds.0
		};
		CumulativeTimeTable::new_in(slv, start_times, durations, usages, capacity);
		Ok(())
	}
}

impl CumulativeTimeTable {
	/// Creates a new `CumulativeTimeTable` propagator and post it in
	/// the solver.
	pub fn new_in<P>(
		solver: &mut P,
		start_times: Vec<IntView>,
		durations: Vec<IntVal>,
		usages: Vec<IntVal>,
		capacity: IntVal,
	) where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				start_times: start_times.clone(),
				durations,
				usages,
				capacity,
				bounds: Vec::new(),
				heights: Vec::new(),
			}),
			PriorityLevel::Low,
		);
		for v in start_times {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}

	#[inline]
	/// Get the earliest start time of the task `i`.
	fn earliest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i64 {
		actions.get_int_lower_bound(self.start_times[i])
	}

	#[inline]
	/// Get the latest start time of the task `i`.
	fn latest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i64 {
		actions.get_int_upper_bound(self.start_times[i])
	}

	#[inline]
	/// Get the earliest completion time of the task `i`.
	fn earliest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i64 {
		actions.get_int_lower_bound(self.start_times[i]) + self.durations[i]
	}

	#[inline]
	/// Get the latest completion time of the task `i`.
	fn latest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i64 {
		actions.get_int_upper_bound(self.start_times[i]) + self.durations[i]
	}

	/// Build the time-table profile as a set of (time, height) rectangles.
	/// Returns a tuple (bounds, heights), where bounds[i]..bounds[i+1] is the interval with height heights[i].
	fn build_profile(&mut self, actions: &mut impl PropagationActions) {
		self.bounds.clear();
		self.heights.clear();
		let n = self.start_times.len();
		let mut events = Vec::with_capacity(2 * n);
		// Collect all start and end events of composlary tasks
		for i in 0..n {
			let lst = self.latest_start_time(i, actions);
			let ect = self.earliest_completion_time(i, actions);
			if lst < ect {
				events.push((lst, self.usages[i]));
				events.push((ect, -self.usages[i]));
			}
		}
		// Sort events by time
		events.sort_unstable_by_key(|&(t, _)| t);

		if !events.is_empty() {
			trace!(
				events =? events,
				"Events for compulosary parts from tasks"
			);
		}

		// Build bounds and heights
		let mut cur_height = 0;
		let mut last_time = None;
		for (t, delta) in events {
			if last_time != Some(t) {
				if let Some(lt) = last_time {
					self.bounds.push(lt);
					self.heights.push(cur_height);
				}
				last_time = Some(t);
			}
			cur_height += delta;
		}
		if let Some(lt) = last_time {
			self.bounds.push(lt);
			self.heights.push(cur_height);
		}

		if !self.bounds.is_empty() {
			trace!(
				bounds = ?self.bounds,
				heights = ?self.heights,
				capacity =? self.capacity,
				"Cumulative time table profile"
			);
		}
	}

	/// Forward sweep: for a given task, check if the profile forces its start time to be increased.
	fn sweep_forward(
		&self,
		task: usize,
		actions: &mut impl PropagationActions,
	) -> Result<(), Conflict> {
		let est = self.earliest_start_time(task, actions);
		let lst = self.latest_start_time(task, actions);
		let dur = self.durations[task];
		let usage = self.usages[task];
		// Find the partition point where est > b
		let first = self.bounds.partition_point(|&b| b < est);
		trace!(task, dur, est, lst, usage, "Task sweep forward");
		let mut updated_est = est;
		for i in first..self.bounds.len() - 1 {
			let b_start = self.bounds[i];
			let b_end = self.bounds[i + 1];
			let height = self.heights[i];
			assert!(b_start < b_end);
			if b_start >= lst.min(updated_est + dur) {
				// The task is not left-conflict with any interval forward
				break;
			}
			// if `est` can be push forward (to ≥ `b_end`) and the resource usage is over the capacity
			if updated_est < b_end && usage + height > self.capacity {
				if lst < updated_est + dur && lst <= b_start && b_end <= updated_est + dur {
					// Skip if the task has a compulsory part in this
					// Resource overload is already checked in `check_overload`
					continue;
				}

				let expl_start = updated_est;
				let remainder = (b_end - expl_start).rem_euclid(dur);
				let expl_end = if remainder > 0 {
					b_end - remainder + dur
				} else {
					b_end
				};
				// timepoints for earliest start time
				let timepoints = (expl_start..=expl_end)
					.step_by(dur as usize)
					.map(|t| (b_end).min(t))
					.skip(1)
					.collect_vec();
				trace!(
					updated_est,
					b_end,
					remainder,
					time_points =? timepoints,
					"Propagate forward shifting"
				);

				for t in timepoints {
					if t > updated_est {
						// Set new lower bound for the task's start time
						actions.set_int_lower_bound(
							self.start_times[task],
							t,
							self.explain_sweeping(
								task,
								CumulativePropagationRule::ForwardShift,
								t - 1,
							),
						)?;
						updated_est = t;
					}
				}
			}
		}
		Ok(())
	}

	/// Backward sweep: for a given task, check if the profile forces its latest start time to be decreased.
	fn sweep_backward(
		&self,
		task: usize,
		actions: &mut impl PropagationActions,
	) -> Result<(), Conflict> {
		let est = self.earliest_start_time(task, actions);
		let lst = self.latest_start_time(task, actions);
		let ect = self.earliest_completion_time(task, actions);
		let dur = self.durations[task];
		let usage = self.usages[task];
		// Find the partition point where b < lst + dur
		let last = self.bounds.partition_point(|&b| b < lst + dur);
		trace!(task, dur, est, lst, usage, "Task sweep backward");
		let mut updated_lct = self.latest_completion_time(task, actions);
		for i in (1..last).rev() {
			let b_start = self.bounds[i - 1];
			let b_end = self.bounds[i];
			let height = self.heights[i - 1];
			assert!(b_start < b_end);
			if b_end <= ect.max(updated_lct - dur) {
				// The task is not right-conflict with any interval backward
				break;
			}
			// if `lct` can be push backward (to ≤ `b_end`) and the resource usage is over the capacity
			if updated_lct > b_start && usage + height > self.capacity {
				if updated_lct - dur < ect && updated_lct - dur <= b_start && ect >= b_end {
					// Skip if the task has a compulsory part in this interval
					// Resource overload is already checked in `check_overload`
					continue;
				}

				let expl_end = updated_lct;
				let remainder = (expl_end - b_start).rem_euclid(dur);
				let expl_start = if remainder > 0 {
					b_start + remainder - dur
				} else {
					b_start
				};
				// timepoints for latest completion time
				let timepoints = (expl_start..=expl_end)
					.rev()
					.step_by(dur as usize)
					.map(|t| (b_start).max(t))
					.skip(1)
					.collect_vec();
				trace!(
					updated_lct,
					b_start,
					remainder,
					time_points =? timepoints,
					"Propagate backward shifting"
				);

				for t in timepoints {
					if t < updated_lct {
						// Set new upper bound for the task's start time
						actions.set_int_upper_bound(
							self.start_times[task] + self.durations[task],
							t,
							self.explain_sweeping(
								task,
								CumulativePropagationRule::BackwardShift,
								t,
							),
						)?;
						updated_lct = t;
					}
				}
			}
		}
		Ok(())
	}

	/// Check if the resource usage exceeds capacity at any point in time.
	fn check_overload<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		for i in 0..self.bounds.len() {
			if self.heights[i] > self.capacity {
				// If the cumulative usage exceeds capacity, we have an overload
				// Use the midpoint of the current and next bound as the overload time
				let overload_time = if i != self.bounds.len() - 1 {
					(self.bounds[i] + self.bounds[i + 1]) / 2
				} else {
					self.bounds[i]
				};
				trace!(
					time = overload_time,
					capacity = self.capacity,
					cumulative_usage = self.heights[i],
					"Resource overload"
				);
				return Err(Conflict::new(
					actions,
					None,
					self.explain_overload_timepoint(overload_time),
				));
			}
		}
		Ok(())
	}

	/// Explain why the current set of tasks overloads the resource at time `timepoint`.
	fn explain_overload_timepoint<A: PropagationActions>(
		&self,
		timepoint: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let relevant_tasks = (0..self.start_times.len())
				.filter(|&i| {
					self.latest_start_time(i, actions) <= timepoint
						&& self.earliest_completion_time(i, actions) > timepoint
				})
				.collect_vec();
			trace!(
				timepoint,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.latest_start_time(i, actions),
					self.earliest_completion_time(i, actions),
					self.durations[i]
				)).collect_vec(),
				"Explain resource overload"
			);

			relevant_tasks
				.iter()
				.flat_map(|&i| {
					[
						actions
							.get_int_lit(self.start_times[i], IntLitMeaning::Less(timepoint + 1)),
						actions.get_int_lit(
							self.start_times[i] + self.durations[i],
							IntLitMeaning::GreaterEq(timepoint + 1),
						),
					]
				})
				.collect_vec()
		}
	}

	/// Construct a reason for the task sweeping propagation.
	fn explain_sweeping<A: PropagationActions>(
		&self,
		task_no: usize,
		propagation_rule: CumulativePropagationRule,
		timepoint: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			trace!(
				task_no,
				timepoint =? timepoint,
				rule =? propagation_rule,
				"Explain task sweeping"
			);
			let relevant_tasks = (0..self.start_times.len())
				.filter(|&i| {
					self.latest_start_time(i, actions) <= timepoint
						&& self.earliest_completion_time(i, actions) > timepoint
				})
				.collect_vec();
			assert_ne!(relevant_tasks.len(), 0);
			trace!(
				timepoint,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.durations[i],
					self.latest_start_time(i, actions),
					self.earliest_completion_time(i, actions),
				)).collect_vec(),
				rule =? propagation_rule,
				"Explain task sweeping"
			);

			let mut clause = vec![];

			relevant_tasks.iter().for_each(|&i| {
				clause.push(
					actions.get_int_lit(self.start_times[i], IntLitMeaning::Less(timepoint + 1)),
				);
				clause.push(actions.get_int_lit(
					self.start_times[i] + self.durations[i],
					IntLitMeaning::GreaterEq(timepoint + 1),
				));
			});

			match propagation_rule {
				CumulativePropagationRule::ForwardShift => {
					clause.push(actions.get_int_lit(
						self.start_times[task_no] + self.durations[task_no],
						IntLitMeaning::GreaterEq(timepoint + 1),
					));
				}
				CumulativePropagationRule::BackwardShift => {
					clause.push(actions.get_int_lit(
						self.start_times[task_no],
						IntLitMeaning::Less(timepoint + 1),
					));
				}
			}

			clause
		}
	}
}

impl<P, E> Propagator<P, E> for CumulativeTimeTable
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "cumulative_timetable", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		self.build_profile(actions);

		if !self.bounds.is_empty() {
			// Check if the resource usage exceeds capacity at any point
			self.check_overload(actions)?;

			// Forward sweep: update the earliest start times
			for i in 0..self.start_times.len() {
				let (lb, ub) = actions.get_int_bounds(self.start_times[i]);
				if lb < ub {
					self.sweep_forward(i, actions)?;
					self.sweep_backward(i, actions)?;
				}
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		constraints::cumulative::CumulativeTimeTable,
		solver::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_cumulative_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		let durations = vec![2, 3, 1];
		let resources_profile_1 = vec![1, 2, 3];
		let resources_profile_2 = vec![2, 2, 1];
		CumulativeTimeTable::new_in(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			3,
		);
		CumulativeTimeTable::new_in(&mut slv, vec![a, b, c], durations, resources_profile_2, 2);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    0, 3, 2
    0, 4, 2
    0, 4, 3
    1, 3, 0
    1, 4, 0
    1, 4, 3
    2, 4, 0
    2, 4, 1
    4, 0, 3
    4, 1, 0"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_cumulative_unsat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		let durations = vec![2, 3, 2];
		let resources_profile_1 = vec![2, 2, 3];
		let resources_profile_2 = vec![2, 2, 2];
		CumulativeTimeTable::new_in(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			3,
		);
		CumulativeTimeTable::new_in(&mut slv, vec![a, b, c], durations, resources_profile_2, 3);

		slv.assert_unsatisfiable();
	}
}
