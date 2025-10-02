//! Structures and algorithms for the `cumulative` constraint.
//! This constraint ensures that the sum of resource usages of all tasks
//! running at any time does not exceed the resource capacity.
//! It uses a time-table propagation approach to efficiently manage the
//! scheduling of tasks.

use itertools::Itertools;
use tracing::trace;

use crate::{
	actions::{
		ConstraintInitActions, ExplanationActions, InspectionActions, PropagatorInitActions,
		ReformulationActions, SimplificationActions,
	},
	constraints::{
		Conflict, Constraint, PropagationActions, Propagator, ReasonBuilder, SimplificationStatus,
	},
	reformulate::ReformulationError,
	solver::{activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView},
	Conjunction, IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `cumulative` constraint within a model.
///
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
/// The propagation rules for the `cumulative` constraint. This enum is
/// used to identify the type of propagation that is being applied. Values:
///
/// - `ForwardShift`: Propagates the earliest start times of tasks forward.
/// - `BackwardShift`: Propagates the latest start times of tasks backward.
enum CumulativePropagationRule {
	/// The forward shifting propagation rule.
	ForwardShift,
	/// The backward shifting propagation rule.
	BackwardShift,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `cumulative` constraint that uses a time-table
/// profile to manage the scheduling of tasks. Refer to the corresponding
/// functions for details on propagation rules and explanations.
///
/// **References**
///
/// - A. Schutt, T. Feydy, P.J. Stuckey, and M. Wallace. Explaining the
///   cumulative propagator. Constraints, 16(3):173-194, 2011.
/// - Gay, Steven, Renaud Hartert, and Pierre Schaus. "Simple and scalable
///   time-table filtering for the cumulative constraint." CP 2015.
pub struct CumulativeTimeTablePropagator {
	/// Start time variables of each task.
	start_times: Vec<IntView>,
	/// Durations of each task.
	durations: Vec<IntView>,
	/// Resource usages of each task.
	usages: Vec<IntView>,
	/// Resource capacity.
	capacity: IntView,

	// Time Table Profile
	/// Bounds of the time intervals where tasks are active.
	bounds: Vec<i64>,
	/// Heights of the time intervals, representing the total resource usage at
	/// that time.
	heights: Vec<IntVal>,
}

impl<S: SimplificationActions> Constraint<S> for Cumulative {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for &i in self
			.start_times
			.iter()
			.chain(&self.durations)
			.chain(&self.usages)
		{
			actions.simplify_on_change_int(i);
		}
		actions.simplify_on_change_int(self.capacity);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// Check if the cumulative constraint is trivially unsatisfiable
		let mut earliest_start = IntVal::MAX;
		let mut latest_completion = IntVal::MIN;
		let capacity = actions.get_int_upper_bound(self.capacity);
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
			trace!(
				"Unsatisfiable {} {} {}",
				total_energy,
				capacity,
				(latest_completion - earliest_start)
			);
			return Err(ReformulationError::TrivialUnsatisfiable);
		}
		// Reformulate the cumulative constraint into a propagator
		Ok(SimplificationStatus::NoFixpoint)
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
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		let usages = self
			.usages
			.iter()
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		let capacity = { slv.get_solver_int(self.capacity) };
		CumulativeTimeTablePropagator::new_in(slv, start_times, durations, usages, capacity);
		Ok(())
	}
}

impl CumulativeTimeTablePropagator {
	/// Build the time-table profile as a set of (time, height) rectangles to
	/// represent the compulsory parts of tasks. The compulsory part of a task
	/// is formed by the interval between its earliest start time and its latest
	/// completion time (i.e. the addition of its latest start time and its
	/// duration lower bound).
	/// The result is a tuple (bounds, heights), where bounds[i]..bounds[i+1]
	/// is the interval in which the cumulative compulsory part is heights[i].
	///
	/// When the profile is built, it checks if the cumulative compulsory part
	/// exceeds the capacity lower bound. If it does, it sets the lower bound
	/// of the capacity variable to the height of the profile at the time point.
	fn build_profile_and_check_overload<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<bool, Conflict> {
		self.bounds.clear();
		self.heights.clear();
		let n = self.start_times.len();
		let mut events = Vec::with_capacity(2 * n);
		let mut capacity_lb = actions.get_int_lower_bound(self.capacity);
		// Collect all start and end events of compulsory tasks
		for i in 0..n {
			let lst = self.latest_start_time(actions, i);
			let ect = self.earliest_completion_time(actions, i);
			let min_usage = actions.get_int_lower_bound(self.usages[i]);
			if lst < ect {
				events.push((lst, min_usage));
				events.push((ect, -min_usage));
			}
		}
		// Sort events by time
		events.sort_unstable_by_key(|&(t, _)| t);

		if !events.is_empty() {
			trace!(
				events =? events,
				"events for compulsory parts from tasks"
			);
		}

		// Build bounds and heights from the events
		// Check if the resource usage exceeds the capacity lower bound
		let mut cur_height = 0;
		let mut last_time = None;
		for (t, delta) in events {
			if last_time != Some(t) {
				if let Some(lt) = last_time {
					self.bounds.push(lt);
					self.heights.push(cur_height);
				}
				if cur_height > capacity_lb {
					trace!(
						timepoint = t,
						capacity_lb,
						cur_height,
						"push capacity lower bound"
					);
					let mid_point = last_time.map_or(t, |lt| (lt + t) / 2);
					actions.set_int_lower_bound(
						self.capacity,
						cur_height,
						self.explain_overload_time_point(cur_height, mid_point),
					)?;
					capacity_lb = cur_height;
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
				capacity_ub =? actions.get_int_upper_bound(self.capacity),
				"cumulative time table profile"
			);
		}
		Ok(self.bounds.is_empty())
	}

	/// A helper function to collect the compulsory tasks that cover a given
	/// amount of energy at a specific time point. This function is used for
	/// explanation.
	fn collect_compulsory_tasks<A: PropagationActions>(
		&self,
		to_cover: i64,
		time_point: i64,
		actions: &mut A,
		skip_task: Option<usize>,
	) -> Vec<usize> {
		// No tasks needed to cover zero or negative energy
		if to_cover <= 0 {
			return Vec::new();
		}

		// Collect a sufficient set of tasks with compulsory parts at `time_point` that
		// cover `to_cover` energy
		let mut relevant_tasks = Vec::new();
		let mut collected_energy = 0;
		for i in 0..self.start_times.len() {
			if Some(i) == skip_task {
				continue; // Skip the task itself
			}
			if self.latest_start_time(actions, i) <= time_point
				&& self.earliest_completion_time(actions, i) > time_point
			{
				let usage_lb = actions.get_int_lower_bound(self.usages[i]);
				if usage_lb > 0 {
					relevant_tasks.push(i);
					collected_energy += usage_lb;
					if collected_energy >= to_cover {
						break;
					}
				}
			}
		}

		// Collect only the minimal set of tasks that cover `to_cover` energy
		let mut remaining_slack = collected_energy - to_cover;
		let mut minimal_relevant_tasks = Vec::new();
		for &i in relevant_tasks.iter() {
			let usage = actions.get_int_lower_bound(self.usages[i]);
			if remaining_slack > usage {
				remaining_slack -= usage;
				continue;
			} else {
				minimal_relevant_tasks.push(i);
			}
		}

		trace!(
			time_point,
			relevant_tasks = ?minimal_relevant_tasks.iter().map(|&i| (
				i,
				self.latest_start_time(actions, i),
				self.earliest_completion_time(actions, i),
				self.durations[i]
			)).collect_vec(),
			"explain resource usage"
		);

		minimal_relevant_tasks
	}

	#[inline]
	/// Get the earliest completion time of the task `i`.
	fn earliest_completion_time<I: InspectionActions>(&self, actions: &mut I, i: usize) -> i64 {
		actions.get_int_lower_bound(self.start_times[i])
			+ actions.get_int_lower_bound(self.durations[i])
	}

	#[inline]
	/// Get the earliest start time of the task `i`.
	fn earliest_start_time<I: InspectionActions>(&self, actions: &mut I, i: usize) -> i64 {
		actions.get_int_lower_bound(self.start_times[i])
	}

	/// Constructs a reason for limiting the usage of a task at a specific
	/// time point. The explanation includes:
	/// (1) relevant tasks (including the target task) that have compulsory
	/// parts at the given time point, which are used to cover the required
	/// resource usage, (2) and the resource capacity at its upper bound.
	fn explain_limit_usage<A: PropagationActions>(
		&self,
		task_no: usize,
		time_point: i64,
		usage_limit: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			trace!(
				task_no,
				timepoint =? time_point,
				usage_limit,
				"Explain task usage limit"
			);
			let capacity_ub = actions.get_int_upper_bound(self.capacity);
			let to_cover = capacity_ub - usage_limit;
			let relevant_tasks =
				self.collect_compulsory_tasks(to_cover, time_point, actions, Some(task_no));

			trace!(
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					actions.get_int_lower_bound(self.durations[i]),
					self.latest_start_time(actions, i),
					self.earliest_completion_time(actions, i),
				)).collect_vec(),
				capacity_ub,
				"Explain task usage limit"
			);

			let mut reason = Conjunction::new();

			// Explanation: (1) relevant tasks (together with task `task_no`) have
			// the required compulsory part at time `time_point`
			relevant_tasks
				.iter()
				.chain(std::iter::once(&task_no))
				.for_each(|&i| {
					reason.push(
						actions
							.get_int_lit(self.start_times[i], IntLitMeaning::Less(time_point + 1)),
					);
					reason.push(actions.get_int_lit(
						self.start_times[i] + actions.get_int_lower_bound(self.durations[i]),
						IntLitMeaning::GreaterEq(time_point + 1),
					));
					reason.push(actions.get_int_lower_bound_lit(self.durations[i]));
					reason.push(actions.get_int_lower_bound_lit(self.usages[i]));
				});

			// Explanation: (2) the resource capacity is at a given level
			reason.push(actions.get_int_upper_bound_lit(self.capacity));

			reason
		}
	}

	/// Construct a reason for why the resource usage is over `to_cover` at a
	/// specific `time_point`. Refer to Schutt et al. (2011) for details on the
	/// explanation construction.
	fn explain_overload_time_point<A: PropagationActions>(
		&self,
		to_cover: i64,
		time_point: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let relevant_tasks = self.collect_compulsory_tasks(to_cover, time_point, actions, None);

			trace!(
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.latest_start_time(actions, i),
					self.earliest_completion_time(actions, i),
					self.durations[i]
				)).collect_vec(),
				"Explain resource overload"
			);

			let mut conflict = Conjunction::new();

			// Explanation: relevant tasks have the required compulsory part at time
			// `time_point`
			relevant_tasks.iter().for_each(|&i| {
				conflict.push(
					actions.get_int_lit(self.start_times[i], IntLitMeaning::Less(time_point + 1)),
				);
				conflict.push(actions.get_int_lit(
					self.start_times[i] + actions.get_int_lower_bound(self.durations[i]),
					IntLitMeaning::GreaterEq(time_point + 1),
				));
				conflict.push(actions.get_int_lower_bound_lit(self.durations[i]));
				conflict.push(actions.get_int_lower_bound_lit(self.usages[i]));
			});

			// Explanation: the resource usage at `time_point` exceeds the upper bound of
			// capacity
			conflict.push(actions.get_int_upper_bound_lit(self.capacity));

			conflict
		}
	}

	/// Construct a reason for the task sweeping explanation.
	/// Refer to Schutt et al. (2011) for details on the explanation
	/// construction.
	fn explain_sweeping_time<A: PropagationActions>(
		&self,
		task_no: usize,
		propagation_rule: CumulativePropagationRule,
		time_point: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let capacity_ub = actions.get_int_upper_bound(self.capacity);
			let min_usage = actions.get_int_lower_bound(self.usages[task_no]);
			let to_cover = capacity_ub - min_usage + 1;
			let relevant_tasks =
				self.collect_compulsory_tasks(to_cover, time_point, actions, Some(task_no));

			trace!(
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					actions.get_int_lower_bound(self.durations[i]),
					self.latest_start_time(actions, i),
					self.earliest_completion_time(actions, i),
				)).collect_vec(),
				rule =? propagation_rule,
				"Explain task sweeping"
			);

			// Construct the reason for the propagation
			let mut reason = Conjunction::new();

			// Explanation: (1) relevant tasks have the required compulsory part at time
			// `time_point`
			relevant_tasks.iter().for_each(|&i| {
				reason.push(
					actions.get_int_lit(self.start_times[i], IntLitMeaning::Less(time_point + 1)),
				);
				reason.push(actions.get_int_lit(
					self.start_times[i] + actions.get_int_lower_bound(self.durations[i]),
					IntLitMeaning::GreaterEq(time_point + 1),
				));
				reason.push(actions.get_int_lower_bound_lit(self.durations[i]));
				reason.push(actions.get_int_lower_bound_lit(self.usages[i]));
			});

			// Explanation: (2) the task itself is either left-conflict or right-conflict
			// with the time point, depending on the propagation rule
			match propagation_rule {
				CumulativePropagationRule::ForwardShift => {
					reason.push(actions.get_int_lit(
						self.start_times[task_no]
							+ actions.get_int_lower_bound(self.durations[task_no]),
						IntLitMeaning::GreaterEq(time_point + 1),
					));
				}
				CumulativePropagationRule::BackwardShift => {
					reason.push(actions.get_int_lit(
						self.start_times[task_no],
						IntLitMeaning::Less(time_point + 1),
					));
				}
			}
			reason.push(actions.get_int_lower_bound_lit(self.durations[task_no]));
			reason.push(actions.get_int_lower_bound_lit(self.usages[task_no]));

			// Explanation: (3) the resource capacity is at a given level
			reason.push(actions.get_int_upper_bound_lit(self.capacity));

			reason
		}
	}

	#[inline]
	/// Get the latest completion time of the task `i`.
	fn latest_completion_time<I: InspectionActions>(&self, actions: &mut I, i: usize) -> i64 {
		actions.get_int_upper_bound(self.start_times[i])
			+ actions.get_int_upper_bound(self.durations[i])
	}

	#[inline]
	/// Get the latest start time of the task `i`.
	fn latest_start_time<I: InspectionActions>(&self, actions: &mut I, i: usize) -> i64 {
		actions.get_int_upper_bound(self.start_times[i])
	}

	/// Propagates the upper bound of a task's resource usage to ensure that,
	/// together with the current resource profile, it does not exceed the
	/// resource capacity.
	///
	/// For the given `task`, this method examines the resource profile (built
	/// from compulsory parts of all tasks) and determines if the task's usage
	/// upper bound must be reduced. It finds the interval where the profile's
	/// height is maximal within the compulsory part of the task, and sets the
	/// task's usage upper bound to `capacity - max_usage + usage_lb`, where
	/// `max_usage` is the maximum compulsory usage in that interval and
	/// `usage_lb` is the lower bound of the task's usage.
	fn limit_usage<P: PropagationActions>(
		&self,
		task: usize,
		actions: &mut P,
	) -> Result<(), Conflict> {
		let lst = self.latest_start_time(actions, task);
		let ect = self.earliest_completion_time(actions, task);
		let dur_lb = actions.get_int_lower_bound(self.durations[task]);
		let usage_lb = actions.get_int_lower_bound(self.usages[task]);

		if !(dur_lb > 0 && usage_lb > 0) {
			// If the task has no duration or usage, no need to sweep
			return Ok(());
		}

		// Find the maximum usage in the interval [lst, ect]
		// where the task has a compulsory part
		let begin = self.bounds.partition_point(|&b| b < lst);
		let mut max_period = begin;
		let mut max_usage = self.heights[begin];
		for i in (begin + 1)..self.bounds.len() {
			if self.bounds[i] >= ect {
				break;
			} else if self.heights[i] > max_usage {
				max_usage = self.heights[i];
				max_period = i;
			}
		}

		let limit = actions.get_int_upper_bound(self.capacity) - max_usage + usage_lb;
		if limit < actions.get_int_upper_bound(self.usages[task]) {
			trace!(
				task,
				compulosary_part =? (lst, ect),
				max_period,
				max_usage,
				limit,
				"Limit task usage"
			);
			actions.set_int_upper_bound(
				self.usages[task],
				limit,
				self.explain_limit_usage(task, self.bounds[max_period], limit),
			)?;
		}
		Ok(())
	}

	/// Creates a new `CumulativeTimeTablePropagator` propagator and post it in
	/// the solver.
	pub fn new_in<P>(
		solver: &mut P,
		start_times: Vec<IntView>,
		durations: Vec<IntView>,
		usages: Vec<IntView>,
		capacity: IntView,
	) where
		P: PropagatorInitActions + ?Sized,
	{
		let prop = solver.add_propagator(
			Box::new(Self {
				start_times: start_times.clone(),
				durations: durations.clone(),
				usages: usages.clone(),
				capacity,
				bounds: Vec::new(),
				heights: Vec::new(),
			}),
			PriorityLevel::Low,
		);
		for v in start_times {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
		for d in durations {
			solver.enqueue_on_int_change(prop, d, IntPropCond::LowerBound);
		}
		for u in usages {
			solver.enqueue_on_int_change(prop, u, IntPropCond::LowerBound);
		}
		solver.enqueue_on_int_change(prop, capacity, IntPropCond::UpperBound);
	}

	/// Performs a backward sweep for a given task to propagate its latest
	/// completion time based on the current cumulative resource profile.
	///
	/// This method checks, for the specified `task`, whether the current
	/// resource profile (built from compulsory parts of all tasks) forces the
	/// task's latest completion time to be decreased in order to avoid
	/// exceeding the resource capacity. It iterates over the profile intervals
	/// in reverse, and if the sum of the task's usage and the profile's height
	/// at an interval exceeds the resource's upper bound, it attempts to push
	/// the task's latest completion time backward. If propagation occurs,
	/// it updates the upper bound of the task's completion time and provides an
	/// explanation for the propagation.
	///
	/// When possible updates on upper bound occur, the method uses a
	/// step-by-step update with the step size being the task's duration lower
	/// bound. This facilitates the generation of point-wise explanations as
	/// described in the original paper by Schutt et al. (2011).
	fn sweep_backward<P: PropagationActions>(
		&self,
		task: usize,
		actions: &mut P,
	) -> Result<(), Conflict> {
		let est = self.earliest_start_time(actions, task);
		let lst = self.latest_start_time(actions, task);
		let ect = self.earliest_completion_time(actions, task);
		let dur_lb = actions.get_int_lower_bound(self.durations[task]);
		let usage_lb = actions.get_int_lower_bound(self.usages[task]);

		if dur_lb <= 0 || usage_lb <= 0 {
			// If the task has no duration or usage, no need to sweep
			return Ok(());
		}

		// Find the partition point where b < lst + dur
		let last = self.bounds.partition_point(|&b| b < lst + dur_lb);
		trace!(task, dur_lb, est, lst, usage_lb, "Task sweep backward");
		let mut updated_lct = self.latest_completion_time(actions, task);
		let max_capacity = actions.get_int_upper_bound(self.capacity);
		for i in (1..last).rev() {
			let b_start = self.bounds[i - 1];
			let b_end = self.bounds[i];
			let height = self.heights[i - 1];
			assert!(b_start < b_end);

			// Stop when the task is not right-conflict with any interval backward
			if b_end <= ect.max(updated_lct - dur_lb) {
				break;
			}
			// if `lct` can be push backward (to ≤ `b_end`) and the resource usage is over
			// the capacity
			if updated_lct > b_start && usage_lb + height > max_capacity {
				if updated_lct - dur_lb < ect && updated_lct - dur_lb <= b_start && ect >= b_end {
					// Skip if the task has a compulsory part in this interval
					// Resource overload is already checked in `check_overload`
					continue;
				}

				let expl_end = updated_lct;
				let remainder = (expl_end - b_start).rem_euclid(dur_lb);
				let expl_start = if remainder > 0 {
					b_start + remainder - dur_lb
				} else {
					b_start
				};
				// time points for latest completion time
				let time_points = (expl_start..=expl_end)
					.rev()
					.step_by(dur_lb as usize)
					.map(|t| (b_start).max(t))
					.skip(1)
					.collect_vec();
				trace!(
					updated_lct,
					b_start,
					remainder,
					time_points =? time_points,
					"propagate backward shifting"
				);

				for t in time_points {
					if t < updated_lct {
						// Set new upper bound for the task's start time
						actions.set_int_upper_bound(
							self.start_times[task] + dur_lb,
							t,
							self.explain_sweeping_time(
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

	/// Performs a forward sweep for a given task to propagate its earliest
	/// start time based on the current cumulative resource profile.
	///
	/// This method checks, for the specified `task`, whether the current
	/// resource profile (built from compulsory parts of all tasks) forces the
	/// task's earliest start time to be increased in order to avoid exceeding
	/// the resource capacity. It iterates over the profile intervals and, if
	/// the sum of the task's usage and the profile's height at an interval
	/// exceeds the resource's upper bound, it attempts to push the task's
	/// earliest start time forward. If propagation occurs, it updates the
	/// lower bound of the task's start time and provides an explanation
	/// for the propagation.
	///
	/// When possible updates on lower bound occur, the method use a
	/// step-by-step update with the step size being the task's duration lower
	/// bound. This facilitates the generation of point-wise explanations as
	/// described in the original paper by Schutt et al. (2011).
	fn sweep_forward<P: PropagationActions>(
		&self,
		task: usize,
		actions: &mut P,
	) -> Result<(), Conflict> {
		let est = self.earliest_start_time(actions, task);
		let lst = self.latest_start_time(actions, task);
		let dur_lb = actions.get_int_lower_bound(self.durations[task]);
		let usage_lb = actions.get_int_lower_bound(self.usages[task]);

		if dur_lb <= 0 || usage_lb <= 0 {
			// If the task has no duration or usage, no need to sweep
			return Ok(());
		}

		// Find the partition point where est > b
		let first = self.bounds.partition_point(|&b| b < est);
		trace!(task, dur_lb, est, lst, usage_lb, "Task sweep forward");
		let mut updated_est = est;
		let max_capacity = actions.get_int_upper_bound(self.capacity);
		for i in first..self.bounds.len() - 1 {
			let b_start = self.bounds[i];
			let b_end = self.bounds[i + 1];
			let height = self.heights[i];
			assert!(b_start < b_end);
			// Stop when the task is not left-conflict with any interval forward
			if b_start >= lst.min(updated_est + dur_lb) {
				break;
			}
			// if `est` can be push forward (to ≥ `b_end`) and the resource usage is over
			// the capacity
			if updated_est < b_end && usage_lb + height > max_capacity {
				if lst < updated_est + dur_lb && lst <= b_start && b_end <= updated_est + dur_lb {
					// Skip if the task has a compulsory part in this
					// Resource overload is already checked in `check_overload`
					continue;
				}

				let expl_start = updated_est;
				let remainder = (b_end - expl_start).rem_euclid(dur_lb);
				let expl_end = if remainder > 0 {
					b_end - remainder + dur_lb
				} else {
					b_end
				};
				// time points for earliest start time updates
				let time_points = (expl_start..=expl_end)
					.step_by(dur_lb as usize)
					.map(|t| (b_end).min(t))
					.skip(1)
					.collect_vec();
				trace!(
					updated_est,
					b_end,
					remainder,
					time_points =? time_points,
					"propagate forward shifting"
				);

				for t in time_points {
					if t > updated_est {
						// Set new lower bound for the task's start time
						actions.set_int_lower_bound(
							self.start_times[task],
							t,
							self.explain_sweeping_time(
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
}

// impl<P, E> Propagator<P, E> for CumulativeTimeTablePropagator
// where
// 	P: PropagationActions,
// 	E: ExplanationActions,
// {
// 	#[tracing::instrument(name = "cumulative_timetable", level = "trace",
// skip(self, actions))] 	fn propagate(&mut self, actions: &mut P) -> Result<(),
// P::Conflict> { 		// Build the time-table profile and check resource overload
// 		match self.build_profile_and_check_overload(actions) {
// 			// If the profile is empty, no tasks are active, so we can skip further
// 			// propagation
// 			Ok(true) => return Ok(()),
// 			// If there is a conflict, return it
// 			Err(conflict) => return Err(conflict),
// 			_ => {}
// 		}

// 		// Sweeping time: update the earliest start times and the latest completion
// 		// times
// 		for i in 0..self.start_times.len() {
// 			let (lb, ub) = actions.get_int_bounds(self.start_times[i]);
// 			if lb < ub {
// 				self.sweep_forward(i, actions)?;
// 				self.sweep_backward(i, actions)?;
// 			}
// 		}

// 		// Limit usage: update the upper bounds of the resource usage
// 		for i in 0..self.start_times.len() {
// 			let (req_lb, req_ub) = actions.get_int_bounds(self.usages[i]);
// 			if req_lb < req_ub
// 				&& self.latest_start_time(actions, i) <
// self.earliest_completion_time(actions, i) 			{
// 				self.limit_usage(i, actions)?;
// 			}
// 		}
// 		Ok(())
// 	}
// }

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		constraints::cumulative::CumulativeTimeTablePropagator,
		solver::{
			int_var::{EncodingType, IntVar},
			IntView,
		},
		Solver,
	};

	/// Helper function to create a task with given start time, duration, and
	/// usage.
	fn create_task(
		slv: &mut Solver,
		start_time: RangeList<i64>,
		duration: RangeList<i64>,
		usage: RangeList<i64>,
	) -> (IntView, IntView, IntView) {
		let start = IntVar::new_in(slv, start_time, EncodingType::Eager, EncodingType::Lazy);
		let dur = IntVar::new_in(slv, duration, EncodingType::Eager, EncodingType::Lazy);
		let usage = IntVar::new_in(slv, usage, EncodingType::Eager, EncodingType::Lazy);
		(start, dur, usage)
	}

	#[test]
	#[traced_test]
	fn test_cumulative_val_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(0..=4).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			(0..=4).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			(0..=4).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		let durations: Vec<IntView> = [2, 3, 1].into_iter().map_into().collect();
		let resources_profile_1 = [1, 2, 3].into_iter().map_into().collect();
		let resources_profile_2 = [2, 2, 1].into_iter().map_into().collect();
		let capacity_1 = 3.into();
		let capacity_2 = 2.into();
		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			capacity_1,
		);
		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![a, b, c],
			durations,
			resources_profile_2,
			capacity_2,
		);

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
	fn test_cumulative_val_unsat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			(0..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			(0..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			(0..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		let durations: Vec<IntView> = [2, 3, 2].into_iter().map_into().collect();
		let resources_profile_1: Vec<IntView> = [2, 2, 3].into_iter().map_into().collect();
		let resources_profile_2: Vec<IntView> = [2, 2, 2].into_iter().map_into().collect();
		let capacity = 3.into();

		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			capacity,
		);
		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![a, b, c],
			durations,
			resources_profile_2,
			capacity,
		);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_capacity_sat() {
		let mut slv = Solver::default();
		let start = [0, 3, 4, 6, 8, 8].into_iter().map_into().collect();
		let duration = [3, 2, 5, 2, 1, 4].into_iter().map_into().collect();
		let usage = [2, 3, 1, 4, 3, 2].into_iter().map_into().collect();
		let capacity = IntVar::new_in(
			&mut slv,
			(1..=6).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		CumulativeTimeTablePropagator::new_in(&mut slv, start, duration, usage, capacity);

		slv.expect_solutions(&[capacity], expect![[r#"6"#]]);
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_capacity_unsat() {
		let mut slv = Solver::default();
		let start = [0, 3, 4, 6, 8, 8].into_iter().map_into().collect();
		let duration = [3, 2, 5, 2, 1, 4].into_iter().map_into().collect();
		let usage = [2, 3, 1, 4, 3, 2].into_iter().map_into().collect();
		let capacity = IntVar::new_in(
			&mut slv,
			(1..=4).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		CumulativeTimeTablePropagator::new_in(&mut slv, start, duration, usage, capacity);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_dur_sat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([1..=3]),
			RangeList::from_iter([2..=2]),
		);

		let (s_b, d_b, u_b) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([1..=3]),
			RangeList::from_iter([2..=2]),
		);

		let (s_c, d_c, u_c) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([1..=3]),
			RangeList::from_iter([2..=2]),
		);
		let capacity = 2.into();

		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
		);

		slv.expect_solutions(
			&[s_a, s_b, s_c, d_a, d_b, d_c],
			expect![[r#"
    0, 1, 2, 1, 1, 1
    0, 1, 2, 1, 1, 2
    0, 1, 2, 1, 1, 3
    0, 2, 1, 1, 1, 1
    0, 2, 1, 1, 2, 1
    0, 2, 1, 1, 3, 1
    1, 0, 2, 1, 1, 1
    1, 0, 2, 1, 1, 2
    1, 0, 2, 1, 1, 3
    1, 2, 0, 1, 1, 1
    1, 2, 0, 1, 2, 1
    1, 2, 0, 1, 3, 1
    2, 0, 1, 1, 1, 1
    2, 0, 1, 2, 1, 1
    2, 0, 1, 3, 1, 1
    2, 1, 0, 1, 1, 1
    2, 1, 0, 2, 1, 1
    2, 1, 0, 3, 1, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_dur_unsat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=3]),
			RangeList::from_iter([2..=2]),
		);

		let (s_b, d_b, u_b) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=3]),
			RangeList::from_iter([2..=2]),
		);

		let (s_c, d_c, u_c) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=3]),
			RangeList::from_iter([2..=2]),
		);
		let capacity = 2.into();

		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
		);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_usage_sat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([1..=1]),
			RangeList::from_iter([1..=2]),
		);

		let (s_b, d_b, u_b) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([3..=3]),
			RangeList::from_iter([2..=3]),
		);

		let (s_c, d_c, u_c) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=2]),
			RangeList::from_iter([2..=3]),
		);
		let capacity = 3.into();

		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
		);

		slv.expect_solutions(
			&[s_a, s_b, s_c, u_a, u_b, u_c],
			expect![[r#"
    0, 2, 0, 1, 2, 2
    0, 2, 0, 1, 3, 2
    1, 2, 0, 1, 2, 2
    1, 2, 0, 1, 3, 2
    2, 2, 0, 1, 2, 2
    2, 2, 0, 1, 2, 3"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_usage_unsat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=2]),
			RangeList::from_iter([1..=3]),
		);

		let (s_b, d_b, u_b) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=2]),
			RangeList::from_iter([2..=3]),
		);

		let (s_c, d_c, u_c) = create_task(
			&mut slv,
			RangeList::from_iter([0..=2]),
			RangeList::from_iter([2..=2]),
			RangeList::from_iter([2..=3]),
		);
		let capacity = 2.into();

		CumulativeTimeTablePropagator::new_in(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
		);

		slv.assert_unsatisfiable();
	}
}
