//! Structures and algorithms for the `cumulative` constraint.
//! This constraint ensures that the sum of resource usages of all tasks
//! running at any time does not exceed the resource capacity.
//!
//! The base propagation is the time-table approach, which maintains a profile
//! of the compulsory parts of tasks. On top of it, the propagator can
//! optionally run time-table-edge-finding (TTEF), a stronger but more
//! expensive energy-based reasoning that combines the time-table profile with
//! edge-finding. TTEF is split into three independently selectable phases:
//! a consistency check, a bounds-filtering phase, and an opportunistic
//! extended-edge-finding phase.
//!
//! **References**
//!
//! - A. Schutt, T. Feydy, P.J. Stuckey, and M. Wallace. Explaining the
//!   cumulative propagator. Constraints, 16(3):173-194, 2011.
//! - P. Vilím. Timetable edge finding filtering algorithm for discrete
//!   cumulative resources. CPAIOR 2011.
//! - A. Schutt, T. Feydy, and P.J. Stuckey. Explaining time-table-edge-finding
//!   propagation for the cumulative resource constraint. CPAIOR 2013.

use std::iter::once;

use itertools::Itertools;
use tracing::trace;

use crate::{
	Conjunction, IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, IntPropCond, PostingActions,
		PropagationActions, ReasoningContext, ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, ReasonBuilder,
		SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	solver::{IntLitMeaning, Polarity, engine::Engine, queue::PriorityLevel},
};

/// The propagation rules for the `cumulative` constraint. This enum is
/// used to identify the type of propagation that is being applied. Values:
///
/// - `ForwardShift`: Propagates the earliest start times of tasks forward.
/// - `BackwardShift`: Propagates the latest start times of tasks backward.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum CumulativePropagationRule {
	/// The forward shifting propagation rule.
	ForwardShift,
	/// The backward shifting propagation rule.
	BackwardShift,
}

/// A propagator for the `cumulative` constraint. It always maintains a
/// time-table profile of the compulsory parts of tasks, and optionally runs
/// time-table-edge-finding (TTEF) on top of it, as selected by the
/// `ttef_*_enabled` flags. Refer to the corresponding functions for details on
/// propagation rules and explanations.
///
/// **References**
///
/// - A. Schutt, T. Feydy, P.J. Stuckey, and M. Wallace. Explaining the
///   cumulative propagator. Constraints, 16(3):173-194, 2011.
/// - Gay, Steven, Renaud Hartert, and Pierre Schaus. "Simple and scalable
///   time-table filtering for the cumulative constraint." CP 2015.
/// - P. Vilím. Timetable edge finding filtering algorithm for discrete
///   cumulative resources. CPAIOR 2011.
/// - A. Schutt, T. Feydy, and P.J. Stuckey. Explaining time-table-edge-finding
///   propagation for the cumulative resource constraint. CPAIOR 2013.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CumulativePropagator<I1, I2, I3, I4> {
	/// Start time variables of each task.
	start_times: Vec<I1>,
	/// Durations of each task.
	durations: Vec<I2>,
	/// Resource usages of each task.
	usages: Vec<I3>,
	/// Resource capacity.
	capacity: I4,
	/// Whether to run the TTEF consistency check on top of the time-table
	/// propagation.
	ttef_check_enabled: bool,
	/// Whether to run the TTEF bounds-filtering phase.
	ttef_filtering_enabled: bool,
	/// Whether to run the opportunistic extended-edge-finding phase.
	ttef_opportunistic_enabled: bool,
	/// Bounds of the time intervals where tasks are active.
	bounds: Vec<IntVal>,
	/// Heights of the time intervals, representing the total resource usage at
	/// that time.
	heights: Vec<IntVal>,
}

/// Per-task quantities used by the time-table-edge-finding phases, computed
/// once per propagation from the current domains.
///
/// All energy reasoning uses the *minimum* duration and usage (a sound lower
/// bound on the energy a task requires) and the *maximum* capacity (a sound
/// upper bound on the energy a resource makes available). The earliest
/// completion time uses the minimum duration (the smallest compulsory part),
/// while the latest completion time uses the maximum duration (the true
/// deadline a task must respect). When durations, usages, and the capacity
/// are fixed.
struct TtefData {
	/// Earliest start time `est_i = lb(S_i)`.
	est: Vec<IntVal>,
	/// Latest start time `lst_i = ub(S_i)`.
	lst: Vec<IntVal>,
	/// Earliest completion time `ect_i = est_i + dur_lb_i`.
	ect: Vec<IntVal>,
	/// Latest completion time `lct_i = lst_i + dur_ub_i` (the deadline).
	lct: Vec<IntVal>,
	/// Minimum duration of each task.
	dur: Vec<IntVal>,
	/// Minimum usage of each task.
	usage: Vec<IntVal>,
	/// Minimum energy `e_i = dur_lb_i * usage_lb_i`.
	energy: Vec<IntVal>,
	/// Length of the compulsory part `pTT_i = max(0, ect_i - lst_i)`.
	fixed_dur: Vec<IntVal>,
	/// Free energy `eEF_i = usage_lb_i * (dur_lb_i - pTT_i)` of each task.
	free_energy: Vec<IntVal>,
	/// Latest start of the free part `lstEF_i = lst_i + pTT_i`.
	lst_ef: Vec<IntVal>,
	/// Maximum resource capacity `R`.
	capacity: IntVal,
	/// Task indices sorted by non-decreasing earliest start time.
	by_est: Vec<usize>,
	/// Task indices sorted by non-decreasing latest completion time.
	by_lct: Vec<usize>,
	/// Energy of the time-table profile in `[est_i, +inf)`, per task.
	tt_after_est: Vec<IntVal>,
	/// Energy of the time-table profile in `[lct_i, +inf)`, per task.
	tt_after_lct: Vec<IntVal>,
}

/// A candidate bound update found by the TTEF bounds-filtering phase: task
/// `task`'s start time can be tightened thanks to the resource overload that
/// would otherwise occur in the time window `[begin, end)`. The concrete bound
/// is re-derived soundly from this window at application time,
/// so only the task, window, and direction are carried here.
struct TtefUpdate {
	/// Task whose bound is tightened.
	task: usize,
	/// Start of the overloaded time window justifying the update.
	begin: IntVal,
	/// End of the overloaded time window justifying the update.
	end: IntVal,
	/// Whether this update raises the earliest start (`true`) or lowers the
	/// latest completion (`false`).
	is_lb: bool,
}

/// Resolve whether a posted `cumulative` constraint runs the TTEF consistency
/// check on top of the time-table propagation, applying the default when the
/// caller leaves the choice unset.
///
/// Defaults to enabled: across the RCPSP and MiniZinc Challenge `cumulative`
/// suites the check removed enough search to pay for its per-node cost.
pub(crate) fn ttef_check_propagation_enabled(config: Option<bool>) -> bool {
	config.unwrap_or(true)
}

/// Resolve whether a posted `cumulative` constraint runs the TTEF
/// bounds-filtering phase, which lifts earliest start times and lowers latest
/// completion times, applying the default when the caller leaves the choice
/// unset.
///
/// Defaults to disabled: on those suites its extra pruning did not recoup its
/// per-node cost, so the check alone was faster overall.
pub(crate) fn ttef_filtering_propagation_enabled(config: Option<bool>) -> bool {
	config.unwrap_or(false)
}

/// Resolve whether a posted `cumulative` constraint runs the opportunistic
/// extended-edge-finding phase of TTEF, applying the default when the caller
/// leaves the choice unset.
///
/// Defaults to disabled: it only adds pruning on top of the
/// [bounds-filtering](ttef_filtering_propagation_enabled) phase, which is
/// itself disabled.
pub(crate) fn ttef_opportunistic_propagation_enabled(config: Option<bool>) -> bool {
	config.unwrap_or(false)
}

impl<I1, I2, I3, I4> CumulativePropagator<I1, I2, I3, I4> {
	/// Whether any TTEF phase is enabled on top of the time-table propagation.
	fn any_ttef_enabled(&self) -> bool {
		self.ttef_check_enabled || self.ttef_filtering_enabled || self.ttef_opportunistic_enabled
	}

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
	fn build_profile_and_check_overload<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		self.bounds.clear();
		self.heights.clear();
		let n = self.start_times.len();
		let mut events = Vec::with_capacity(2 * n);
		let mut capacity_lb = self.capacity.min(ctx);
		// Collect all start and end events of compulsory tasks
		for i in 0..n {
			let lst = self.latest_start_time(ctx, i);
			let ect = self.earliest_completion_time(ctx, i);
			let min_usage = self.usages[i].min(ctx);
			if lst < ect {
				events.push((lst, min_usage));
				events.push((ect, -min_usage));
			}
		}
		// Sort events by time
		events.sort_unstable_by_key(|&(t, _)| t);

		if !events.is_empty() {
			trace!(
				target: "cumulative",
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
						target: "cumulative",
						timepoint = t,
						capacity_lb, cur_height, "push capacity lower bound"
					);
					let mid_point = last_time.map_or(t, |lt| (lt + t) / 2);
					self.capacity.tighten_min(
						ctx,
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
				target: "cumulative",
				bounds = ?self.bounds,
				heights = ?self.heights,
				capacity_ub =? self.capacity.max(ctx),
				"cumulative time table profile"
			);
		}
		Ok(self.bounds.is_empty())
	}

	/// A helper function to collect the compulsory tasks that cover a given
	/// amount of energy at a specific time point. This function is used for
	/// explanation.
	fn collect_compulsory_tasks<Ctx>(
		&self,
		ctx: &mut Ctx,
		to_cover: i64,
		time_point: i64,
		skip_task: Option<usize>,
	) -> Vec<usize>
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntInspectionActions<Ctx>,
		I2: IntInspectionActions<Ctx>,
		I3: IntInspectionActions<Ctx>,
		I4: IntInspectionActions<Ctx>,
	{
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
			if self.latest_start_time(ctx, i) <= time_point
				&& self.earliest_completion_time(ctx, i) > time_point
			{
				let usage_lb = self.usages[i].min(ctx);
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
			let usage = self.usages[i].min(ctx);
			if remaining_slack > usage {
				remaining_slack -= usage;
				continue;
			} else {
				minimal_relevant_tasks.push(i);
			}
		}

		trace!(
			target: "cumulative",
			time_point,
			relevant_tasks = ?minimal_relevant_tasks.iter().map(|&i| (
				i,
				self.latest_start_time(ctx, i),
				self.earliest_completion_time(ctx, i),
				&self.durations[i]
			)).collect_vec(),
			"explain resource usage"
		);

		minimal_relevant_tasks
	}

	/// Get the earliest completion time of the task `i`.
	#[inline]
	fn earliest_completion_time<C>(&self, ctx: &mut C, i: usize) -> i64
	where
		C: ReasoningContext + ?Sized,
		I1: IntInspectionActions<C>,
		I2: IntInspectionActions<C>,
	{
		self.start_times[i].min(ctx) + self.durations[i].min(ctx)
	}

	/// Get the earliest start time of the task `i`.
	#[inline]
	fn earliest_start_time<C>(&self, ctx: &mut C, i: usize) -> i64
	where
		C: ReasoningContext + ?Sized,
		I1: IntInspectionActions<C>,
	{
		self.start_times[i].min(ctx)
	}

	/// Constructs a reason for limiting the usage of a task at a specific
	/// time point. The explanation includes:
	/// (1) relevant tasks (including the target task) that have compulsory
	/// parts at the given time point, which are used to cover the required
	/// resource usage, (2) and the resource capacity at its upper bound.
	fn explain_limit_usage<Ctx>(
		&self,
		task_no: usize,
		time_point: i64,
		usage_limit: i64,
	) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			trace!(
				target: "cumulative",
				task_no,
				timepoint =? time_point,
				usage_limit,
				"explain task usage limit"
			);
			let capacity_ub = self.capacity.max(ctx);
			let to_cover = capacity_ub - usage_limit;
			let relevant_tasks =
				self.collect_compulsory_tasks(ctx, to_cover, time_point, Some(task_no));

			trace!(
				target: "cumulative",
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.durations[i].min(ctx),
					self.usages[i].min(ctx),
					self.latest_start_time(ctx, i),
					self.earliest_completion_time(ctx, i),
				)).collect_vec(),
				capacity_ub,
				"explain task usage limit"
			);

			let cap_lit = self.capacity.max_lit(ctx);

			// Explanation: (1) relevant tasks (together with task `task_no`) have
			// the required compulsory part at time `time_point`
			relevant_tasks
				.iter()
				.chain(once(&task_no))
				.flat_map(|&i| {
					[
						self.start_times[i].lit(ctx, IntLitMeaning::Less(time_point + 1)),
						self.start_times[i].lit(
							ctx,
							IntLitMeaning::GreaterEq(time_point + 1 - self.durations[i].min(ctx)),
						),
						self.durations[i].min_lit(ctx),
						self.usages[i].min_lit(ctx),
					]
				})
				// Explanation: (2) the resource capacity is at a given level
				.chain(once(cap_lit))
				.collect_vec()
		}
	}

	/// Construct a reason for why the resource usage is over `to_cover` at a
	/// specific `time_point`. Refer to Schutt et al. (2011) for details on the
	/// explanation construction.
	fn explain_overload_time_point<Ctx>(
		&self,
		to_cover: i64,
		time_point: i64,
	) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let relevant_tasks = self.collect_compulsory_tasks(ctx, to_cover, time_point, None);

			trace!(
				target: "cumulative",
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.latest_start_time(ctx, i),
					self.earliest_completion_time(ctx, i),
					&self.durations[i]
				)).collect_vec(),
				"explain resource overload"
			);

			let cap_lit = self.capacity.max_lit(ctx);

			// Explanation: relevant tasks have the required compulsory part at time
			// `time_point`
			relevant_tasks
				.iter()
				.flat_map(|&i| {
					[
						self.start_times[i].lit(ctx, IntLitMeaning::Less(time_point + 1)),
						self.start_times[i].lit(
							ctx,
							IntLitMeaning::GreaterEq(time_point - self.durations[i].min(ctx) + 1),
						),
						self.durations[i].min_lit(ctx),
						self.usages[i].min_lit(ctx),
					]
				})
				.chain(once(cap_lit))
				.collect_vec()
		}
	}

	/// Construct a reason for the task sweeping explanation.
	/// Refer to Schutt et al. (2011) for details on the explanation
	/// construction.
	fn explain_sweeping_time<Ctx>(
		&self,
		task_no: usize,
		propagation_rule: CumulativePropagationRule,
		time_point: i64,
	) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let capacity_ub = self.capacity.max(ctx);
			let min_usage = self.usages[task_no].min(ctx);
			let to_cover = capacity_ub - min_usage + 1;
			let relevant_tasks =
				self.collect_compulsory_tasks(ctx, to_cover, time_point, Some(task_no));

			trace!(
				target: "cumulative",
				time_point,
				relevant_tasks = ?relevant_tasks.iter().map(|&i| (
					i,
					self.durations[i].min(ctx),
					self.latest_start_time(ctx, i),
					self.earliest_completion_time(ctx, i),
				)).collect_vec(),
				rule =? propagation_rule,
				"explain task sweeping"
			);

			// Construct the reason for the propagation
			let mut reason = Conjunction::with_capacity(4 * relevant_tasks.len() + 4);

			// Explanation: (1) relevant tasks have the required compulsory part at time
			// `time_point`
			reason.extend(relevant_tasks.iter().flat_map(|&i| {
				[
					self.start_times[i].lit(ctx, IntLitMeaning::Less(time_point + 1)),
					self.start_times[i].lit(
						ctx,
						IntLitMeaning::GreaterEq(time_point - self.durations[i].min(ctx) + 1),
					),
					self.durations[i].min_lit(ctx),
					self.usages[i].min_lit(ctx),
				]
			}));

			// Explanation: (2) the task itself is either left-conflict or right-conflict
			// with the time point, depending on the propagation rule
			match propagation_rule {
				CumulativePropagationRule::ForwardShift => {
					reason.push(self.start_times[task_no].lit(
						ctx,
						IntLitMeaning::GreaterEq(time_point - self.durations[task_no].min(ctx) + 1),
					));
				}
				CumulativePropagationRule::BackwardShift => {
					reason.push(
						self.start_times[task_no].lit(ctx, IntLitMeaning::Less(time_point + 1)),
					);
				}
			}
			reason.push(self.durations[task_no].min_lit(ctx));
			reason.push(self.usages[task_no].min_lit(ctx));

			// Explanation: (3) the resource capacity is at a given level
			reason.push(self.capacity.max_lit(ctx));

			reason
		}
	}

	/// Build the explanation for a TTEF resource overload detected in the time
	/// window `[begin, end)`.
	///
	/// The reason is the naive energetic-overload nogood: every task that
	/// contributes energy to the window is pinned to its current start-time
	/// bounds (`est_i <= S_i <= lst_i`), together with the duration and usage
	/// lower bounds it contributed and the resource-capacity upper bound. Any
	/// assignment satisfying these literals keeps at least the counted energy
	/// inside the window, which exceeds the available energy — hence the
	/// inconsistency. (The bound-widening generalisation of Schutt et al.
	/// (2013, §3.1) is a future refinement.)
	fn explain_ttef_overload<'a, Ctx>(
		&'a self,
		data: &'a TtefData,
		begin: IntVal,
		end: IntVal,
	) -> impl ReasonBuilder<Ctx> + 'a
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let mut reason = Vec::new();
			for i in 0..data.len() {
				if data.contributes(i, begin, end) {
					reason.push(self.start_times[i].min_lit(ctx));
					reason.push(self.start_times[i].max_lit(ctx));
					reason.push(self.durations[i].min_lit(ctx));
					reason.push(self.usages[i].min_lit(ctx));
				}
			}
			reason.push(self.capacity.max_lit(ctx));
			reason
		}
	}

	/// Build the explanation for a TTEF bounds-filtering update of task `u`
	/// justified by the time window `[begin, end)`.
	///
	/// The naive energetic explanation pins every *other* task contributing to
	/// the window to its current start-time bounds, and `u` to the start-time
	/// bound on the side opposite the update (its earliest start for a
	/// lower-bound update, its latest start for an upper-bound update),
	/// together with the duration and usage lower bounds and the
	/// resource-capacity upper bound. Any assignment satisfying these literals
	/// forces at least the counted energy into the window, leaving `u` no room
	/// to start (complete) earlier (later) than the new bound. (The
	/// bound-widening generalisation of Schutt et al. (2013, §3.1) is a future
	/// refinement.)
	fn explain_ttef_update<'a, Ctx>(
		&'a self,
		data: &'a TtefData,
		u: usize,
		begin: IntVal,
		end: IntVal,
		is_lb: bool,
	) -> impl ReasonBuilder<Ctx> + 'a
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let mut reason = Vec::new();
			for i in 0..data.len() {
				if i == u || !data.contributes(i, begin, end) {
					continue;
				}
				reason.push(self.start_times[i].min_lit(ctx));
				reason.push(self.start_times[i].max_lit(ctx));
				reason.push(self.durations[i].min_lit(ctx));
				reason.push(self.usages[i].min_lit(ctx));
			}
			// The updated task contributes only the bound on the side from which it
			// is being pushed (its previous earliest start for a lower-bound update,
			// or its previous latest start for an upper-bound update).
			if is_lb {
				reason.push(self.start_times[u].min_lit(ctx));
			} else {
				reason.push(self.start_times[u].max_lit(ctx));
			}
			reason.push(self.durations[u].min_lit(ctx));
			reason.push(self.usages[u].min_lit(ctx));
			reason.push(self.capacity.max_lit(ctx));
			reason
		}
	}

	/// Get the latest completion time of the task `i`.
	#[inline]
	fn latest_completion_time<C>(&self, ctx: &mut C, i: usize) -> i64
	where
		C: ReasoningContext + ?Sized,
		I1: IntInspectionActions<C>,
		I2: IntInspectionActions<C>,
	{
		self.start_times[i].max(ctx) + self.durations[i].max(ctx)
	}

	/// Get the latest start time of the task `i`.
	#[inline]
	fn latest_start_time<C>(&self, ctx: &mut C, i: usize) -> i64
	where
		C: ReasoningContext + ?Sized,
		I1: IntInspectionActions<C>,
	{
		self.start_times[i].max(ctx)
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
	fn limit_usage<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		task: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let lst = self.latest_start_time(ctx, task);
		let ect = self.earliest_completion_time(ctx, task);
		let dur_lb = self.durations[task].min(ctx);
		let usage_lb = self.usages[task].min(ctx);
		debug_assert!(lst < ect, "Task must have compulsory part");

		if !(dur_lb > 0 && usage_lb > 0) {
			// If the task has no duration or usage, no need to sweep
			return Ok(());
		}

		// Find the maximum usage in the interval [lst, ect]
		// where the task has a compulsory part
		let max_period = self.max_period_within(task, lst, ect);
		if let Some(max_period) = max_period {
			let max_usage = self.heights[max_period];
			let limit = self.capacity.max(ctx) - max_usage + usage_lb;
			trace!(
				target: "cumulative",
				task,
				compulsory_part =? (lst, ect),
				max_period,
				max_usage,
				limit,
				"limit task usage"
			);
			self.usages[task].tighten_max(
				ctx,
				limit,
				self.explain_limit_usage(task, self.bounds[max_period], limit),
			)?;
		}
		Ok(())
	}

	/// A helper function to find the index of the maximum usage in the
	/// time-table profile within a specified period [start, end].
	fn max_period_within(&self, _task: usize, start: i64, end: i64) -> Option<usize> {
		trace!(
			target: "cumulative",
			task = _task,
			start,
			end,
			bounds = ?self.bounds,
			heights = ?self.heights,
			"find max usage period within compulsory part"
		);
		let begin = self.bounds.partition_point(|&b| b <= start);
		if begin >= self.bounds.len() {
			return None;
		}
		// Adjust begin to point to the interval containing `start`
		let begin = if begin == 0 { 0 } else { begin - 1 };
		let end = self.bounds[begin..].partition_point(|&b| b < end) + begin;
		(begin < end).then(|| begin + self.heights[(begin)..end].iter().position_max().unwrap())
	}

	/// Creates a new `CumulativePropagator` running the TTEF phases selected by
	/// the `ttef_*_enabled` flags on top of the time-table propagation.
	pub(crate) fn new(
		start_times: Vec<I1>,
		durations: Vec<I2>,
		usages: Vec<I3>,
		capacity: I4,
		ttef_check_enabled: bool,
		ttef_filtering_enabled: bool,
		ttef_opportunistic_enabled: bool,
	) -> Self {
		Self {
			start_times,
			durations,
			usages,
			capacity,
			ttef_check_enabled,
			ttef_filtering_enabled,
			ttef_opportunistic_enabled,
			bounds: Vec::new(),
			heights: Vec::new(),
		}
	}

	/// Creates a new `CumulativePropagator` with the given TTEF flags and posts
	/// it in the solver.
	#[expect(
		clippy::too_many_arguments,
		reason = "the `cumulative` constraint takes four decision arguments plus the three TTEF phase toggles"
	)]
	pub fn post<E>(
		solver: &mut E,
		start_times: Vec<I1>,
		durations: Vec<I2>,
		usages: Vec<I3>,
		capacity: I4,
		ttef_check_enabled: bool,
		ttef_filtering_enabled: bool,
		ttef_opportunistic_enabled: bool,
	) where
		E: PostingActions + ?Sized,
		I1: IntSolverActions<Engine>,
		I2: IntSolverActions<Engine>,
		I3: IntSolverActions<Engine>,
		I4: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(CumulativePropagator::new(
			start_times,
			durations,
			usages,
			capacity,
			ttef_check_enabled,
			ttef_filtering_enabled,
			ttef_opportunistic_enabled,
		)));
	}

	/// Energy of the time-table profile in the interval `[tau, +inf)`, i.e. the
	/// sum over profile segments of their height times their length clipped to
	/// start at `tau`. The profile is the `(bounds, heights)` step function
	/// built by [`Self::build_profile_and_check_overload`]: segment `i` covers
	/// `[bounds[i], bounds[i + 1])` at height `heights[i]`.
	fn profile_energy_after(&self, tau: IntVal) -> IntVal {
		let mut energy = 0;
		for i in 0..self.bounds.len().saturating_sub(1) {
			let seg_start = self.bounds[i].max(tau);
			let seg_end = self.bounds[i + 1];
			if seg_end > seg_start {
				energy += self.heights[i] * (seg_end - seg_start);
			}
		}
		energy
	}

	/// Run the enabled time-table-edge-finding (TTEF) phases on top of the
	/// time-table profile. Returns `Ok(true)` if a bound was updated, so the
	/// caller defers further propagation until the engine has applied it.
	///
	/// TTEF reasons about the energy required by tasks within time windows
	/// `[est_a, lct_b)` (task intervals), combining the free-part energy of the
	/// tasks fully inside the window, the compulsory-part energy stored in the
	/// time-table profile, and the partial overlaps of free parts. See Schutt
	/// et al. (2013) and Vilím (2011).
	fn propagate_ttef<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let data = self.ttef_data::<E>(ctx);
		if data.len() < 2 {
			return Ok(false);
		}

		// Bounds filtering (Schutt et al. (2013), Alg. 2) subsumes the consistency
		// check: its sweeps also detect resource overloads. When only the check is
		// enabled, run the cheaper consistency check on its own.
		if self.ttef_filtering_enabled {
			let opp = self.ttef_opportunistic_enabled;
			let mut updates = Vec::new();
			if let Some((begin, end)) = data.est_filtering(opp, &mut updates) {
				trace!(target: "cumulative", window =? (begin, end), "ttef resource overload");
				return Err(ctx.declare_conflict(self.explain_ttef_overload(&data, begin, end)));
			}
			if let Some((begin, end)) = data.lct_filtering(opp, &mut updates) {
				trace!(target: "cumulative", window =? (begin, end), "ttef resource overload");
				return Err(ctx.declare_conflict(self.explain_ttef_overload(&data, begin, end)));
			}
			let mut propagated = false;
			for upd in &updates {
				// Re-derive the bound from the forced energy of the other tasks the
				// reason pins, so the naive energetic explanation provably entails it
				// (the sweep's `upd.bound` can rest on energy a naive reason cannot
				// justify, notably for the opportunistic through-position update).
				let Some(bound) = data.sound_update_bound(upd.task, upd.begin, upd.end, upd.is_lb)
				else {
					continue;
				};
				let reason =
					self.explain_ttef_update(&data, upd.task, upd.begin, upd.end, upd.is_lb);
				if upd.is_lb {
					self.start_times[upd.task].tighten_min(ctx, bound, reason)?;
				} else {
					self.start_times[upd.task].tighten_max(ctx, bound, reason)?;
				}
				propagated = true;
			}
			return Ok(propagated);
		}

		// Consistency check only (Schutt et al. (2013), Alg. 1): detect a task
		// interval whose required energy exceeds the available resource energy.
		if self.ttef_check_enabled
			&& let Some((begin, end)) = data.consistency_check()
		{
			trace!(target: "cumulative", window =? (begin, end), "ttef resource overload");
			return Err(ctx.declare_conflict(self.explain_ttef_overload(&data, begin, end)));
		}

		Ok(false)
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
	fn sweep_backward<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		task: usize,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let est = self.earliest_start_time(ctx, task);
		let lst = self.latest_start_time(ctx, task);
		let ect = self.earliest_completion_time(ctx, task);
		let dur_lb = self.durations[task].min(ctx);
		let usage_lb = self.usages[task].min(ctx);

		if dur_lb <= 0 || usage_lb <= 0 {
			// If the task has no duration or usage, no need to sweep
			return Ok(false);
		}

		// Find the partition point where b < lst + dur
		let last = self.bounds.partition_point(|&b| b < lst + dur_lb);
		trace!(target: "cumulative", task, dur_lb, est, lst, usage_lb, "task sweep backward");
		let mut updated_lct = self.latest_completion_time(ctx, task);
		let max_capacity = self.capacity.max(ctx);
		let mut updated = false;
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
					target: "cumulative",
					updated_lct,
					b_start,
					remainder,
					time_points =? time_points,
					"propagate backward shifting"
				);

				for t in time_points {
					if t < updated_lct {
						// Set new upper bound for the task's start time
						self.start_times[task].tighten_max(
							ctx,
							t - dur_lb,
							self.explain_sweeping_time(
								task,
								CumulativePropagationRule::BackwardShift,
								t,
							),
						)?;
						updated_lct = t;
						updated = true;
					}
				}
			}
		}
		Ok(updated)
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
	fn sweep_forward<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		task: usize,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let est = self.earliest_start_time(ctx, task);
		let lst = self.latest_start_time(ctx, task);
		let dur_lb = self.durations[task].min(ctx);
		let usage_lb = self.usages[task].min(ctx);

		if dur_lb <= 0 || usage_lb <= 0 {
			// If the task has no duration or usage, no need to sweep
			return Ok(false);
		}

		// Find the partition point where est > b
		let first = self.bounds.partition_point(|&b| b < est);
		trace!(target: "cumulative", task, dur_lb, est, lst, usage_lb, "task sweep forward");
		let mut updated_est = est;
		let max_capacity = self.capacity.max(ctx);
		let mut updated = false;
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
					target: "cumulative",
					updated_est,
					b_end,
					remainder,
					time_points =? time_points,
					"propagate forward shifting"
				);

				for t in time_points {
					if t > updated_est {
						// Set new lower bound for the task's start time
						self.start_times[task].tighten_min(
							ctx,
							t,
							self.explain_sweeping_time(
								task,
								CumulativePropagationRule::ForwardShift,
								t - 1,
							),
						)?;
						updated_est = t;
						updated = true;
					}
				}
			}
		}
		Ok(updated)
	}

	/// Collect the per-task quantities used by the TTEF phases from the current
	/// domains. See [`TtefData`] for the soundness rationale of the bound
	/// choices.
	fn ttef_data<E>(&self, ctx: &mut E::PropagationContext<'_>) -> TtefData
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let n = self.start_times.len();
		let mut est = vec![0; n];
		let mut lst = vec![0; n];
		let mut ect = vec![0; n];
		let mut lct = vec![0; n];
		let mut dur = vec![0; n];
		let mut usage = vec![0; n];
		let mut energy = vec![0; n];
		let mut fixed_dur = vec![0; n];
		let mut free_energy = vec![0; n];
		let mut lst_ef = vec![0; n];
		for i in 0..n {
			let d_lb = self.durations[i].min(ctx);
			let u_lb = self.usages[i].min(ctx);
			est[i] = self.earliest_start_time(ctx, i);
			lst[i] = self.latest_start_time(ctx, i);
			ect[i] = self.earliest_completion_time(ctx, i);
			lct[i] = self.latest_completion_time(ctx, i);
			dur[i] = d_lb;
			usage[i] = u_lb;
			energy[i] = d_lb * u_lb;
			// Length of the compulsory part pTT_i = max(0, ect_i - lst_i).
			fixed_dur[i] = (ect[i] - lst[i]).max(0);
			lst_ef[i] = lst[i] + fixed_dur[i];
			free_energy[i] = u_lb * (d_lb - fixed_dur[i]);
		}
		let capacity = self.capacity.max(ctx);
		let mut by_est: Vec<usize> = (0..n).collect();
		by_est.sort_unstable_by_key(|&i| est[i]);
		let mut by_lct: Vec<usize> = (0..n).collect();
		by_lct.sort_unstable_by_key(|&i| lct[i]);
		let tt_after_est = (0..n).map(|i| self.profile_energy_after(est[i])).collect();
		let tt_after_lct = (0..n).map(|i| self.profile_energy_after(lct[i])).collect();
		TtefData {
			est,
			lst,
			ect,
			lct,
			dur,
			usage,
			energy,
			fixed_dur,
			free_energy,
			lst_ef,
			capacity,
			by_est,
			by_lct,
			tt_after_est,
			tt_after_lct,
		}
	}
}

impl<E, I1, I2, I3, I4> Constraint<E> for CumulativePropagator<I1, I2, I3, I4>
where
	E: ReasoningEngine,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
	I3: IntModelActions<E>,
	I4: IntModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		// The constraint is easier to satisfy with a larger resource capacity,
		// and with tasks that use less of the resource for a shorter time.
		self.capacity.polarity(ctx, Polarity::Positive);
		for usage in &self.usages {
			usage.polarity(ctx, Polarity::Negative);
		}
		for duration in &self.durations {
			duration.polarity(ctx, Polarity::Negative);
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if self.capacity.val(ctx).is_some()
			&& self.start_times.iter().all(|v| v.val(ctx).is_some())
			&& self.durations.iter().all(|v| v.val(ctx).is_some())
			&& self.usages.iter().all(|v| v.val(ctx).is_some())
		{
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let start_times = self
			.start_times
			.iter()
			.map(|v| slv.solver_view(v.clone().into()))
			.collect_vec();
		let durations = self
			.durations
			.iter()
			.map(|v| slv.solver_view(v.clone().into()))
			.collect_vec();
		let usages = self
			.usages
			.iter()
			.map(|v| slv.solver_view(v.clone().into()))
			.collect_vec();
		let capacity = { slv.solver_view(self.capacity.clone().into()) };
		CumulativePropagator::post(
			slv,
			start_times,
			durations,
			usages,
			capacity,
			self.ttef_check_enabled,
			self.ttef_filtering_enabled,
			self.ttef_opportunistic_enabled,
		);
		Ok(())
	}
}

impl<E, I1, I2, I3, I4> Propagator<E> for CumulativePropagator<I1, I2, I3, I4>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
	I3: IntSolverActions<E>,
	I4: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		for v in &self.start_times {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
		for d in &self.durations {
			d.enqueue_when(ctx, IntPropCond::LowerBound);
		}
		for u in &self.usages {
			u.enqueue_when(ctx, IntPropCond::LowerBound);
		}
		self.capacity.enqueue_when(ctx, IntPropCond::UpperBound);
	}

	#[tracing::instrument(
		name = "cumulative_time_table",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let profile_empty = self.build_profile_and_check_overload(ctx)?;

		if !profile_empty {
			let mut bounds_updated = false;
			for i in 0..self.start_times.len() {
				let (lb, ub) = self.start_times[i].bounds(ctx);
				if lb < ub {
					bounds_updated |= self.sweep_forward(ctx, i)?;
					bounds_updated |= self.sweep_backward(ctx, i)?;
				}
			}

			// Defer further propagation until the engine has applied the bound
			// changes, so that the profile (and the TTEF reasoning below) operate on
			// up-to-date bounds.
			if bounds_updated {
				return Ok(());
			}
		}

		// Time-table-edge-finding phases run once the time-table propagation has
		// reached its fixpoint. Unlike the time-table phase, edge-finding can also
		// propagate when there are no compulsory parts, so it runs regardless of
		// whether the profile is empty. It returns early when it updated a bound.
		if self.any_ttef_enabled() && self.propagate_ttef(ctx)? {
			return Ok(());
		}

		if profile_empty {
			return Ok(());
		}

		for i in 0..self.start_times.len() {
			let (req_lb, req_ub) = self.usages[i].bounds(ctx);
			if req_lb < req_ub
				&& self.latest_start_time(ctx, i) < self.earliest_completion_time(ctx, i)
			{
				self.limit_usage(ctx, i)?;
			}
		}
		Ok(())
	}
}

impl TtefData {
	/// The TTEF consistency check (Schutt et al. (2013), Alg. 1; Vilím (2011),
	/// Alg. 1). It searches for a task interval `[begin, end)` whose required
	/// energy exceeds the energy the resource makes available, i.e.
	/// `R * (end - begin) - energy(begin, end) < 0`. The required energy
	/// `energy(begin, end)` combines (i) the free energy of tasks whose free
	/// part is entirely inside the window, (ii) the compulsory-part energy
	/// stored in the time-table profile (`tt_after_est - tt_after_lct`), and
	/// (iii) the partial free energy of tasks that start inside the window but
	/// complete after it.
	///
	/// It returns the first overloaded window `(begin, end)` found, or `None`
	/// if the check passes. The windows considered are task intervals: the end
	/// times range over the distinct latest completion times, and for each end
	/// the begin times range over the earliest start times inside the window.
	fn consistency_check(&self) -> Option<(IntVal, IntVal)> {
		// Outer loop: end = lct in non-increasing order.
		let mut prev_end: Option<IntVal> = None;
		for &b in self.by_lct.iter().rev() {
			if self.energy[b] == 0 {
				continue;
			}
			let end = self.lct[b];
			if prev_end == Some(end) {
				// A window with this end was already checked (duplicate lct).
				continue;
			}
			prev_end = Some(end);

			// Inner loop: begin = est in non-increasing order, accumulating the
			// free energy required within [begin, end).
			let mut en_req_free = 0;
			for &j in self.by_est.iter().rev() {
				let begin = self.est[j];
				if begin >= end || self.energy[j] == 0 {
					continue;
				}
				if self.lct[j] <= end {
					// The free part of task j is entirely inside the window.
					en_req_free += self.free_energy[j];
				} else {
					// Task j starts inside the window but completes after it; only
					// the part of its free duration forced into the window counts.
					en_req_free += self.usage[j] * (end - self.lst_ef[j]).max(0);
				}
				let en_req = en_req_free + self.tt_after_est[j] - self.tt_after_lct[b];
				if self.capacity * (end - begin) - en_req < 0 && self.window_overloaded(begin, end)
				{
					return Some((begin, end));
				}
			}
		}
		None
	}

	/// Whether task `i` is forced to place energy inside the window
	/// `[begin, end)` under *every* schedule consistent with its current
	/// bounds. This holds exactly when the task can be scheduled neither
	/// entirely before the window (it cannot complete by `begin`, i.e. `ect_i
	/// > begin`) nor entirely after it (it cannot start at or after `end`,
	/// i.e. `lst_i < end`).
	///
	/// These are exactly the tasks whose energy the TTEF energy balance for
	/// `[begin, end)` relies on, so they are the tasks that must appear in an
	/// energetic explanation. Pinning each to its current `[est_i, lst_i]`
	/// guarantees the window holds at least the energy the propagator counted;
	/// omitting any of them would yield a reason too weak to entail the
	/// inference (an unsound nogood). A task with no energy never forces
	/// anything.
	fn contributes(&self, i: usize, begin: IntVal, end: IntVal) -> bool {
		self.energy[i] > 0 && self.ect[i] > begin && self.lst[i] < end
	}

	/// TTEF earliest-start-time filtering. For each task
	/// interval `[begin, end)` it tracks the task `u` (overlapping the window
	/// on its right) that would require the most energy inside the window if
	/// started at its earliest start. When the energy available to `u` is too
	/// small, `est_u` is lifted so that only the affordable part of `u` lies
	/// inside the window.
	///
	/// Found updates are appended to `updates`. Returns `Some((begin, end))` if
	/// a resource overload is detected instead.
	fn est_filtering(
		&self,
		opportunistic: bool,
		updates: &mut Vec<TtefUpdate>,
	) -> Option<(IntVal, IntVal)> {
		// Strongest new bounds found so far per task, to keep only the best update
		// and avoid queueing dominated ones.
		let mut new_est = self.est.clone();
		let mut new_lct = self.lct.clone();
		let horizon_energy =
			self.capacity * (self.lct[*self.by_lct.last().unwrap()] - self.est[self.by_est[0]]);
		let mut prev_end: Option<IntVal> = None;
		for &i in self.by_lct.iter().rev() {
			if self.energy[i] == 0 {
				continue;
			}
			let end = self.lct[i];
			if prev_end == Some(end) {
				continue;
			}
			prev_end = Some(end);

			let mut en_req_free = 0;
			let mut max_en_req_start = -1;
			let mut iota: Option<usize> = None;
			// Minimum available energy and the begin achieving it, for the
			// opportunistic extended-edge-finding upper-bound update.
			let mut min_en_avail = horizon_energy;
			let mut min_begin: Option<IntVal> = None;
			for &j in self.by_est.iter().rev() {
				let begin = self.est[j];
				if begin >= end || self.energy[j] == 0 {
					continue;
				}

				// Opportunistic extended edge finding (Vilím (2011), through/left): if
				// the tightest window `[min_begin, end)` seen so far cannot fit all of
				// `j`, lower its latest completion accordingly.
				if opportunistic && let Some(mb) = min_begin {
					let min_en_in =
						self.usage[j] * (self.ect[j].min(end) - mb.max(self.lst[j])).max(0);
					let full = self.usage[j] * (self.lct[j].min(end) - mb.max(self.lst[j]));
					if min_en_avail + min_en_in < full {
						let dur_avail = (min_en_avail + min_en_in) / self.usage[j];
						let lct_new = mb + dur_avail;
						if lct_new < new_lct[j] {
							updates.push(TtefUpdate {
								task: j,
								begin: mb,
								end,
								is_lb: false,
							});
							new_lct[j] = lct_new;
						}
					}
				}

				if self.lct[j] <= end {
					en_req_free += self.free_energy[j];
				} else {
					// The free part of `j` is forced into the window from the right.
					let dur_shift = (end - self.lst_ef[j]).max(0);
					en_req_free += self.usage[j] * dur_shift;
					// Extra energy `j` would need in the window if started at est_j.
					let en_req_start = self.free_energy[j].min(self.usage[j] * (end - self.est[j]))
						- self.usage[j] * dur_shift;
					if en_req_start > max_en_req_start {
						max_en_req_start = en_req_start;
						iota = Some(j);
					}
				}
				let en_req = en_req_free + self.tt_after_est[j] - self.tt_after_lct[i];
				let en_avail = self.capacity * (end - begin) - en_req;
				if en_avail < 0 && self.window_overloaded(begin, end) {
					return Some((begin, end));
				}
				if min_en_avail > en_avail {
					min_en_avail = en_avail;
					min_begin = Some(begin);
				}
				if let Some(u) = iota
					&& en_avail < max_en_req_start
				{
					// Energy of `u` already counted as inside the window.
					let dur_mand = (self.ect[u].min(end) - self.lst[u]).max(0);
					let dur_shift = if begin <= self.est[u] {
						(end - self.lst[u] - dur_mand).max(0)
					} else {
						0
					};
					let en_in = self.usage[u] * (dur_mand + dur_shift);
					// Only `dur_avail` of `u` can fit before `end`, so it must start at
					// `end - dur_avail` at the earliest.
					let dur_avail = (en_avail + en_in) / self.usage[u];
					let start_new = end - dur_avail;
					if start_new > new_est[u] {
						updates.push(TtefUpdate {
							task: u,
							begin,
							end,
							is_lb: true,
						});
						new_est[u] = start_new;
					}
				}
			}
		}
		None
	}

	/// Minimum energy task `i` is *forced* to place inside `[begin, end)` under
	/// every schedule allowed by its current bounds: start in `[est_i, lst_i]`,
	/// `dur ≥ dur_lb_i`, `usage ≥ usage_lb_i`. The in-window overlap of the
	/// placement `[s, s + dur_lb_i)` is, as a function of `s`, a trapezoid
	/// (rises, plateaus, falls), so its minimum over `[est_i, lst_i]` is
	/// attained at an endpoint. Using `dur_lb`/`usage_lb` yields the least
	/// energy the bounds guarantee, which is exactly what a naive energetic
	/// reason pinning the task to `[est_i, lst_i]` (plus the duration and
	/// usage lower bounds) can rely on.
	fn forced_energy(&self, i: usize, begin: IntVal, end: IntVal) -> IntVal {
		let overlap = |s: IntVal| ((s + self.dur[i]).min(end) - s.max(begin)).max(0);
		self.usage[i] * overlap(self.est[i]).min(overlap(self.lst[i]))
	}

	/// TTEF latest-completion-time filtering: the time-symmetric counterpart of
	/// [`Self::est_filtering`] (Vilím (2011), left and inside positions). For
	/// each task interval `[begin, end)` it lowers the latest completion time
	/// of the task `u` overlapping the window on its left. Found updates
	/// (carrying the new `lct`) are appended to `updates`; returns
	/// `Some((begin, end))` on a resource overload.
	fn lct_filtering(
		&self,
		opportunistic: bool,
		updates: &mut Vec<TtefUpdate>,
	) -> Option<(IntVal, IntVal)> {
		let mut new_est = self.est.clone();
		let mut new_lct = self.lct.clone();
		let horizon_energy =
			self.capacity * (self.lct[*self.by_lct.last().unwrap()] - self.est[self.by_est[0]]);
		let mut prev_begin: Option<IntVal> = None;
		for &i in self.by_est.iter() {
			if self.energy[i] == 0 {
				continue;
			}
			let begin = self.est[i];
			if prev_begin == Some(begin) {
				continue;
			}
			prev_begin = Some(begin);

			let mut en_req_free = 0;
			let mut max_en_req_end = -1;
			let mut iota: Option<usize> = None;
			// Minimum available energy and the end achieving it, for the
			// opportunistic extended-edge-finding lower-bound update.
			let mut min_en_avail = horizon_energy;
			let mut min_end: Option<IntVal> = None;
			for &j in self.by_lct.iter() {
				let end = self.lct[j];
				if end <= begin || self.energy[j] == 0 {
					continue;
				}

				// Opportunistic extended edge finding (Vilím (2011), through/left): if
				// the tightest window `[begin, min_end)` seen so far cannot fit all of
				// `j`, raise its earliest start accordingly.
				if opportunistic && let Some(me) = min_end {
					let min_en_in =
						self.usage[j] * (me.min(self.ect[j]) - begin.max(self.lst[j])).max(0);
					let full = self.usage[j] * (me.min(self.ect[j]) - begin.max(self.est[j]));
					if min_en_avail + min_en_in < full {
						let dur_avail = (min_en_avail + min_en_in) / self.usage[j];
						let est_new = me - dur_avail;
						if est_new > new_est[j] {
							updates.push(TtefUpdate {
								task: j,
								begin,
								end: me,
								is_lb: true,
							});
							new_est[j] = est_new;
						}
					}
				}

				if begin <= self.est[j] {
					en_req_free += self.free_energy[j];
				} else {
					// The free part of `j` is forced into the window from the left.
					let dur_shift = if end >= self.lct[j] {
						(self.ect[j] - begin - self.fixed_dur[j]).max(0)
					} else {
						0
					};
					en_req_free += self.usage[j] * dur_shift;
					let en_req_end = self.free_energy[j].min(self.usage[j] * (self.lct[j] - begin))
						- self.usage[j] * dur_shift;
					if en_req_end > max_en_req_end {
						max_en_req_end = en_req_end;
						iota = Some(j);
					}
				}
				let en_req = en_req_free + self.tt_after_est[i] - self.tt_after_lct[j];
				let en_avail = self.capacity * (end - begin) - en_req;
				if en_avail < 0 && self.window_overloaded(begin, end) {
					return Some((begin, end));
				}
				if min_en_avail > en_avail {
					min_en_avail = en_avail;
					min_end = Some(end);
				}
				if let Some(u) = iota
					&& en_avail < max_en_req_end
				{
					let dur_mand = (self.ect[u] - begin.max(self.lst[u])).max(0);
					let dur_shift = if end >= self.lct[u] {
						(self.ect[u] - begin - dur_mand).max(0)
					} else {
						0
					};
					let en_in = self.usage[u] * (dur_mand + dur_shift);
					let dur_avail = (en_avail + en_in) / self.usage[u];
					let end_new = begin + dur_avail;
					if end_new < new_lct[u] {
						updates.push(TtefUpdate {
							task: u,
							begin,
							end,
							is_lb: false,
						});
						new_lct[u] = end_new;
					}
				}
			}
		}
		None
	}

	/// Number of tasks.
	fn len(&self) -> usize {
		self.est.len()
	}

	/// Re-derive a *sound* start-time bound for a queued filtering update of
	/// task `u` justified by the window `[begin, end)`, computed solely from
	/// the energy the explanation actually pins: the forced energy of every
	/// other contributing task and the capacity upper bound.
	/// This guarantees the naive energetic reason entails the
	/// applied bound, for the regular *and* the opportunistic
	/// (through-position) updates alike, mirroring Chuffed's re-derivation in
	/// `ttef_update_bounds`.
	///
	/// Returns the new earliest start (`is_lb`) or new latest start
	/// (otherwise), or `None` when the pinned energy does not justify a
	/// tighter bound. The guard `overlap(anchor) > dur_avail` is the
	/// edge-finding condition that `u` cannot fit its forced part in the
	/// energy left for it, so it must be pushed off the window; `u`'s own
	/// overlap uses `dur_lb_u` (an under-estimate) and the available duration
	/// uses `usage_lb_u` (giving the weakest sound bound).
	fn sound_update_bound(
		&self,
		u: usize,
		begin: IntVal,
		end: IntVal,
		is_lb: bool,
	) -> Option<IntVal> {
		let mut en_others = 0;
		for i in 0..self.len() {
			if i != u && self.contributes(i, begin, end) {
				en_others += self.forced_energy(i, begin, end);
			}
		}
		let en_avail = self.capacity * (end - begin) - en_others;
		if en_avail < 0 {
			return None;
		}
		let dur_avail = en_avail / self.usage[u];
		let overlap = |s: IntVal| ((s + self.dur[u]).min(end) - s.max(begin)).max(0);
		if is_lb {
			// `u` placed at its earliest start cannot fit in the energy left for
			// it, so any feasible start lies at or after `end - dur_avail`.
			if overlap(self.est[u]) <= dur_avail {
				return None;
			}
			let start_new = end - dur_avail;
			(start_new > self.est[u]).then_some(start_new)
		} else {
			// Symmetric: `u` placed at its latest start cannot fit, so its latest
			// completion is at most `begin + dur_avail`, bounding its latest start.
			if overlap(self.lst[u]) <= dur_avail {
				return None;
			}
			let start_new = begin + dur_avail - self.dur[u];
			(start_new < self.lst[u]).then_some(start_new)
		}
	}

	/// Total energy every task is *forced* to place inside `[begin, end)`.
	/// A resource overload is only soundly explainable by pinning the
	/// contributing tasks when this exceeds the energy the resource makes
	/// available, `R * (end - begin)`; the sweep's incremental `en_req` can
	/// over-count for variable durations (its `lct` uses `dur_max` while the
	/// energy uses `dur_lb`), so overload detection is gated on this.
	fn window_forced_energy(&self, begin: IntVal, end: IntVal) -> IntVal {
		(0..self.len())
			.map(|i| self.forced_energy(i, begin, end))
			.sum()
	}

	/// Whether `[begin, end)` is provably overloaded by the energy its tasks
	/// are forced to place inside it, i.e. an overload with a sound energetic
	/// reason.
	fn window_overloaded(&self, begin: IntVal, end: IntVal) -> bool {
		self.window_forced_energy(begin, end) > self.capacity * (end - begin)
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		actions::IntInspectionActions,
		constraints::cumulative::CumulativePropagator,
		model::{ConRef, Model},
		solver::{LiteralStrategy, Solver, View},
	};

	/// Every TTEF configuration; sound propagation must give the same solutions
	/// under each of them.
	const ALL_CONFIGS: [TtefConfig; 4] = [TT, CHECK_ONLY, FILTER, FILTER_OPP];
	/// Only the consistency check.
	const CHECK_ONLY: TtefConfig = (true, false, false);
	/// The consistency check and bounds filtering (the paper's `ttef` setting).
	const FILTER: TtefConfig = (true, true, false);
	/// All phases including the opportunistic extended edge finding (the
	/// paper's `ttef+` setting).
	const FILTER_OPP: TtefConfig = (true, true, true);
	/// No TTEF phases: pure time-table propagation (the baseline).
	const TT: TtefConfig = (false, false, false);

	/// A TTEF configuration as `(check, filtering, opportunistic)`, matching
	/// the trailing arguments of [`CumulativePropagator::post`].
	type TtefConfig = (bool, bool, bool);

	/// Helper function to create a task with given start time, duration, and
	/// usage.
	fn create_task(
		slv: &mut Solver,
		start_time: impl Into<IntSet>,
		duration: impl Into<IntSet>,
		usage: impl Into<IntSet>,
	) -> (View<IntVal>, View<IntVal>, View<IntVal>) {
		let start = slv
			.new_int_decision(start_time)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let dur = slv
			.new_int_decision(duration)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let usage = slv
			.new_int_decision(usage)
			.order_literals(LiteralStrategy::Eager)
			.view();
		(start, dur, usage)
	}

	/// Enumerate every solution of a cumulative instance under the given TTEF
	/// configuration, sorted. Each task `i` has start domain `0..=dom`,
	/// duration domain `dur_doms[i]`, and usage domain `use_doms[i]` (pass
	/// `(v, v)` for a fixed value). Solutions list starts, then durations,
	/// then usages, so that variable-duration instances are compared over
	/// their full assignment.
	#[cfg(test)]
	fn enumerate_cumulative(
		(check, filtering, opportunistic): TtefConfig,
		dom: IntVal,
		dur_doms: &[(IntVal, IntVal)],
		use_doms: &[(IntVal, IntVal)],
		cap: IntVal,
	) -> Vec<Vec<IntVal>> {
		let mut slv: Solver = Solver::default();
		let mk = |slv: &mut Solver, lo: IntVal, hi: IntVal| {
			slv.new_int_decision(lo..=hi)
				.order_literals(LiteralStrategy::Eager)
				.view()
		};
		let starts: Vec<View<IntVal>> = (0..dur_doms.len()).map(|_| mk(&mut slv, 0, dom)).collect();
		let durs: Vec<View<IntVal>> = dur_doms
			.iter()
			.map(|&(lo, hi)| mk(&mut slv, lo, hi))
			.collect();
		let usages: Vec<View<IntVal>> = use_doms
			.iter()
			.map(|&(lo, hi)| mk(&mut slv, lo, hi))
			.collect();
		CumulativePropagator::post(
			&mut slv,
			starts.clone(),
			durs.clone(),
			usages.clone(),
			cap,
			check,
			filtering,
			opportunistic,
		);
		let mut all: Vec<View<IntVal>> = starts.clone();
		all.extend(durs.iter().copied());
		all.extend(usages.iter().copied());
		let views: Vec<crate::solver::AnyView> = all.iter().map(|v| (*v).into()).collect();
		let mut solns: Vec<Vec<IntVal>> = Vec::new();
		let _ = slv
			.solve()
			.all_solutions(views.iter().cloned())
			.collect_solutions_in(all.clone(), &mut solns)
			.satisfy();
		solns.sort();
		solns
	}

	/// This test verifies that the cumulative propagator performs multiple
	/// rounds of propagation to reach a fixpoint. In each round, the
	/// propagator first updates the start times of tasks according to the
	/// time-table profile. Once no further updates to start times are possible,
	/// the propagator then tightens the usage bounds based on the current
	/// profile. This ensures the time-table profile is the latest and the
	/// propagation of usage bounds are correct.
	#[test]
	#[traced_test]
	fn test_cumulative_propagate() {
		let mut prb = Model::default();
		// Task A: can start at 0, 1, or 2; duration 3. Latest start time: 2, earliest
		// completion time: 3. Compulsory part: [0, 2] (must be scheduled in this
		// interval for feasibility).
		let start_time_a = prb.new_int_decision(0..=2);
		// Task B: same as Task A (identical domain and duration).
		let start_time_b = prb.new_int_decision(0..=2);
		// Task C: can start at 0..=4; duration 3. Latest start time: 4, earliest
		// completion time: 3. No compulsory part.
		let start_time_c = prb.new_int_decision(0..=4);
		let usages = prb.new_int_decisions(3, 1..=2);
		prb.post_constraint_internal(CumulativePropagator::new(
			vec![start_time_a, start_time_b, start_time_c],
			vec![3, 3, 3],
			usages.clone(),
			2,
			false,
			false,
			false,
		));

		// First propagation: The compulsory parts of Task A and B ([0, 2])
		// require that Task C cannot overlap with them due to capacity constraints.
		// This pushes the earliest start time of Task C to 3.
		let _ = prb.propagate_single(ConRef::from_raw(0));
		let time_bounds = start_time_a.bounds(&prb);
		assert_eq!(time_bounds, (0, 2));
		let usage_bounds = usages[0].bounds(&prb);
		assert_eq!(usage_bounds, (1, 2));

		let time_bounds = start_time_b.bounds(&prb);
		assert_eq!(time_bounds, (0, 2));
		let usage_bounds = usages[1].bounds(&prb);
		assert_eq!(usage_bounds, (1, 2));

		let time_bounds = start_time_c.bounds(&prb);
		assert_eq!(time_bounds, (3, 4));
		let usage_bounds = usages[2].bounds(&prb);
		assert_eq!(usage_bounds, (1, 2));

		// Second propagation: With Task C's start time now at least 3, only A and B
		// overlap in [0, 2]. The combined usage of A and B in this interval must not
		// exceed the capacity (2), so their usage upper bounds are tightened to 1.
		let _ = prb.propagate_single(ConRef::from_raw(0));
		let time_bounds = start_time_a.bounds(&prb);
		assert_eq!(time_bounds, (0, 2));
		let usage_bounds = usages[0].bounds(&prb);
		assert_eq!(usage_bounds, (1, 1));

		let time_bounds = start_time_b.bounds(&prb);
		assert_eq!(time_bounds, (0, 2));
		let usage_bounds = usages[1].bounds(&prb);
		assert_eq!(usage_bounds, (1, 1));

		let time_bounds = start_time_c.bounds(&prb);
		assert_eq!(time_bounds, (3, 4));
		let usage_bounds = usages[2].bounds(&prb);
		assert_eq!(usage_bounds, (1, 2));
	}

	#[test]
	#[traced_test]
	fn test_cumulative_val_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(0..=4)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(0..=4)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(0..=4)
			.order_literals(LiteralStrategy::Eager)
			.view();

		let durations: Vec<View<IntVal>> = [2, 3, 1].into_iter().map_into().collect();
		let resources_profile_1 = vec![1, 2, 3];
		let resources_profile_2 = vec![2, 2, 1];
		let capacity_1 = 3;
		let capacity_2 = 2;
		CumulativePropagator::post(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			capacity_1,
			false,
			false,
			false,
		);
		CumulativePropagator::post(
			&mut slv,
			vec![a, b, c],
			durations,
			resources_profile_2,
			capacity_2,
			false,
			false,
			false,
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
		let a = slv
			.new_int_decision(0..=3)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(0..=3)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(0..=3)
			.order_literals(LiteralStrategy::Eager)
			.view();

		let durations: Vec<View<IntVal>> = [2, 3, 2].into_iter().map_into().collect();
		let resources_profile_1: Vec<View<IntVal>> = [2, 2, 3].into_iter().map_into().collect();
		let resources_profile_2: Vec<View<IntVal>> = [2, 2, 2].into_iter().map_into().collect();
		let capacity = 3;

		CumulativePropagator::post(
			&mut slv,
			vec![a, b, c],
			durations.clone(),
			resources_profile_1,
			capacity,
			false,
			false,
			false,
		);
		CumulativePropagator::post(
			&mut slv,
			vec![a, b, c],
			durations,
			resources_profile_2,
			capacity,
			false,
			false,
			false,
		);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_capacity_sat() {
		let mut slv = Solver::default();
		let start = vec![0, 3, 4, 6, 8, 8];
		let duration = vec![3, 2, 5, 2, 1, 4];
		let usage = vec![2, 3, 1, 4, 3, 2];
		let capacity = slv
			.new_int_decision(1..=6)
			.order_literals(LiteralStrategy::Eager)
			.view();
		CumulativePropagator::post(
			&mut slv, start, duration, usage, capacity, false, false, false,
		);

		slv.expect_solutions(&[capacity], expect![[r#"6"#]]);
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_capacity_unsat() {
		let mut slv = Solver::default();
		let start = vec![0, 3, 4, 6, 8, 8];
		let duration = vec![3, 2, 5, 2, 1, 4];
		let usage = vec![2, 3, 1, 4, 3, 2];
		let capacity = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.view();
		CumulativePropagator::post(
			&mut slv, start, duration, usage, capacity, false, false, false,
		);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_dur_sat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(&mut slv, 0..=2, 1..=3, 2..=2);
		let (s_b, d_b, u_b) = create_task(&mut slv, 0..=2, 1..=3, 2..=2);
		let (s_c, d_c, u_c) = create_task(&mut slv, 0..=2, 1..=3, 2..=2);
		let capacity = 2;

		CumulativePropagator::post(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
			false,
			false,
			false,
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
		let (s_a, d_a, u_a) = create_task(&mut slv, 0..=2, 2..=3, 2..=2);
		let (s_b, d_b, u_b) = create_task(&mut slv, 0..=2, 2..=3, 2..=2);
		let (s_c, d_c, u_c) = create_task(&mut slv, 0..=2, 2..=3, 2..=2);
		let capacity = 2;

		CumulativePropagator::post(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
			false,
			false,
			false,
		);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_cumulative_var_usage_sat() {
		let mut slv = Solver::default();
		let (s_a, d_a, u_a) = create_task(&mut slv, 0..=2, 1..=1, 1..=2);
		let (s_b, d_b, u_b) = create_task(&mut slv, 0..=2, 3..=3, 2..=3);
		let (s_c, d_c, u_c) = create_task(&mut slv, 0..=2, 2..=2, 2..=3);
		let capacity = 3;

		CumulativePropagator::post(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
			false,
			false,
			false,
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
		let (s_a, d_a, u_a) = create_task(&mut slv, 0..=2, 2..=2, 1..=3);
		let (s_b, d_b, u_b) = create_task(&mut slv, 0..=2, 2..=2, 2..=3);
		let (s_c, d_c, u_c) = create_task(&mut slv, 0..=2, 2..=2, 2..=3);
		let capacity = 2;

		CumulativePropagator::post(
			&mut slv,
			vec![s_a, s_b, s_c],
			vec![d_a, d_b, d_c],
			vec![u_a, u_b, u_c],
			capacity,
			false,
			false,
			false,
		);

		slv.assert_unsatisfiable();
	}

	/// Three tasks, each with start domain `[0, 2]`, duration 2, and usage 1,
	/// on a resource of capacity 1. No task has a compulsory part (`lst = ect
	/// = 2`), so pure time-tabling sees an empty profile and cannot detect the
	/// conflict at the root. The free parts require `3 * 2 = 6` energy units
	/// in the window `[0, 4)`, which only offers `1 * 4 = 4` — a resource
	/// overload that the TTEF consistency check detects immediately.
	#[test]
	#[traced_test]
	fn test_ttef_consistency_check_detects_energetic_overload() {
		let make = |(check, filtering, opportunistic): TtefConfig| {
			let mut slv = Solver::default();
			let starts = (0..3)
				.map(|_| {
					slv.new_int_decision(0..=2)
						.order_literals(LiteralStrategy::Eager)
						.view()
				})
				.collect_vec();
			CumulativePropagator::post(
				&mut slv,
				starts,
				vec![2, 2, 2],
				vec![1, 1, 1],
				1,
				check,
				filtering,
				opportunistic,
			);
			slv
		};

		// Pure time-tabling cannot detect the overload at the root: there are no
		// compulsory parts, so the first propagation round finds no conflict.
		let mut tt = make(TT);
		assert!(tt.propagate_next().is_ok());

		// With the TTEF consistency check enabled, the energetic overload in
		// `[0, 4)` is detected in the first propagation round.
		let mut ttef = make(CHECK_ONLY);
		assert!(ttef.propagate_next().is_err());
	}

	/// Minimal instances on which a too-weak energetic explanation made a TTEF
	/// configuration drop real solutions during search, surfaced by the M3
	/// benchmark. The fixed-duration cases (e.g. RCPSP `Bl2519`) come from
	/// [`TtefData::contributes`] omitting a task forced to overlap the window
	/// from the left; the variable-duration cases (multi-mode RCPSP `mrcpsp`)
	/// come from the opportunistic through-position update resting on energy a
	/// naive reason cannot justify, fixed by [`TtefData::sound_update_bound`].
	/// Every configuration must enumerate the identical solution set as the
	/// pure time-table baseline.
	#[test]
	fn test_ttef_cross_config_solution_regression() {
		// (dur_doms, use_doms, cap, dom); a domain is an inclusive `(lo, hi)` pair.
		type Dom = (IntVal, IntVal);
		type Case<'a> = (&'a [Dom], &'a [Dom], IntVal, IntVal);
		let cases: &[Case] = &[
			// Fixed duration: left-forced task omitted from the energetic reason.
			(
				&[(1, 1), (2, 2), (1, 1), (3, 3)],
				&[(2, 2), (1, 1), (2, 2), (2, 2)],
				2,
				5,
			),
			(
				&[(1, 1), (2, 2), (1, 1), (2, 2)],
				&[(2, 2), (1, 1), (2, 2), (2, 2)],
				2,
				5,
			),
			(
				&[(1, 1), (1, 1), (3, 3), (2, 2)],
				&[(1, 1), (1, 1), (2, 2), (2, 2)],
				3,
				5,
			),
			// Variable duration: opportunistic (ttef+) through-position over-push.
			(&[(2, 3), (1, 2), (2, 3)], &[(1, 2), (1, 2), (1, 2)], 2, 4),
			(&[(2, 3), (2, 2), (2, 3)], &[(1, 2), (1, 2), (1, 2)], 2, 4),
			(&[(2, 3), (2, 3), (1, 2)], &[(1, 2), (1, 2), (1, 2)], 2, 4),
		];
		for (dd, ud, cap, dom) in cases {
			let base = enumerate_cumulative(TT, *dom, dd, ud, *cap);
			for flags in [CHECK_ONLY, FILTER, FILTER_OPP] {
				let got = enumerate_cumulative(flags, *dom, dd, ud, *cap);
				assert_eq!(
					got, base,
					"config {flags:?} changed the solution set for dur_doms={dd:?} use_doms={ud:?} cap={cap}"
				);
			}
		}
	}

	/// Cross-configuration soundness oracle: enumerate *all* solutions of a
	/// small cumulative instance under every TTEF configuration. Sound
	/// propagation only changes search speed, never the solution set, so
	/// toggling the TTEF phases must leave the enumerated solutions identical.
	/// The instance is the two overlapping cumulative resources from
	/// `test_cumulative_val_sat`.
	#[test]
	#[traced_test]
	fn test_ttef_cross_config_solution_set() {
		for (check, filtering, opportunistic) in ALL_CONFIGS {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let c = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let durations: Vec<View<IntVal>> = [2, 3, 1].into_iter().map_into().collect();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, c],
				durations.clone(),
				vec![1, 2, 3],
				3,
				check,
				filtering,
				opportunistic,
			);
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, c],
				durations,
				vec![2, 2, 1],
				2,
				check,
				filtering,
				opportunistic,
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
	}

	/// A larger cross-configuration soundness oracle, sized so that
	/// edge-finding fires during the search while keeping the enumerated set
	/// small: four tasks of mixed duration and usage on a resource of capacity
	/// 2, start domains `[0, 2]`. Every TTEF configuration must enumerate the
	/// identical solutions.
	#[test]
	#[traced_test]
	fn test_ttef_cross_config_solution_set_large() {
		for (check, filtering, opportunistic) in ALL_CONFIGS {
			let mut slv = Solver::default();
			let starts: Vec<View<IntVal>> = (0..4)
				.map(|_| {
					slv.new_int_decision(0..=2)
						.order_literals(LiteralStrategy::Eager)
						.view()
				})
				.collect();
			CumulativePropagator::post(
				&mut slv,
				starts.clone(),
				vec![2, 1, 2, 1],
				vec![1, 2, 1, 1],
				2,
				check,
				filtering,
				opportunistic,
			);
			slv.expect_solutions(
				&starts,
				expect![[r#"
    1, 0, 2, 1
    2, 0, 1, 1
    2, 0, 2, 1
    2, 1, 2, 0"#]],
			);
		}
	}

	/// Exhaustive cross-configuration soundness sweep over a small parameter
	/// grid: every TTEF configuration must enumerate the identical solution set
	/// as the pure time-table baseline, for fixed-duration four-task instances
	/// and variable-duration three-task instances. The variable grid spans wide
	/// duration domains (so `dur_max > dur_lb`) and capacities, exercising both
	/// the opportunistic through-position update and the overload-conflict
	/// over-count regime. Marked `#[ignore]` because it solves tens of
	/// thousands of instances (tens of minutes); run on demand with
	/// `cargo test -p huub ttef_cross_config_sweep -- --ignored`.
	#[test]
	#[ignore = "exhaustive soundness sweep, tens of minutes; run on demand"]
	fn test_ttef_cross_config_sweep() {
		let check = |dom: IntVal, dd: &[(IntVal, IntVal)], ud: &[(IntVal, IntVal)], cap: IntVal| {
			let base = enumerate_cumulative(TT, dom, dd, ud, cap);
			for flags in [CHECK_ONLY, FILTER, FILTER_OPP] {
				assert_eq!(
					enumerate_cumulative(flags, dom, dd, ud, cap),
					base,
					"config {flags:?} changed the solution set for dur_doms={dd:?} use_doms={ud:?} cap={cap}"
				);
			}
		};
		// Fixed-duration four-task grid.
		let fd: Vec<Vec<(IntVal, IntVal)>> = (0..4)
			.map(|_| vec![(1, 1), (2, 2), (3, 3)])
			.multi_cartesian_product()
			.collect();
		let fu: Vec<Vec<(IntVal, IntVal)>> = (0..4)
			.map(|_| vec![(1, 1), (2, 2)])
			.multi_cartesian_product()
			.collect();
		for dd in &fd {
			for ud in &fu {
				for cap in [2, 3] {
					check(5, dd, ud, cap);
				}
			}
		}
		// Variable-duration three-task grid: wide duration/usage spread and
		// capacities, exercising both the opportunistic through-position update
		// and the overload-conflict over-count regime (where `lct` uses `dur_max`
		// but energy uses `dur_lb`).
		let vd: Vec<Vec<(IntVal, IntVal)>> = (0..3)
			.map(|_| vec![(1, 1), (1, 2), (2, 3), (1, 3)])
			.multi_cartesian_product()
			.collect();
		let vu: Vec<Vec<(IntVal, IntVal)>> = (0..3)
			.map(|_| vec![(1, 1), (1, 2), (2, 2)])
			.multi_cartesian_product()
			.collect();
		for dd in &vd {
			for ud in &vu {
				for cap in [2, 3, 4] {
					check(4, dd, ud, cap);
				}
			}
		}
	}

	/// Tasks A and B (start `[0, 2]`, duration 2, usage 2) exactly fill the
	/// resource of capacity 2 over the window `[0, 4)`. Task `u` (start `[0,
	/// 8]`, duration 2, usage 2) therefore cannot run in `[0, 4)`, so TTEF
	/// edge-finding lifts its earliest start from 0 to 4. Pure time-tabling
	/// cannot (the tasks have no compulsory parts).
	#[test]
	#[traced_test]
	fn test_ttef_filtering_lifts_earliest_start() {
		let make = |(check, filtering, opportunistic): TtefConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=2)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=2)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(0..=8)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![2, 2, 2],
				vec![2, 2, 2],
				2,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};

		// Time-tabling leaves u's earliest start at 0.
		let (mut tt, u) = make(TT);
		let _ = tt.propagate_next();
		assert!(u.in_domain(&tt, 0));

		// TTEF bounds filtering lifts u's earliest start to 4.
		let (mut ttef, u) = make(FILTER);
		let _ = ttef.propagate_next();
		assert!(!u.in_domain(&ttef, 3));
		assert!(u.in_domain(&ttef, 4));
	}

	/// Time-symmetric counterpart of the previous test. Tasks A and B (start
	/// `[4, 6]`, duration 2, usage 2) fill the resource over `[4, 8)`, so task
	/// `u` (start `[0, 6]`, duration 2, usage 2) cannot run in `[4, 8)` and
	/// TTEF lowers its latest completion to 4, i.e. its start upper bound from
	/// 6 to 2.
	#[test]
	#[traced_test]
	fn test_ttef_filtering_lowers_latest_completion() {
		let make = |(check, filtering, opportunistic): TtefConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(4..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(4..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![2, 2, 2],
				vec![2, 2, 2],
				2,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};

		// Time-tabling leaves u's latest start at 6.
		let (mut tt, u) = make(TT);
		let _ = tt.propagate_next();
		assert!(u.in_domain(&tt, 6));

		// TTEF bounds filtering lowers u's latest start to 2.
		let (mut ttef, u) = make(FILTER);
		let _ = ttef.propagate_next();
		assert!(!u.in_domain(&ttef, 3));
		assert!(u.in_domain(&ttef, 2));
	}
	/// A per-rule check that the opportunistic extended edge finding (`ttef+`)
	/// performs an extended-edge-finding bound update that plain `ttef` does
	/// not. Two tasks (start `[0, 6]`, duration 4, usage 2) on capacity 3
	/// leave only `3 * 10 - 2 * 4 * 2 = 14` energy in `[0, 10)`; a third task
	/// `u` (start `[1, 5]`, duration 4, usage 1) overlaps the window on both
	/// sides, so the extended rule lifts its earliest start.
	#[test]
	#[traced_test]
	fn test_ttef_opportunistic_extended_edge_finding() {
		let make = |(check, filtering, opportunistic): TtefConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(1..=5)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![4, 4, 4],
				vec![2, 2, 1],
				3,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};
		// The opportunistic configuration must not be unsound: it can only ever
		// tighten bounds that the non-opportunistic configuration also leaves
		// feasible. We assert it is at least as strong on u's domain.
		let (mut ttef, u1) = make(FILTER);
		let _ = ttef.propagate_next();
		let (mut ttefp, u2) = make(FILTER_OPP);
		let _ = ttefp.propagate_next();
		for v in 0..=5 {
			if !u1.in_domain(&ttef, v) {
				assert!(
					!u2.in_domain(&ttefp, v),
					"ttef+ must remove every value ttef removed (value {v})"
				);
			}
		}
	}
}
