//! Structures and algorithms for the `cumulative` constraint, which
//! ensures that the sum of resource usages of all tasks
//! running at any time does not exceed the resource capacity.

mod edge_finding;
mod time_table;

use itertools::Itertools;

use crate::{
	IntVal,
	actions::{
		InitActions, IntAnalyzeActions, IntInspectionActions, IntPropCond, PostingActions,
		ReasoningContext, ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model,
	solver::{Polarity, engine::Engine, queue::PriorityLevel},
};

/// The largest capacity for which the knapsack-based strengthening rules run.
/// The knapsack dynamic program is `O(n * capacity)` per task, so a very large
/// capacity would make strengthening disproportionately expensive for little
/// gain; the cheap saturation and gcd rules always run.
const MAX_KNAPSACK_CAPACITY: IntVal = 10_000;

/// Representation of the `cumulative` constraint within a model.
///
/// This constriant enforces that the given a set of tasks, each with a start
/// time, duration, and resource usage, do not exceed the specified resource
/// capacity at any point in time. The constraint can optionally apply
/// edge finding propagation to strengthen the reasoning about
/// the tasks' scheduling.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cumulative {
	/// Inner propagator.
	pub(crate) propagator: CumulativePropagator<
		model::View<IntVal>,
		model::View<IntVal>,
		model::View<IntVal>,
		model::View<IntVal>,
	>,
	/// Whether to apply the edge-finding consistency check during
	/// propagation.
	///
	/// Defaults to `true`.
	pub(crate) energy_overload_checking: Option<bool>,
	/// Whether to apply the edge-finding bounds-filtering during
	/// propagation.
	///
	/// Defaults to `false`.
	pub(crate) edge_finding_propagation: Option<bool>,
	/// Whether to apply the edge-finding opportunistic
	/// extended-edge-finding during propagation.
	///
	/// Defaults to `false`.
	pub(crate) opportunistic_edge_finding_propagation: Option<bool>,
}

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

/// A propagator for the `cumulative` constraint using time-table propagation
/// and optionally edge finding algorithms.
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
/// - J. Schulz, "Hybrid Solving Techniques for Project Scheduling Problems", TU
///   Berlin, 2012
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
	/// Whether to run the edge-finding consistency check on top of the
	/// time-table propagation.
	energy_overload_check_enabled: bool,
	/// Whether to run the edge-finding bounds-filtering phase.
	edge_finding_propagation_enabled: bool,
	/// Whether to run the opportunistic extended-edge-finding phase.
	opportunistic_edge_finding_propagation_enabled: bool,
	/// Bounds of the time intervals where tasks are active.
	bounds: Vec<IntVal>,
	/// Heights of the time intervals, representing the total resource usage at
	/// that time.
	heights: Vec<IntVal>,
}

impl Cumulative {
	/// Returns whether the edge-finding bounds-filtering is used when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn edge_finding_propagation_enabled(&self) -> bool {
		self.edge_finding_propagation.unwrap_or(false)
	}

	/// Returns whether the edge-finding consistency check is used when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn energy_overload_checking_enabled(&self) -> bool {
		self.energy_overload_checking.unwrap_or(true)
	}

	/// Read the fixed usages and capacity, or return `None` when any is still
	/// unfixed or the instance is ill-formed (a non-positive capacity, or a
	/// usage outside `0..=capacity`), in which case no strengthening is
	/// attempted.
	fn fixed_usages<E>(&self, ctx: &mut E::PropagationContext<'_>) -> Option<Vec<IntVal>>
	where
		E: ReasoningEngine,
		model::View<IntVal>: IntModelActions<E>,
	{
		let mut usages = Vec::with_capacity(self.propagator.usages.len());
		for usage in &self.propagator.usages {
			usages.push(usage.val(ctx)?);
		}
		Some(usages)
	}

	/// Read each task's `[est, lct)` window from the current start-time bounds
	/// and the durations, or return `None` when any duration is still unfixed.
	fn fixed_windows<E>(&self, ctx: &mut E::PropagationContext<'_>) -> Option<Vec<(IntVal, IntVal)>>
	where
		E: ReasoningEngine,
		model::View<IntVal>: IntModelActions<E>,
	{
		let mut windows = Vec::with_capacity(self.propagator.start_times.len());
		for (start, duration) in self
			.propagator
			.start_times
			.iter()
			.zip(&self.propagator.durations)
		{
			let (earliest_start, latest_start) = start.bounds(ctx);
			windows.push((earliest_start, latest_start + duration.val(ctx)?));
		}
		Some(windows)
	}

	/// The largest total that some subset of `weights` can reach without
	/// exceeding `capacity`, a bounded max-subset-sum solved by dynamic
	/// programming.
	fn max_reachable_load(weights: &[IntVal], capacity: IntVal) -> IntVal {
		if capacity <= 0 {
			return 0;
		}
		let cap = capacity as usize;
		let mut reachable = vec![false; cap + 1];
		reachable[0] = true;
		let mut best = 0;
		for &w in weights {
			if w <= 0 || w > capacity {
				continue;
			}
			let w = w as usize;
			// Iterate downward so that each item contributes at most once.
			for s in (0..=cap - w).rev() {
				if reachable[s] && !reachable[s + w] {
					reachable[s + w] = true;
					best = best.max((s + w) as IntVal);
					if best == capacity {
						return best;
					}
				}
			}
		}
		best
	}

	/// Returns whether the edge-finding opportunistic
	/// extended-edge-finding is used when creating a
	/// [`Solver`](crate::solver::Solver) object.
	pub fn opportunistic_edge_finding_propagation_enabled(&self) -> bool {
		self.opportunistic_edge_finding_propagation.unwrap_or(false)
	}

	/// Raise the usage of every task that cannot run in parallel with any other
	/// resource-using task up to the capacity (Schulz Corollary 3.1). Such a
	/// task already occupies the whole resource, so saturating its usage
	/// removes no solution and strengthens the energy arguments.
	fn saturate_usages(usages: &mut [IntVal], capacity: IntVal) {
		// The smallest usage that any other resource-using task could run
		// alongside; a task using more than the capacity left by it cannot share
		// the resource with any other task.
		let Some(r_min) = usages
			.iter()
			.copied()
			.filter(|&r| 0 < r && r < capacity)
			.min()
		else {
			return;
		};
		for usage in usages.iter_mut() {
			if *usage < capacity && *usage > capacity - r_min {
				*usage = capacity;
			}
		}
	}

	/// Inflate each task's usage to fill the gap left by the tasks that can run
	/// concurrently with it.
	///
	/// Requires constant durations for all tasks.
	fn strengthen_usages(usages: &mut [IntVal], capacity: IntVal, windows: &[(IntVal, IntVal)]) {
		// The knapsack dynamic program is `O(n * capacity)`; skip it for very large
		// capacities, where it would cost more than it can save.
		if capacity > MAX_KNAPSACK_CAPACITY {
			return;
		}

		let n = usages.len();
		// Strengthen usages sequentially since each update changes the knapsacks of
		// later tasks.
		for j in 0..n {
			let r_j = usages[j];
			let (est_j, lct_j) = windows[j];
			if r_j == 0 || r_j >= capacity || est_j >= lct_j {
				continue;
			}
			// The most the tasks that can overlap task `j` use together is a
			// knapsack over their usages bounded by the capacity left for them, so
			// task `j` can claim whatever remains.
			let others: Vec<IntVal> = (0..n)
				.filter(|&i| i != j)
				.filter_map(|i| {
					let (est_i, lct_i) = windows[i];
					// The windows `[est_i, lct_i)` and `[est_j, lct_j)` overlap.
					(est_i < lct_j && est_j < lct_i && usages[i] > 0).then_some(usages[i])
				})
				.collect();
			let others_max = Self::max_reachable_load(&others, capacity - r_j);
			if capacity - others_max > r_j {
				usages[j] = capacity - others_max;
			}
		}
	}

	/// Lower the capacity to the largest load that any set of
	/// concurrently-runnable tasks can actually reach.
	///
	/// Requires constant durations for all tasks.
	fn tighten_capacity(
		usages: &mut [IntVal],
		capacity: &mut IntVal,
		windows: &[(IntVal, IntVal)],
	) {
		// The knapsack dynamic program is `O(n * capacity)`; skip it for very large
		// capacities, where it would cost more than it can save.
		if *capacity > MAX_KNAPSACK_CAPACITY {
			return;
		}

		// The new capacity must stay at least as large as every non-saturating
		// usage (each is reachable on its own), and at least one.
		let mut best = usages
			.iter()
			.copied()
			.filter(|&u| 0 < u && u < *capacity)
			.max()
			.unwrap_or(1);

		// The reachable load at each time point is a knapsack over the tasks whose
		// window covers it.
		let starts: Vec<IntVal> = windows
			.iter()
			.map(|&(est, _)| est)
			.sorted()
			.dedup()
			.collect();
		for t in starts {
			let active: Vec<IntVal> = usages
				.iter()
				.zip(windows)
				.filter_map(|(&r, &(est, lct))| {
					(est <= t && t < lct && 0 < r && r < *capacity).then_some(r)
				})
				.collect();
			let reachable = Self::max_reachable_load(&active, *capacity);
			// If the reachable load is already at least the current capacity, no
			// strengthening is possible.
			if reachable >= *capacity {
				return;
			}
			best = best.max(reachable);
		}

		// Tasks that used the old capacity are lowered to the new one.
		for usage in usages.iter_mut() {
			if *usage == *capacity {
				*usage = best;
			}
		}
		*capacity = best;
	}
}

impl<E> Constraint<E> for Cumulative
where
	E: ReasoningEngine,
	model::View<IntVal>: IntModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		// The constraint is easier to satisfy with a larger resource capacity,
		// and with tasks that use less of the resource for a shorter time.
		self.propagator.capacity.polarity(ctx, Polarity::Positive);
		for usage in &self.propagator.usages {
			usage.polarity(ctx, Polarity::Negative);
		}
		for duration in &self.propagator.durations {
			duration.polarity(ctx, Polarity::Negative);
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Perform coefficient strengthening on a single working copy of the fixed
		// coefficients, then rewrite the changed usages and capacity in one pass so
		// that the usages and capacity can never fall out of sync.
		if let Some(mut capacity) = self.propagator.capacity.val(ctx)
			&& let Some(mut usages) = self.fixed_usages(ctx)
		{
			let before_usages = usages.clone();
			let before_capacity = capacity;
			Self::saturate_usages(&mut usages, capacity);
			if let Some(windows) = self.fixed_windows(ctx) {
				Self::tighten_capacity(&mut usages, &mut capacity, &windows);
				Self::strengthen_usages(&mut usages, capacity, &windows);
			}
			for (view, (&before, &after)) in self
				.propagator
				.usages
				.iter_mut()
				.zip(before_usages.iter().zip(&usages))
			{
				if before != after {
					*view = after.into();
				}
			}
			if capacity != before_capacity {
				self.propagator.capacity = capacity.into();
			}
		}

		// Delagate to the inner propagator's propagate method.
		self.propagator.propagate(ctx)?;

		if self.propagator.capacity.val(ctx).is_some()
			&& self
				.propagator
				.start_times
				.iter()
				.all(|v| v.val(ctx).is_some())
			&& self
				.propagator
				.durations
				.iter()
				.all(|v| v.val(ctx).is_some())
			&& self.propagator.usages.iter().all(|v| v.val(ctx).is_some())
		{
			Ok(SimplificationStatus::Subsumed)
		} else {
			Ok(SimplificationStatus::NoFixpoint)
		}
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let start_times = self
			.propagator
			.start_times
			.iter()
			.map(|v| slv.solver_view(*v))
			.collect_vec();
		let durations = self
			.propagator
			.durations
			.iter()
			.map(|v| slv.solver_view(*v))
			.collect_vec();
		let usages = self
			.propagator
			.usages
			.iter()
			.map(|v| slv.solver_view(*v))
			.collect_vec();
		let capacity = slv.solver_view(self.propagator.capacity);
		CumulativePropagator::post(
			slv,
			start_times,
			durations,
			usages,
			capacity,
			self.energy_overload_checking_enabled(),
			self.edge_finding_propagation_enabled(),
			self.opportunistic_edge_finding_propagation_enabled(),
		);
		Ok(())
	}
}

impl<E> Propagator<E> for Cumulative
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		self.propagator.initialize(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		self.propagator.propagate(ctx)
	}
}

impl<I1, I2, I3, I4> CumulativePropagator<I1, I2, I3, I4> {
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

	/// Whether any edge-finding phase is enabled on top of the
	/// time-table propagation.
	#[inline]
	fn edge_finding_enabled(&self) -> bool {
		self.energy_overload_check_enabled
			|| self.edge_finding_propagation_enabled
			|| self.opportunistic_edge_finding_propagation_enabled
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

	/// Creates a new `CumulativePropagator` running the edge-finding
	/// phases selected by the `*_enabled` phase flags on top of the time-table
	/// propagation.
	pub(crate) fn new(
		start_times: Vec<I1>,
		durations: Vec<I2>,
		usages: Vec<I3>,
		capacity: I4,
		energy_overload_check_enabled: bool,
		edge_finding_propagation_enabled: bool,
		opportunistic_edge_finding_propagation_enabled: bool,
	) -> Self {
		Self {
			start_times,
			durations,
			usages,
			capacity,
			energy_overload_check_enabled,
			edge_finding_propagation_enabled,
			opportunistic_edge_finding_propagation_enabled,
			bounds: Vec::new(),
			heights: Vec::new(),
		}
	}

	/// Creates a new `CumulativePropagator` with the given edge-finding
	/// flags and posts it in the solver.
	#[expect(
		clippy::too_many_arguments,
		reason = "the `cumulative` constraint takes four decision arguments plus the three edge-finding phase toggles"
	)]
	pub fn post<E>(
		solver: &mut E,
		start_times: Vec<I1>,
		durations: Vec<I2>,
		usages: Vec<I3>,
		capacity: I4,
		energy_overload_check_enabled: bool,
		edge_finding_propagation_enabled: bool,
		opportunistic_edge_finding_propagation_enabled: bool,
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
			energy_overload_check_enabled,
			edge_finding_propagation_enabled,
			opportunistic_edge_finding_propagation_enabled,
		)));
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
			// changes, so that the profile (and the edge finding below)
			// operate on up-to-date bounds.
			if bounds_updated {
				return Ok(());
			}
		}

		// Time-table-edge-finding phases run once the time-table propagation has
		// reached its fixpoint. Unlike the time-table phase, edge-finding can also
		// propagate when there are no compulsory parts, so it runs regardless of
		// whether the profile is empty. It returns early when it updated a bound.
		if self.edge_finding_enabled() {
			self.propagate_edge_finding(ctx)?;
		}

		if !profile_empty {
			for i in 0..self.start_times.len() {
				let (req_lb, req_ub) = self.usages[i].bounds(ctx);
				if req_lb < req_ub
					&& self.latest_start_time(ctx, i) < self.earliest_completion_time(ctx, i)
				{
					self.limit_usage(ctx, i)?;
				}
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		actions::IntInspectionActions,
		model::{ConRef, Model},
		solver::Solver,
	};

	/// Every edge-finding configuration `(check, filtering,
	/// opportunistic)`; the model applies them all during full propagation,
	/// and each must preserve the solution set.
	const ALL_CONFIGS: [EdgeFindingConfig; 4] = [
		(false, false, false),
		(true, false, false),
		(true, true, false),
		(true, true, true),
	];

	/// An edge-finding configuration as `(check, filtering,
	/// opportunistic)`.
	type EdgeFindingConfig = (bool, bool, bool);

	/// The model runs full edge finding during simplification, so an
	/// energy overload is detected when the constraint is posted regardless
	/// of the configured edge-finding phases (the phases only govern the
	/// lowered solver).
	#[test]
	#[traced_test]
	fn test_cumulative_model_check_detects_unsat() {
		let post_overload = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut prb = Model::default();
			let starts = prb.new_int_decisions(3, 0..=2);
			prb.cumulative()
				.start_times(starts)
				.durations(vec![2, 2, 2])
				.usages(vec![1, 1, 1])
				.capacity(1)
				.maybe_energy_overload_checking(Some(check))
				.maybe_edge_finding_propagation(Some(filtering))
				.maybe_opportunistic_edge_finding_propagation(Some(opportunistic))
				.post()
		};

		// Full model propagation detects the energy overload under every
		// configuration, including pure time-tabling.
		for config in ALL_CONFIGS {
			assert!(post_overload(config).is_err());
		}
	}

	/// Soundness across every edge-finding configuration selected
	/// through the model builder (model -> solver): each configuration must
	/// lower to a propagator that enumerates the shared four-task solution
	/// set, so choosing a configuration through the `maybe_*` phase toggles
	/// and carrying it through lowering never drops a solution.
	#[test]
	#[traced_test]
	fn test_cumulative_model_config_solution_set() {
		for (check, filtering, opportunistic) in ALL_CONFIGS {
			let mut prb = Model::default();
			let starts = prb.new_int_decisions(4, 0..=2);
			prb.cumulative()
				.start_times(starts.clone())
				.durations(vec![2, 1, 2, 1])
				.usages(vec![1, 2, 1, 1])
				.capacity(2)
				.maybe_energy_overload_checking(Some(check))
				.maybe_edge_finding_propagation(Some(filtering))
				.maybe_opportunistic_edge_finding_propagation(Some(opportunistic))
				.post()
				.unwrap();
			let (mut slv, map) = prb.lower().to_solver().unwrap();
			let starts = starts
				.into_iter()
				.map(|x| map.get(&mut slv, x))
				.collect_vec();
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

	/// The model runs full edge finding during simplification, so
	/// its bounds filtering lifts an earliest start that pure time-tabling
	/// cannot, regardless of the configured phases.
	#[test]
	#[traced_test]
	fn test_cumulative_model_filtering_lifts_earliest_start() {
		let make = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut prb = Model::default();
			let a = prb.new_int_decision(0..=2);
			let b = prb.new_int_decision(0..=2);
			let u = prb.new_int_decision(0..=8);
			prb.cumulative()
				.start_times(vec![a, b, u])
				.durations(vec![2, 2, 2])
				.usages(vec![2, 2, 2])
				.capacity(2)
				.maybe_energy_overload_checking(Some(check))
				.maybe_edge_finding_propagation(Some(filtering))
				.maybe_opportunistic_edge_finding_propagation(Some(opportunistic))
				.post()
				.unwrap();
			let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
			let u = map.get(&mut slv, u);
			(slv, u)
		};

		for config in ALL_CONFIGS {
			let (slv, u) = make(config);
			assert!(!u.in_domain(&slv, 3));
			assert!(u.in_domain(&slv, 4));
		}
	}

	/// Full model propagation (time-tabling plus edge-finding) reaches the
	/// fixpoint in a single round.
	#[test]
	#[traced_test]
	fn test_cumulative_propagate() {
		let mut prb = Model::default();
		// Tasks A and B (start [0, 2], duration 3) each have a compulsory part in
		// [0, 2]; task C (start [0, 4], duration 3) has none.
		let start_time_a = prb.new_int_decision(0..=2);
		let start_time_b = prb.new_int_decision(0..=2);
		let start_time_c = prb.new_int_decision(0..=4);
		let usages = prb.new_int_decisions(3, 1..=2);
		prb.cumulative()
			.start_times(vec![start_time_a, start_time_b, start_time_c])
			.durations(vec![3, 3, 3])
			.usages(usages.clone())
			.capacity(2)
			.post()
			.unwrap();

		let _ = prb.propagate_single(ConRef::from_raw(0));
		assert_eq!(start_time_a.bounds(&prb), (0, 2));
		assert_eq!(usages[0].bounds(&prb), (1, 1));
		assert_eq!(start_time_b.bounds(&prb), (0, 2));
		assert_eq!(usages[1].bounds(&prb), (1, 1));
		assert_eq!(start_time_c.bounds(&prb), (3, 4));
		assert_eq!(usages[2].bounds(&prb), (1, 2));
	}
}
