//! Structures and algorithms for the `disjunctive_strict` constraint, which
//! enforces that no two tasks overlap from a list of tasks.

use itertools::Itertools;
use tracing::trace;

use crate::{
	Conjunction, IntVal,
	actions::{
		ConstructionActions, InitActions, IntDecisionActions, IntInspectionActions, PostingActions,
		PropagationActions, ReasoningContext, ReasoningEngine, Trailed, TrailingActions,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, ReasonBuilder,
		SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model,
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `disjunctive` constraint within a model.
///
/// This constraint enforces that the given a list of integer decision variables
/// representing the start times of tasks and a list of integer values
/// representing the durations of tasks, the tasks do not overlap in time.
pub struct Disjunctive {
	/// Inner propagator.
	pub(crate) propagator: DisjunctivePropagator<model::View<IntVal>>,
	/// Whether to enable the [`DisjunctivePropagationRule::EdgeFinding`]
	/// propagation rule.
	///
	/// Defaults to `true`.
	pub(crate) edge_finding_propagation: Option<bool>,
	/// Whether to enable the [`DisjunctivePropagationRule::NotLast`]
	/// propagation rule.
	///
	/// Defaults to `false`.
	pub(crate) not_last_propagation: Option<bool>,
	/// Whether to enable the [`DisjunctivePropagationRule::Precedence`]
	/// propagation rule.
	///
	/// Defaults to `false`.
	pub(crate) detectable_precedence_propagation: Option<bool>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// The propagation rules for the `disjunctive` constraint. This enum is
/// used to identify which propagation algorithm is being applied during the
/// propagation phase of the `DisjunctiveStrictPropagator`. Values:
///
/// - `EdgeFinding`: The edge finding propagation rule in function
///   `propagate_edge_finding`.
/// - `NotLast`: The not-last propagation rule in function `propagate_not_last`.
/// - `Precedence`: The detectable precedence propagation rule in function
///   `propagate_detectable_precedence`.
enum DisjunctivePropagationRule {
	/// The edge finding propagation in `propagate_edge_finding`.
	EdgeFinding,
	/// The not-last propagation in `propagate_not_last`.
	NotLast,
	/// The precedence propagation in `propagate_detectable_precedence`.
	Precedence,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `disjunctive` constraint using the Overload
/// Checking, Edge Finding, Not-First/Not-Last, and Detectable Precedence
/// algorithms. Refer to the corresponding functions for details on propagation
/// rules and explanations.
///
/// **References**
///
/// - Vilim, Petr "Filtering algorithms for the unary resource constraint."
///   Archives of Control Sciences 18.2 (2008): 159-202.
/// - Vilím, Petr "Computing explanations for the unary resource constraint."
///   CPAIOR 2005.
pub struct DisjunctivePropagator<I> {
	/// Start time variables of each task.
	start_times: Vec<I>,
	/// Durations of each task.
	durations: Vec<IntVal>,
	/// The Omega-Theta tree to compute the earliest completion time.
	ot_tree: OmegaThetaTree,
	/// Trailed earliest start and latest completion times to aid in
	/// explaination.
	trailed_info: Vec<TaskInfo>,

	// Flags for enabling/disabling propagation rules.
	/// Whether to enable the edge finding propagation.
	edge_finding_enabled: bool,
	/// Whether to enable the not-last propagation.
	not_last_enabled: bool,
	/// Whether to enable the detectable precedence propagation.
	detectable_precedence_enabled: bool,

	// Internal state for propagation
	/// Indexes of the tasks sorted by earliest start time.
	tasks_sorted_by_earliest_start: Vec<usize>,
	/// Indexes of the tasks sorted by latest start time.
	tasks_sorted_by_latest_start: Vec<usize>,
	/// Indexes of the tasks sorted by earliest completion time.
	tasks_sorted_by_earliest_completion: Vec<usize>,
	/// Indexes of the tasks sorted by latest completion time.
	tasks_sorted_by_latest_completion: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// The Omega-Theta tree is a balanced binary tree data structure used in
/// disjunctive scheduling to efficiently maintain and update earliest
/// completion times (ECT) for sets of tasks. Each leaf node represents a task;
/// internal nodes represent sets of tasks in their subtrees.
///
/// For a set of tasks Ω, the ECT at an internal node is computed recursively:
///
/// ect_v = max(ect_right, ect_left + total_duration_right)
///
/// where ect_right and ect_left are the ECTs of the right and left children,
/// and total_duration_right is the sum of durations in the right subtree. The
/// root node gives the ECT for all tasks in Ω.
///
/// The tree also maintains "gray" earliest completion times, used in
/// edge-finding propagation. Gray tasks (Ѳ) are tasks temporarily excluded from
/// Ω. The gray ECT is:
///
/// ect_gray(Ω, Ѳ) = max({ect_Ω} ∪ {ect_{Ω ∪ {i}} | i ∈ Ѳ})
///
/// where ect_{Ω ∪ {i}} is the ECT if gray task i is added back to Ω.
///
/// This structure allows efficient updates and queries for ECTs and gray ECTs
/// as tasks are added, removed, or marked gray. For details, see Vilim (2008).
struct OmegaThetaTree {
	/// Storage of the nodes of the tree.
	nodes: Vec<OmegaThetaTreeNode>,
	/// Index of the first leaf node.
	leaves_start_idx: usize,
	/// Mapping of the task number to the tree node index (offset by
	/// `leaves_start_idx`). The tasks are sorted by their earliest start time
	/// in the tree.
	node_index_offset: Vec<usize>,
	/// Mapping of the tree node index (offset by `leaves_start_idx`) to the
	/// task number.
	task_no: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A node structure for the [`OmegaThetaTree`].
struct OmegaThetaTreeNode {
	/// Total duration of the tasks under the tree rooted at this node.
	total_durations: i64,
	/// Earliest completion time of the tasks under the tree rooted at this
	/// node.
	earliest_completion: i64,
	/// Total duration of the tasks under the tree rooted at this node, with at
	/// most one gray node.
	total_durations_gray: i64,
	/// Earliest completion time of the tasks under the tree rooted at this
	/// node, with at most one gray node.
	earliest_completion_gray: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Internal structure to store trailed information about tasks.
struct TaskInfo {
	/// Earliest start time of the task.
	earliest_start: Trailed<IntVal>,
	/// Latest completion time of the task.
	latest_completion: Trailed<IntVal>,
}

impl Disjunctive {
	/// Return whether the detectable precedence algorithm will be used when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn detectable_precedence_propagation_enabled(&self) -> bool {
		self.detectable_precedence_propagation.unwrap_or(false)
	}

	/// Return whether the edge finding algorithm will be used when creating a
	/// [`Solver`](crate::solver::Solver) object.
	pub fn edge_finding_propagation_enabled(&self) -> bool {
		self.edge_finding_propagation.unwrap_or(true)
	}

	/// Return whether the not-last algorithm will be used when creating a
	/// [`Solver`](crate::solver::Solver) object.
	pub fn not_last_propagation_enabled(&self) -> bool {
		self.not_last_propagation.unwrap_or(false)
	}
}

impl<E> Constraint<E> for Disjunctive
where
	E: ReasoningEngine,
	model::View<IntVal>: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if self
			.propagator
			.start_times
			.iter()
			.all(|v| v.val(ctx).is_some())
		{
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let start_times = self
			.propagator
			.start_times
			.iter()
			.map(|&v| slv.solver_view(v))
			.collect_vec();
		// Add symmetric version of start time for upper bound propagation
		let iter = start_times.iter().zip(self.propagator.durations.iter());
		let horizon = iter.clone().map(|(v, d)| v.max(slv) + d).max().unwrap();
		let symmetric_vars: Vec<_> = iter.map(|(v, d)| -*v + (horizon - d)).collect();

		// Add detectable precedence propagators
		DisjunctivePropagator::post(
			slv,
			start_times,
			self.propagator.durations.clone(),
			self.edge_finding_propagation_enabled(),
			self.not_last_propagation_enabled(),
			self.detectable_precedence_propagation_enabled(),
		);
		DisjunctivePropagator::post(
			slv,
			symmetric_vars,
			self.propagator.durations.clone(),
			self.edge_finding_propagation_enabled(),
			self.not_last_propagation_enabled(),
			self.detectable_precedence_propagation_enabled(),
		);

		Ok(())
	}
}

impl<E> Propagator<E> for Disjunctive
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
{
	fn explain(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		self.propagator.explain(ctx, lit, data)
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		self.propagator.initialize(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.propagator.propagate(ctx)
	}
}

impl<I> DisjunctivePropagator<I> {
	/// Return the data stored for explanation from propagation rule and task
	/// number.
	fn data_for_explanation(
		&self,
		task_no: usize,
		propagation_rule: DisjunctivePropagationRule,
	) -> u64 {
		((propagation_rule as u64) << 62) + task_no as u64
	}

	/// Return the (current) earliest completion time of task `i`.
	fn earliest_completion_time<Ctx>(&self, ctx: &mut Ctx, i: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.earliest_start_time(ctx, i) + self.durations[i]
	}

	/// Return the (current) earliest start time of task `i`.
	fn earliest_start_time<Ctx>(&self, ctx: &mut Ctx, i: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.start_times[i].min(ctx)
	}

	/// Explain edge finding propagation for task `i` with the time window
	/// [`earliest_start`, `latest_completion`] For details, refer to the CPAIOR
	/// paper by Vilim (2005).
	fn explain_edge_finding<E>(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		task_no: usize,
		earliest_start: i64,
		latest_completion: i64,
	) -> Conjunction<E::Atom>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		// explain why the set of tasks LCut(j) ∪ {i} cannot be completed before
		// lct_j since energy of the set of tasks (including i) within the time
		// window [earliest_start, latest_completion] is overloaded
		let latest_completion_times = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(ctx, i))
			.collect_vec();
		let earliest_start_times = (0..self.start_times.len())
			.map(|i| self.earliest_start_time(ctx, i))
			.collect_vec();
		trace!(
			task_no,
			left_cut_set =? (0..self.start_times.len())
				.filter(|&j| {
					j != task_no
					&& earliest_start_times[j] >= earliest_start
					&& latest_completion_times[j] <= latest_completion
				})
				.map(|j| {
					(
						j,
						earliest_start_times[j],
						latest_completion_times[j],
					)
				})
				.collect_vec(),
			window =? (earliest_start, latest_completion),
			"explain edge finding"
		);

		// collect at least latest_completion - earliest_start energy (including
		// durations[task_no]) from tasks bracketed in
		// [earliest_start, latest_completion] and form a set O [start(t) >=
		// latest_completion + 1] because [start(t) >= earliest_start] /\ forall (t'
		// in O) [start(t') >= earliest_start] /\ forall (t' in O) [end(t') <=
		// latest_completion]
		let mut clause = Vec::new();
		let (bv, _) =
			self.start_times[task_no].lit_relaxed(ctx, IntLitMeaning::GreaterEq(earliest_start));
		clause.push(bv);
		let mut energy = latest_completion - earliest_start - self.durations[task_no];
		for i in 0..self.start_times.len() {
			if i != task_no
				&& earliest_start_times[i] >= earliest_start
				&& latest_completion_times[i] <= latest_completion
			{
				clause.push(self.start_times[i].min_lit(ctx));
				let (bv, _) = self.start_times[i].lit_relaxed(
					ctx,
					IntLitMeaning::Less(latest_completion - self.durations[i] + 1),
				);
				clause.push(bv);
				energy -= self.durations[i];
				if energy < 0 {
					break;
				}
			}
		}
		clause
	}

	/// Explain Not-Last propagation for task `i` with the time window
	/// [`earliest_start`, `updated_lct_i`] For details, refer to the CPAIOR
	/// paper by Vilim (2005).
	fn explain_not_last<E>(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		task_no: usize,
		earliest_start: i64,
		updated_lct_i: i64,
	) -> Conjunction<E::Atom>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		// Collect the set of tasks in NLset(i) = { j | lst_j < lct_i && est_j + p_j
		// ≥ earliest_start & j ≠ i }
		let nlset = (0..self.start_times.len())
			.filter(|j| {
				{
					*j != task_no
						&& self.latest_start_time(ctx, *j) <= updated_lct_i
						&& self.earliest_start_time(ctx, *j) >= earliest_start
				}
			})
			.collect_vec();

		trace!(
			task_no,
			window =? (earliest_start, updated_lct_i),
			nlset = ? nlset.iter().map(|&j| (j, self.durations[j], self.earliest_start_time(ctx,j, ), self.latest_start_time( ctx,j,))).collect_vec(),
			"explain not last"
		);

		assert_ne!(nlset.len(), 0);

		// Explain the reason why task i cannot be the last task
		let mut clause = Vec::new();
		clause.push(self.start_times[task_no].max_lit(ctx));
		for j in nlset {
			// explain the reason why all tasks in NLset(i) will stay in NLset(i)
			//
			// (1) If for all j in NLset(i) [est_j ≥ earliest_start], then ect_Ω >
			// lst_i, and NLset(i) \not\prec i
			let (bv, _) =
				self.start_times[j].lit_relaxed(ctx, IntLitMeaning::GreaterEq(earliest_start));
			clause.push(bv);
			// (2) explain the reason why the latest completion time of task i is set
			// to latest_completion If for all j in NLset(i) [lst_j ≤ lct_i'], then
			// max{lst_j, j \in Ω} ≤ lct_i', and lct_i' should be set
			let (bv, _) =
				self.start_times[j].lit_relaxed(ctx, IntLitMeaning::Less(updated_lct_i + 1));
			clause.push(bv);
		}
		clause
	}

	/// Explain resource overload within the time window
	/// [`earliest_start`,`time_bound`]. For details, refer to the CPAIOR paper
	/// by Vilim (2005).
	fn explain_overload_checking<Ctx>(&self, time_bound: i64) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let binding_task = self.ot_tree.binding_task(time_bound, 0);
			let earliest_start = self.start_times[binding_task].min(ctx);
			let mut slack = time_bound - earliest_start;
			let mut e_tasks = Vec::new();

			trace!(
				window =? (earliest_start, time_bound),
				"explain resource overload"
			);
			// collect sufficient energy within the window [lb, time_bound)
			for i in 0..self.tasks_sorted_by_earliest_start.len() {
				let task_no = self.tasks_sorted_by_earliest_start[i];
				if self.earliest_start_time(ctx, task_no) >= earliest_start
					&& self.latest_completion_time(ctx, task_no) < time_bound
				{
					e_tasks.push(task_no);
					slack -= self.durations[task_no];
					if slack <= 0 {
						break;
					}
				}
			}

			e_tasks
				.iter()
				.flat_map(|&i| {
					let bv = self.start_times[i].lit(
						ctx,
						IntLitMeaning::Less((time_bound - slack) - self.durations[i]),
					);
					[self.start_times[i].min_lit(ctx), bv]
				})
				.collect_vec()
		}
	}

	/// Explain precedence propagation for task `i` with the earliest start time
	/// For details, refer to the CPAIOR paper by Vilim (2005).
	fn explain_precedence<E>(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		task_no: usize,
		earliest_start: i64,
		latest_start: i64,
	) -> Conjunction<E::Atom>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		// Collect all tasks of which the earliest start time greater than
		// `earliest_start`
		let precedence_set = (0..self.start_times.len())
			.filter(|&j| {
				j != task_no
					&& self.earliest_start_time(ctx, j) >= earliest_start
					&& self.latest_start_time(ctx, j) < latest_start
			})
			.collect_vec();

		trace!(
			task_no,
			window =? (earliest_start, latest_start),
			precedence_set = ?precedence_set,
			"explain detectable precedence"
		);

		assert_ne!(precedence_set.len(), 0);
		// Compute the latest start time of the tasks in precedence_set
		let task_i_est = self.earliest_start_time(ctx, task_no);

		// Explain the reason why task i must be scheduled after a certain time
		// bound
		let mut clause = Vec::new();
		let (bv, _) =
			self.start_times[task_no].lit_relaxed(ctx, IntLitMeaning::GreaterEq(task_i_est));
		clause.push(bv);
		for j in precedence_set {
			let v = self.start_times[j].clone();
			// (1) explain the reason why all tasks in precedence_set will stay in
			// precedence_set
			let (bv, _) = v.lit_relaxed(ctx, IntLitMeaning::GreaterEq(earliest_start));
			clause.push(bv);
			// (2) explain the reason why the earliest start time of task i is set to
			// earliest completeion time of the precedence set
			let (bv, _) = v.lit_relaxed(
				ctx,
				IntLitMeaning::Less(task_i_est + self.durations[task_no]),
			);
			clause.push(bv);
		}
		clause
	}

	/// Return the (current) latest completion time of task `i`.
	fn latest_completion_time<Ctx>(&self, ctx: &mut Ctx, i: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.latest_start_time(ctx, i) + self.durations[i]
	}

	/// Return the (current) latest start time of task `i`.
	fn latest_start_time<Ctx>(&self, ctx: &mut Ctx, i: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.start_times[i].max(ctx)
	}

	/// Create a new [`DisjunctiveStrict`] propagator and post it in the solver.
	pub(crate) fn new<E>(
		solver: &mut E,
		start_times: Vec<I>,
		durations: Vec<IntVal>,
		edge_finding_enabled: bool,
		not_last_enabled: bool,
		detectable_precedence_enabled: bool,
	) -> Self
	where
		E: ConstructionActions + ?Sized,
	{
		let n = start_times.len();
		let trailed_info = (0..n)
			.map(|_| TaskInfo {
				earliest_start: solver.new_trailed(0),
				latest_completion: solver.new_trailed(0),
			})
			.collect();
		Self {
			start_times,
			durations,
			ot_tree: OmegaThetaTree::new(n),
			trailed_info,
			edge_finding_enabled,
			not_last_enabled,
			detectable_precedence_enabled,
			tasks_sorted_by_earliest_start: (0..n).collect_vec(),
			tasks_sorted_by_latest_start: (0..n).collect_vec(),
			tasks_sorted_by_earliest_completion: (0..n).collect_vec(),
			tasks_sorted_by_latest_completion: (0..n).collect_vec(),
		}
	}

	/// Create a new [`Disjunctive`] propagator and post it in the solver.
	pub fn post<E>(
		solver: &mut E,
		start_times: Vec<I>,
		durations: Vec<IntVal>,
		edge_finding_enabled: bool,
		not_last_enabled: bool,
		detectable_precedence_enabled: bool,
	) where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		let b = Box::new(Self::new(
			solver,
			start_times,
			durations,
			edge_finding_enabled,
			not_last_enabled,
			detectable_precedence_enabled,
		));
		solver.add_propagator(b);
	}

	/// Detectable precedence updates the lower bound of each task's earliest
	/// start time based on the earliest completion time of its detectable
	/// predecessors.
	///
	/// For each task `i`, define the set of detectable predecessors:
	///
	/// DPrec(T, i) = { j ∈ T | est_i + p_i > lct_j - p_j, j ≠ i }
	///
	/// The earliest start time of `i` is updated as:
	///
	/// est_i := max(est_i, ect_{DPrec(T, i)})
	///
	/// The algorithm processes tasks in order of increasing earliest completion
	/// time. For each task, it incrementally builds a set
	/// DPrec'(T, i) = { j ∈ T | est_i + p_i > lct_j - p_j }.
	/// All tasks with earliest completion time less than the current task's
	/// latest start time are added to the Omega-Theta tree. To update est_i,
	/// the algorithm temporarily removes `i` from the tree, then sets est_i to
	/// the earliest completion time of the tasks in the tree if this is
	/// greater than the current est_i. The task is then added back to the
	/// tree.
	fn propagate_detectable_precedence<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut propagated = false;
		// Clear the Omega-Theta tree
		self.ot_tree.clear();
		// Store the updated earliest start time of each task
		let mut updated_est = (0..self.start_times.len())
			.map(|i| self.earliest_start_time(ctx, i))
			.collect_vec();
		// Store the task which push the earliest start time in the tree
		let mut binding_tasks = vec![None; self.start_times.len()];

		// Initialize a queue of all tasks sorted by their latest start time
		let latest_start_times = (0..self.start_times.len())
			.map(|i| self.latest_start_time(ctx, i))
			.collect_vec();
		let earliest_completion_times = (0..self.start_times.len())
			.map(|i| self.earliest_completion_time(ctx, i))
			.collect_vec();

		self.tasks_sorted_by_latest_start
			.sort_by_key(|&i| latest_start_times[i]);
		self.tasks_sorted_by_earliest_completion
			.sort_by_key(|&i| earliest_completion_times[i]);

		// Initialize the placeholer for the index of the front task in the queue
		let mut lst_front_idx = 0;
		// Traverse all tasks by their earliest completion time non-decreasingly
		for &ect_task in self.tasks_sorted_by_earliest_completion.iter() {
			let ect = earliest_completion_times[ect_task];
			while lst_front_idx < self.tasks_sorted_by_latest_start.len()
				&& ect > latest_start_times[self.tasks_sorted_by_latest_start[lst_front_idx]]
			{
				let front_task = self.tasks_sorted_by_latest_start[lst_front_idx];
				// the latest start time of the front task is smaller than the earliest
				// completion of the current task, `front_task` << `ect_task` detected
				self.ot_tree.add_task(
					front_task,
					self.earliest_start_time(ctx, front_task),
					self.durations[front_task],
				);
				trace!(
					successor = ect_task,
					predecessor = front_task,
					"precedence detected",
				);
				lst_front_idx += 1;
			}

			// temporarily remove task `ect_task` from the tree
			let task_exists = self.ot_tree.remove_task(ect_task);

			// Check if the earliest completion time of tasks in the tree is greater
			// than the earliest completion time of task `ect_task`
			let tasks_in_tree_ect = self.ot_tree.root().earliest_completion;
			if tasks_in_tree_ect > self.earliest_start_time(ctx, ect_task) {
				binding_tasks[ect_task] = Some(self.ot_tree.binding_task(tasks_in_tree_ect, 0));
				updated_est[ect_task] = updated_est[ect_task].max(tasks_in_tree_ect);
				trace!(
					ect_task,
					updated_est = updated_est[ect_task],
					tasks_in_tree =? (0..lst_front_idx)
						.map(|i| self.tasks_sorted_by_latest_start[i])
						.filter(|&task_no| task_no != ect_task)
						.map(|task_no| {
							(
								task_no,
								latest_start_times[task_no],
							)
						})
						.collect_vec(),
					tasks_in_tree_ect,
					"propagate detected precedence"
				);
			}
			// add task `ect_task` back to the tree
			if task_exists {
				self.ot_tree.add_task(
					ect_task,
					self.earliest_start_time(ctx, ect_task),
					self.durations[ect_task],
				);
			}
		}

		// Update the earliest start time for each task
		for (i, v) in self.start_times.iter().enumerate() {
			if let Some(binding_task) = binding_tasks[i] {
				let earliest_start_time = self.earliest_start_time(ctx, i);
				let earliest_completion_time = self.earliest_completion_time(ctx, i);
				if updated_est[i] > earliest_start_time {
					let lb = self.start_times[binding_task].min(ctx);
					ctx.set_trailed(self.trailed_info[i].earliest_start, lb);
					ctx.set_trailed(
						self.trailed_info[i].latest_completion,
						earliest_completion_time,
					);
					let data = self.data_for_explanation(i, DisjunctivePropagationRule::Precedence);
					v.tighten_min(ctx, updated_est[i], ctx.deferred_reason(data))?;
					propagated = true;
				}
			}
		}
		trace!(propagated, "detectable precedence propagation completed");
		Ok(propagated)
	}

	/// Edge finding propagation rule checks if a task must be scheduled after a
	/// set of tasks.
	///
	/// For a set $Ω \subseteq T$ and a task $i \in (T \setminus Ω)$, task $i$
	/// must be scheduled after $Ω$ if:
	///
	/// $ect_{Ω \cup \{i\}} > lct_Ω$
	///
	/// In this case, update the earliest start time of $i$:
	///
	/// $est_i := \max(est_i, ect_Ω)$
	///
	/// When the resource is not overloaded for $Ω \cup \{i\}$, it suffices to
	/// consider the left cut $LCut(T, j) = \{k \in T \mid lct_k \leq lct_j\}$.
	/// For all $i \in T \setminus LCut(T, j)$, if $ect_{LCut(T, j) \cup \{i\}}
	/// > lct_j$, then $est_i := \max(est_i, ect_{LCut(T, j)})$.
	///
	/// The algorithm maintains $LCut(T, j)$ using the Omega-Theta tree,
	/// iterating tasks in decreasing order of latest completion time.
	/// At each step, resource overload is checked for the current set.
	/// If not overloaded, the current task is annotated as gray in the tree.
	/// The Omega-Theta tree maintains the gray earliest completion time:
	///
	/// $\bar{ect}(Ω, Ѳ) = \max(\{ect_Ω\} \cup \{ect_{Ω \cup \{i\}} \mid i \in
	/// Ѳ\})$
	///
	/// If $\bar{ect}(Ω, Ѳ) > lct_j$, there exists a gray task $i$ such that
	/// $ect_{LCut(T, j) \cup \{i\}} > lct_j$, and $est_i$ is updated
	/// accordingly. As $est_i$ cannot be further updated, $i$ is removed from
	/// $Ѳ$ in the tree. For more details of the algorithm, refer to the
	/// original paper by Vilim (2008).
	fn propagate_edge_finding<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		check_overload: bool,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut propagated = false;
		// Add all tasks to the Omega-Theta tree
		let earliest_start: Vec<_> = self.start_times.iter().map(|v| v.min(ctx)).collect();
		self.ot_tree
			.fill(earliest_start.as_slice(), self.durations.as_slice());

		// Sort the tasks by non-increasing latest completion time
		let latest_completion_times: Vec<_> = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(ctx, i))
			.collect();
		self.tasks_sorted_by_latest_completion
			.sort_by_key(|&i| -latest_completion_times[i]);

		// Traverse all tasks ordered by latest completion time and check the edge
		// finding propagation rule
		//
		// Invariant:
		//
		//   1. all non-gray tasks of `ot_tree` (Ω) forms LCut(j) = { i | lct_i ≤ lct_j
		//      }
		//   2. all gray tasks of `ot_tree` (Ѳ) are in the set T \setminus LCut(j)
		for (j, &lct_task) in self.tasks_sorted_by_latest_completion.iter().enumerate() {
			let lct = self.latest_completion_time(ctx, lct_task);
			// Assume that resource overload is not detected, i.e., ect(LCut(j)) <=
			// lct_j
			let ect_in_tree = self.ot_tree.root().earliest_completion;
			if check_overload {
				// Checking resource overload for LCut(j): ect(LCut(j)) > lct_j =>
				// conflict
				if ect_in_tree > lct {
					// Resource overload detected, eagerly build the reason clause for
					// conflict
					let expl = self.explain_overload_checking(lct + 1);
					self.start_times[lct_task].tighten_min(
						ctx,
						ect_in_tree - self.durations[lct_task],
						expl,
					)?;
				}
			} else {
				assert!(ect_in_tree <= lct);
			}

			// Checking the edge finding propagation rule
			while j > 0 && self.ot_tree.root().earliest_completion_gray > lct {
				let ect_gray_in_tree = self.ot_tree.root().earliest_completion_gray;
				let blocked_task = self.ot_tree.blocked_task(ect_gray_in_tree);
				if self.start_times[blocked_task].min(ctx) < ect_in_tree {
					let gray_est_task = self.ot_tree.blocking_task(ect_gray_in_tree);
					let lb = self.start_times[gray_est_task].min(ctx);
					// set trailed integer for lazy explanation
					ctx.set_trailed(self.trailed_info[blocked_task].earliest_start, lb);
					ctx.set_trailed(
						self.trailed_info[blocked_task].latest_completion,
						ect_gray_in_tree - 1,
					);
					trace!(
						ect_in_tree,
						task = blocked_task,
						window =? (lb, ect_gray_in_tree - 1),
						"propagate edge finding"
					);
					let data = self.data_for_explanation(
						blocked_task,
						DisjunctivePropagationRule::EdgeFinding,
					);
					self.start_times[blocked_task].tighten_min(
						ctx,
						ect_in_tree,
						ctx.deferred_reason(data),
					)?;
					propagated = true;
				}
				// Remove the blocked task as the maximum propagation has been achieved
				// by LCut(j) where lct_j is maximum
				self.ot_tree.remove_task(blocked_task);
			}
			self.ot_tree.annotate_gray_task(lct_task);
		}
		trace!(propagated, "edge finding propagation completed");
		Ok(propagated)
	}

	/// Not-Last propagation rule checks if a task cannot be the last scheduled
	/// among a set.
	///
	/// For a set $Ω \subseteq T$ and a task $i \in (T \setminus Ω)$, task $i$
	/// cannot be the last if:
	///
	/// $est_Ω + p_Ω > lst_i - p_i$
	///
	/// In this case, at least one $j \in Ω$ must be scheduled after $i$, so
	/// update:
	///
	/// $lct_i := \min \{ lct_i, \max \{ lst_j \mid j \in Ω \} \}$
	///
	/// For each $i$, it suffices to check the set:
	///
	/// $NLset(T, i) = \{ j \in T \mid lst_j < lct_i,\, j \neq i \}$
	///
	/// The algorithm iterates tasks in order of increasing latest completion
	/// time, incrementally building
	///
	/// $NLset'(T, i) = \{ j \in T \mid lst_j < lct_i \}$.
	///
	/// At each step, all tasks with latest start time less than the current
	/// task's latest completion time are added to the Omega-Theta tree. To
	/// update $lct_i$, the algorithm temporarily removes $i$ from the tree,
	/// then sets $lct_i$ to the maximum latest start time in the tree if this
	/// is less than $lct_i$. The task $i$ is then added back to the tree.
	fn propagate_not_last<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut propagated = false;
		// Clear the Omega-Theta tree
		self.ot_tree.clear();

		// Store the updated latest completion time of each task
		let mut updated_lct = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(ctx, i))
			.collect_vec();
		// Store the task which push the earliest start time in the tree
		let mut binding_tasks = vec![None; self.start_times.len()];

		// Initialize a queue of all tasks sorted by their latest start time
		let latest_start_times = (0..self.start_times.len())
			.map(|i| self.latest_start_time(ctx, i))
			.collect_vec();
		let latest_completion_times = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(ctx, i))
			.collect_vec();
		self.tasks_sorted_by_latest_start
			.sort_by_key(|&i| latest_start_times[i]);
		self.tasks_sorted_by_latest_completion
			.sort_by_key(|&i| latest_completion_times[i]);

		// Initialize the placeholer for the front task in the queue
		let mut lst_front_idx = 0;
		// Traverse all tasks by their latest completion time non-decreasingly
		for &lct_task in self.tasks_sorted_by_latest_completion.iter() {
			let lct = latest_completion_times[lct_task];
			// Add all tasks with latest start time less than lct to the Omega-Theta
			// tree
			while lst_front_idx < self.tasks_sorted_by_latest_start.len()
				&& lct > latest_start_times[self.tasks_sorted_by_latest_start[lst_front_idx]]
			{
				let lst_task = self.tasks_sorted_by_latest_start[lst_front_idx];
				self.ot_tree.add_task(
					lst_task,
					self.earliest_start_time(ctx, lst_task),
					self.durations[lst_task],
				);
				lst_front_idx += 1;
			}

			// temporarily remove task `ect_task` from the tree
			let task_exists = self.ot_tree.remove_task(lct_task);

			// Check if the earliest completion time of tasks in the tree is greater
			// than the earliest completion time of task `ect_task`
			let tasks_in_tree_ect = self.ot_tree.root().earliest_completion;
			if tasks_in_tree_ect > (lct - self.durations[lct_task]) {
				binding_tasks[lct_task] = Some(self.ot_tree.binding_task(tasks_in_tree_ect, 0));
				let front_lst =
					latest_start_times[self.tasks_sorted_by_latest_start[lst_front_idx - 1]];
				updated_lct[lct_task] = updated_lct[lct_task].min(front_lst);
				trace!(
					lct_task=? (lct_task, lct),
					updated_lct = updated_lct[lct_task],
					lst_front_idx,
					tasks_in_tree =? (0..lst_front_idx)
						.map(|i| self.tasks_sorted_by_latest_start[i])
						.filter(|&task_no| task_no != lct_task)
						.map(|task_no| {
							(
								task_no,
								latest_start_times[task_no],
							)
						})
						.collect_vec(),
					tasks_in_tree_ect,
					"propagate not last"
				);
			}
			// add task `ect_task` back to the tree
			if task_exists {
				self.ot_tree.add_task(
					lct_task,
					self.earliest_start_time(ctx, lct_task),
					self.durations[lct_task],
				);
			}
		}

		// Update the latest completion time for each task
		for (i, v) in self.start_times.iter().enumerate() {
			if let Some(binding_task) = binding_tasks[i]
				&& updated_lct[i] < self.latest_completion_time(ctx, i)
			{
				let lb = self.earliest_start_time(ctx, binding_task);
				trace!(
					task = i,
					window =? (lb, updated_lct[i]),
					"not last propagation"
				);
				ctx.set_trailed(self.trailed_info[i].earliest_start, lb);

				ctx.set_trailed(self.trailed_info[i].latest_completion, updated_lct[i]);
				let data = self.data_for_explanation(i, DisjunctivePropagationRule::NotLast);
				v.tighten_max(
					ctx,
					updated_lct[i] - self.durations[i],
					ctx.deferred_reason(data),
				)?;
				propagated = true;
			}
		}
		trace!(propagated, "not last propagation completed");
		Ok(propagated)
	}

	/// Overload checking detects if the total duration of any set of tasks
	/// cannot fit within their available time window, indicating a resource
	/// overload.
	///
	/// For all subsets Ω of tasks:
	///
	/// est_Ω + p_Ω > lct_Ω ⇒ conflict (resource overload)
	///
	/// It is sufficient to check the "left cut" for each task j:
	///
	/// LCut(T, j) = { k ∈ T | lct_k ≤ lct_j }
	///
	/// If est_{LCut(T, j)} + p_{LCut(T, j)} > lct_{LCut(T, j)}, then conflict.
	///
	/// The algorithm processes tasks in order of increasing latest completion
	/// time. For each task, it adds the task to the Omega-Theta tree, which
	/// maintains the set of tasks with latest completion times up to the
	/// current one (the left cut). If the tree's earliest completion time
	/// exceeds the current task's latest completion time, a resource overload
	/// is detected and a conflict is triggered.
	fn propagate_overload_checking<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		// Clear the Omega-Theta tree before propagation
		self.ot_tree.clear();

		// Sort the tasks by non-decreasing latest completion time
		let tasks_sorted_by_lct = (0..self.start_times.len())
			.map(|i| (i, self.latest_completion_time(ctx, i)))
			.sorted_by_key(|(_, lct)| *lct)
			.collect_vec();

		// Traverse all tasks ordered by latest completion time and check resource
		// overload
		for (i, lct_i) in tasks_sorted_by_lct.iter() {
			let est_i = self.earliest_start_time(ctx, *i);
			self.ot_tree.add_task(*i, est_i, self.durations[*i]);
			let ect = self.ot_tree.root().earliest_completion;
			if ect > *lct_i {
				let binding_task = self
					.ot_tree
					.binding_task(self.ot_tree.root().earliest_completion, 0);
				let earliest_start = self.start_times[binding_task].min(ctx);
				let expl = self.explain_overload_checking(lct_i + 1);
				trace!(
					time_window =? (earliest_start, lct_i),
					"Resource overload"
				);
				self.start_times[*i].tighten_min(ctx, ect - self.durations[*i], expl)?;
			}
		}
		Ok(())
	}

	/// Return the propagation rule from the data stored for explanation.
	fn propagation_rule_from_data(&self, data: u64) -> DisjunctivePropagationRule {
		match data >> 62 {
			0 => DisjunctivePropagationRule::EdgeFinding,
			1 => DisjunctivePropagationRule::NotLast,
			2 => DisjunctivePropagationRule::Precedence,
			_ => unreachable!("Invalid propagation rule in data"),
		}
	}

	/// Return the task number from the data stored for explanation.
	fn task_no_from_data(&self, data: u64) -> usize {
		((data << 2) >> 2) as usize
	}
}

impl<E, I> Propagator<E> for DisjunctivePropagator<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	/// Explain the propagation of the disjunctive propagator.
	#[tracing::instrument(name = "disjunctive_strict", level = "trace", skip(self, ctx))]
	fn explain(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		_: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		// Extract the task number and propagation rule from the data
		let task_no = self.task_no_from_data(data);
		let earliest_start = ctx.trailed(self.trailed_info[task_no].earliest_start);
		let latest_completion = ctx.trailed(self.trailed_info[task_no].latest_completion);

		// Explain the reason based on the propagation rule of disjunctive.
		match self.propagation_rule_from_data(data) {
			DisjunctivePropagationRule::EdgeFinding => {
				self.explain_edge_finding(ctx, task_no, earliest_start, latest_completion)
			}
			DisjunctivePropagationRule::NotLast => {
				self.explain_not_last(ctx, task_no, earliest_start, latest_completion)
			}
			DisjunctivePropagationRule::Precedence => {
				self.explain_precedence(ctx, task_no, earliest_start, latest_completion)
			}
		}
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in &self.start_times {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	/// Propagate the disjunctive propagator.
	#[tracing::instrument(name = "disjunctive_strict", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// Sort the tasks by earliest start time and initialize the Omega-Theta tree
		// according to the property of the Omega-Theta tree.
		let earliest_start: Vec<_> = self.start_times.iter().map(|v| v.min(ctx)).collect();
		self.tasks_sorted_by_earliest_start
			.sort_by_key(|&i| earliest_start[i]);
		self.ot_tree
			.initialize(self.tasks_sorted_by_earliest_start.as_slice());

		// Propagate edge finding propagation rule with overload checking or perform
		// overload checking only
		if self.edge_finding_enabled {
			if self.propagate_edge_finding(ctx, true)? {
				return Ok(());
			}
		} else {
			self.propagate_overload_checking(ctx)?;
		}
		// Propagate detectable precedence propagation rule
		if self.detectable_precedence_enabled && self.propagate_detectable_precedence(ctx)? {
			return Ok(());
		}
		// Propagate not-last propagation rule
		if self.not_last_enabled && self.propagate_not_last(ctx)? {
			return Ok(());
		}
		Ok(())
	}
}

impl OmegaThetaTree {
	/// Add a task with number `task_no` to the tree.
	fn add_task(&mut self, task_no: usize, earliest_start_time: i64, duration: i64) {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		self.nodes[idx].total_durations = duration;
		self.nodes[idx].earliest_completion = earliest_start_time + duration;
		self.nodes[idx].total_durations_gray = duration;
		self.nodes[idx].earliest_completion_gray = earliest_start_time + duration;
		self.recursive_update(idx);
	}

	/// Annotate task with number `task_no` as gray, and update its ancestors.
	fn annotate_gray_task(&mut self, task_no: usize) {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i64::MIN;
		self.recursive_update(idx);
	}

	/// Find the task responsible for pushing the earliest completion time of
	/// node with index `idx` beyond the `time_bound`
	fn binding_task(&self, time_bound: i64, idx: usize) -> usize {
		assert!(self.root().earliest_completion >= time_bound);
		let mut node_id = idx;
		let mut earliest_completion_time = time_bound;
		while node_id < self.leaves_start_idx {
			if self.nodes[Self::right_child(node_id)].earliest_completion
				>= earliest_completion_time
			{
				node_id = Self::right_child(node_id);
			} else {
				earliest_completion_time -= self.nodes[Self::right_child(node_id)].total_durations;
				node_id = Self::left_child(node_id);
			}
		}
		self.task_no[node_id - self.leaves_start_idx]
	}

	/// Find the gray task, blocked by tasks in the tree, whose earliest start
	/// time (EST) needs to be updated.
	fn blocked_task(&self, time_bound: i64) -> usize {
		assert!(self.root().earliest_completion <= time_bound);
		assert!(self.root().earliest_completion_gray >= time_bound);
		let mut node_id = 0;
		let mut earliest_completion_time = time_bound;
		while node_id < self.leaves_start_idx {
			if self.nodes[Self::left_child(node_id)].total_durations_gray == 0 {
				node_id = Self::right_child(node_id);
			} else if self.nodes[Self::right_child(node_id)].total_durations_gray == 0 {
				node_id = Self::left_child(node_id);
			} else if self.nodes[Self::right_child(node_id)].earliest_completion_gray
				>= earliest_completion_time
			{
				node_id = Self::right_child(node_id);
			} else if self.nodes[Self::left_child(node_id)].earliest_completion
				+ self.nodes[Self::right_child(node_id)].total_durations_gray
				>= earliest_completion_time
			{
				// The binding task is to the left, blocked task contributes only to the
				// sum
				earliest_completion_time -=
					self.nodes[Self::left_child(node_id)].earliest_completion;
				node_id = Self::right_child(node_id);
				while node_id < self.leaves_start_idx {
					if self.nodes[Self::left_child(node_id)].total_durations_gray
						+ self.nodes[Self::right_child(node_id)].total_durations
						== earliest_completion_time
					{
						earliest_completion_time -=
							self.nodes[Self::right_child(node_id)].total_durations;
						node_id = Self::left_child(node_id);
					} else if self.nodes[Self::left_child(node_id)].total_durations
						+ self.nodes[Self::right_child(node_id)].total_durations_gray
						>= earliest_completion_time
					{
						earliest_completion_time -=
							self.nodes[Self::left_child(node_id)].total_durations;
						node_id = Self::right_child(node_id);
					} else {
						unreachable!("unexpected case");
					}
				}
				break;
			} else {
				earliest_completion_time -= self.nodes[Self::right_child(node_id)].total_durations;
				node_id = Self::left_child(node_id);
			}
		}
		self.task_no[node_id - self.leaves_start_idx]
	}

	/// Find the task responsible for pushing the gray task’s earliest
	/// completion time (ECT), i.e., ECT(Ω ∪ i) > time_bound.
	fn blocking_task(&self, time_bound: i64) -> usize {
		assert!(self.root().earliest_completion <= time_bound);
		assert!(self.root().earliest_completion_gray >= time_bound);
		let mut node_id = 0;
		let mut earliest_completion_time = time_bound;
		while node_id < self.leaves_start_idx {
			let left_child = Self::left_child(node_id);
			let right_child = Self::right_child(node_id);
			if self.nodes[right_child].earliest_completion_gray >= earliest_completion_time {
				node_id = right_child;
			} else if self.nodes[left_child].earliest_completion
				+ self.nodes[right_child].total_durations_gray
				>= earliest_completion_time
			{
				return self.binding_task(
					earliest_completion_time - self.nodes[right_child].total_durations_gray,
					left_child,
				);
			} else {
				earliest_completion_time -= self.nodes[right_child].total_durations;
				node_id = left_child;
			}
		}
		self.task_no[node_id - self.leaves_start_idx]
	}

	/// Clear the tree and reset the earliest completion time.
	fn clear(&mut self) {
		for i in 0..self.nodes.len() {
			self.nodes[i].total_durations = 0;
			self.nodes[i].earliest_completion = i64::MIN;
			self.nodes[i].total_durations_gray = 0;
			self.nodes[i].earliest_completion_gray = i64::MIN;
		}
	}

	/// Fill the tree with task are sorted by earliest start time.
	fn fill(&mut self, earliest_start: &[i64], durations: &[i64]) {
		assert_eq!(earliest_start.len(), self.task_no.len());
		for i in 0..self.task_no.len() {
			let idx = self.node_index(i);
			let ect = earliest_start[i] + durations[i];
			self.nodes[idx].total_durations = durations[i];
			self.nodes[idx].earliest_completion = ect;
			self.nodes[idx].total_durations_gray = durations[i];
			self.nodes[idx].earliest_completion_gray = ect;
		}

		// update internal nodes in a bottom-up manner
		for i in (0..self.leaves_start_idx).rev() {
			self.update_internal_node(i);
		}
	}

	/// Initialize the tree to update the node index mapping by sorting the
	/// tasks with their earliest start time
	fn initialize(&mut self, task_sorted_by_earliest_start: &[usize]) {
		self.task_no.copy_from_slice(task_sorted_by_earliest_start);
		for i in 0..self.task_no.len() {
			self.node_index_offset[self.task_no[i]] = i;
		}
	}

	/// Calculate the index of the left child of a node `i`
	fn left_child(i: usize) -> usize {
		(i << 1) + 1
	}

	/// Create a new OmegaThetaTree with `tasks_no` tasks.
	pub(crate) fn new(tasks_no: usize) -> Self {
		let tree_size = (1 << (33 - (tasks_no as i32 - 1).leading_zeros())) - 1;
		OmegaThetaTree {
			nodes: vec![
				OmegaThetaTreeNode {
					total_durations: 0,
					earliest_completion: i64::MIN,
					total_durations_gray: 0,
					earliest_completion_gray: i64::MIN,
				};
				tree_size
			],
			leaves_start_idx: tree_size / 2,
			node_index_offset: (0..tasks_no).collect(),
			task_no: (0..tasks_no).collect(),
		}
	}

	/// Get the node index of a task with number `i` in the tree.
	fn node_index(&self, i: usize) -> usize {
		assert!(i < self.task_no.len());
		self.leaves_start_idx + self.node_index_offset[i]
	}

	/// Calculate the index of the parent of a node with index `i`
	fn parent(i: usize) -> usize {
		debug_assert_ne!(i, 0);
		(i - 1) >> 1
	}

	/// Update the node with index `i` and trigger the update of its parent
	/// recursively.
	fn recursive_update(&mut self, i: usize) {
		if i == 0 {
			return;
		}
		let parent = Self::parent(i);
		self.update_internal_node(parent);
		self.recursive_update(parent);
	}

	/// Remove the task with number `task_no` from the tree.
	fn remove_task(&mut self, task_no: usize) -> bool {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		if self.nodes[idx].total_durations == 0 && self.nodes[idx].total_durations_gray == 0 {
			// task already removed
			false
		} else {
			// reset the node and update the tree
			self.nodes[idx].total_durations = 0;
			self.nodes[idx].earliest_completion = i64::MIN;
			self.nodes[idx].total_durations_gray = 0;
			self.nodes[idx].earliest_completion_gray = i64::MIN;
			self.recursive_update(idx);
			true
		}
	}

	/// Calculate the index of the right child of a node `i`
	fn right_child(i: usize) -> usize {
		(i << 1) + 2
	}

	/// Return the root node of the tree.
	fn root(&self) -> &OmegaThetaTreeNode {
		&self.nodes[0]
	}

	/// Update the internal node `i` based on its children.
	fn update_internal_node(&mut self, i: usize) {
		let left_child = Self::left_child(i);
		let right_child = Self::right_child(i);
		let left_total_durations = self.nodes[left_child].total_durations;
		let right_total_durations = self.nodes[right_child].total_durations;
		let left_total_durations_gray = self.nodes[left_child].total_durations_gray;
		let right_total_durations_gray = self.nodes[right_child].total_durations_gray;
		let left_earliest_completion = self.nodes[left_child].earliest_completion;
		let right_earliest_completion = self.nodes[right_child].earliest_completion;
		let left_earliest_completion_gray = self.nodes[left_child].earliest_completion_gray;
		let right_earliest_completion_gray = self.nodes[right_child].earliest_completion_gray;

		self.nodes[i].total_durations = left_total_durations + right_total_durations;
		self.nodes[i].earliest_completion =
			right_earliest_completion.max(left_earliest_completion + right_total_durations);

		self.nodes[i].total_durations_gray = (left_total_durations_gray + right_total_durations)
			.max(left_total_durations + right_total_durations_gray);

		self.nodes[i].earliest_completion_gray = right_earliest_completion_gray.max(
			(left_earliest_completion + right_total_durations_gray)
				.max(left_earliest_completion_gray + right_total_durations),
		);
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::disjunctive::DisjunctivePropagator,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn test_disjunctive_strict_propagator() {
		for (edge_finding, not_last, detectable_precedence) in
			itertools::iproduct!([true, false], [true, false], [true, false])
		{
			let mut slv = Solver::default();
			let a = IntDecision::new_in(
				&mut slv,
				RangeList::from_iter([0..=4]),
				EncodingType::Eager,
				EncodingType::Lazy,
			);
			let b = IntDecision::new_in(
				&mut slv,
				RangeList::from_iter([0..=4]),
				EncodingType::Eager,
				EncodingType::Lazy,
			);
			let c = IntDecision::new_in(
				&mut slv,
				RangeList::from_iter([0..=4]),
				EncodingType::Eager,
				EncodingType::Lazy,
			);

			let durations = vec![2, 3, 1];
			DisjunctivePropagator::post(
				&mut slv,
				vec![a, b, c],
				durations.clone(),
				edge_finding,
				not_last,
				detectable_precedence,
			);
			DisjunctivePropagator::post(
				&mut slv,
				[a, b, c]
					.iter()
					.zip(durations.iter())
					.map(|(v, d)| -*v + (7 - d))
					.collect(),
				durations.clone(),
				edge_finding,
				not_last,
				detectable_precedence,
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
}
