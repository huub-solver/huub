//! Structures and algorithms for the `disjunctive_strict` constraint, which
//! enforces that no two tasks overlap from a list of tasks.

use itertools::Itertools;
use pindakaas::Lit as RawLit;
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
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, BoolView,
		BoolViewInner, IntLitMeaning, IntView,
	},
	Conjunction, IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `disjunctive_strict` constraint within a model.
///
/// This constraint enforces that the given a list of integer decision variables
/// representing the start times of tasks and a list of integer values
/// representing the durations of tasks, the tasks do not overlap in time.
pub struct DisjunctiveStrict {
	/// Start time variables of each task.
	pub(crate) start_times: Vec<IntDecision>,
	/// Durations of each task.
	pub(crate) durations: Vec<IntVal>,
	/// Whether to enable the edge finding propagator.
	///
	/// Defaults to `true`.
	pub(crate) edge_finding_prop: Option<bool>,
	/// Whether to enable the not last propagator.
	///
	/// Defaults to `false`.
	pub(crate) not_last_prop: Option<bool>,
	/// Whether to enable the detectable precedence propagator.
	///
	/// Defaults to `false`.
	pub(crate) detectable_precedence_prop: Option<bool>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum DisjunctivePropagationRule {
	/// The edge finding propagation rule.
	EdgeFinding,
	/// The not-last propagation rule.
	NotLast,
	/// The precedence propagation rule.
	Precedence,
}

impl From<u64> for DisjunctivePropagationRule {
	fn from(val: u64) -> Self {
		match val {
			0 => DisjunctivePropagationRule::EdgeFinding,
			1 => DisjunctivePropagationRule::NotLast,
			2 => DisjunctivePropagationRule::Precedence,
			_ => unreachable!("Invalid propagation rule"),
		}
	}
}

impl From<DisjunctivePropagationRule> for u64 {
	fn from(value: DisjunctivePropagationRule) -> Self {
		match value {
			DisjunctivePropagationRule::EdgeFinding => 0,
			DisjunctivePropagationRule::NotLast => 1,
			DisjunctivePropagationRule::Precedence => 2,
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `disjunctive_strict` constraint using the Overload Checking,
/// Edge Finding, Not-First/Not-Last, and Detectable Precedence algorithms.
pub struct DisjunctiveStrictPropagator {
	/// Start time variables of each task.
	start_times: Vec<IntView>,
	/// Durations of each task.
	durations: Vec<IntVal>,
	/// The Omega-Theta tree to compute the earliest completion time.
	ot_tree: OmegaThetaTree,
	/// Trailed earliest start and latest completion times to aid in explaination.
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
/// A binary tree structure that stores the total duration and earliest
/// completion time of tasks.
struct OmegaThetaTree {
	/// Storage of the nodes of the tree.
	nodes: Vec<OmegaThetaTreeNode>,
	/// Index of the first leaf node.
	leaves_start_idx: usize,
	/// Mapping of the task number to the tree node index (offset by `leaves_start_idx`).
	/// The tasks are sorted by their earliest start time in the tree.
	node_index_offset: Vec<usize>,
	/// Mapping of the tree node index (offset by `leaves_start_idx`)
	/// to the task number.
	task_no: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A node structure for the [`OmegaThetaTree`].
struct OmegaThetaTreeNode {
	/// Total duration of the tasks under the tree rooted at this node.
	total_durations: i64,
	/// Earliest completion time of the tasks under the tree rooted at this node.
	earliest_completion: i64,
	/// Total duration of the tasks under the tree rooted at this node, with at
	/// most one gray node.
	total_durations_gray: i64,
	/// Earliest completion time of the tasks under the tree rooted at this node,
	/// with at most one gray node.
	earliest_completion_gray: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Internal structure to store trailed information about tasks.
struct TaskInfo {
	/// Earliest start time of the task.
	earliest_start: TrailedInt,
	/// Latest completion time of the task.
	latest_completion: TrailedInt,
}

impl DisjunctiveStrict {
	/// Return whether the edge finding propagation will be used when
	/// creating a [`Solver`] object.
	pub fn edge_finding_propagation_enabled(&self) -> bool {
		self.edge_finding_prop.unwrap_or(true)
	}

	/// Ensure the use of the edge finding propagator when this constraint is
	/// posted to a [`Solver`] object.
	///
	/// Note that this method does not affect whether other propagators
	/// will be used or not.
	pub fn use_edge_finding_propagation(&mut self, enable: bool) {
		self.edge_finding_prop = Some(enable);
	}

	/// Return whether the not-last propagation will be used when
	/// creating a [`Solver`] object.
	pub fn not_last_propagation_enabled(&self) -> bool {
		self.not_last_prop.unwrap_or(false)
	}

	/// Ensure the use of the not-last propagator when this constraint is
	/// posted to a [`Solver`] object.
	///
	/// Note that this method does not affect whether other propagators
	/// will be used or not.
	pub fn use_not_last_propagation(&mut self, enable: bool) {
		self.not_last_prop = Some(enable);
	}

	/// Return whether the detectable precedence propagation will be used
	/// creating a [`Solver`] object.
	pub fn detectable_precedence_propagation_enabled(&self) -> bool {
		self.detectable_precedence_prop.unwrap_or(false)
	}

	/// Ensure the use of the detectable precedence propagator when this
	/// constraint is posted to a [`Solver`] object.
	///
	/// Note that this method does not affect whether other propagators
	/// will be used or not.
	pub fn use_detectable_precedence_propagation(&mut self, enable: bool) {
		self.detectable_precedence_prop = Some(enable);
	}
}

impl<S: SimplificationActions> Constraint<S> for DisjunctiveStrict {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// return TrivialUnsatisfiable if overload is detected
		let (earliest_start, latest_completion) =
			self.start_times.iter().zip(self.durations.iter()).fold(
				(IntVal::MAX, IntVal::MIN),
				|(earliest_start, latest_completion), (&start, &duration)| {
					(
						i64::min(
							earliest_start.min(actions.get_int_lower_bound(start)),
							earliest_start,
						),
						i64::max(
							latest_completion.max(actions.get_int_upper_bound(start) + duration),
							latest_completion,
						),
					)
				},
			);
		let total_duration = self.durations.iter().sum::<IntVal>();
		if earliest_start + total_duration > latest_completion {
			return Err(ReformulationError::TrivialUnsatisfiable);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let start_times = self
			.start_times
			.iter()
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		// Add symmetric version of start time for upper bound propagation
		let iter = start_times.iter().zip(self.durations.iter());
		let horizon = iter
			.clone()
			.map(|(v, d)| slv.get_int_upper_bound(*v) + d)
			.max()
			.unwrap();
		let symmetric_vars: Vec<IntView> = iter.map(|(v, d)| -*v + (horizon - d)).collect();

		// Add detectable precedence propagators
		DisjunctiveStrictPropagator::new_in(
			slv,
			start_times,
			self.durations.clone(),
			self.edge_finding_propagation_enabled(),
			self.not_last_propagation_enabled(),
			self.detectable_precedence_propagation_enabled(),
		);
		DisjunctiveStrictPropagator::new_in(
			slv,
			symmetric_vars,
			self.durations.clone(),
			self.edge_finding_propagation_enabled(),
			self.not_last_propagation_enabled(),
			self.detectable_precedence_propagation_enabled(),
		);

		Ok(())
	}
}

impl DisjunctiveStrictPropagator {
	#[inline]
	/// Return the (current) earliest start time of task `i`.
	fn earliest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> IntVal {
		actions.get_int_lower_bound(self.start_times[i])
	}

	#[inline]
	/// Return the (current) latest start time of task `i`.
	fn latest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> IntVal {
		actions.get_int_upper_bound(self.start_times[i])
	}

	#[inline]
	/// Return the (current) earliest completion time of task `i`.
	fn earliest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> IntVal {
		self.earliest_start_time(i, actions) + self.durations[i]
	}

	#[inline]
	/// Return the (current) latest completion time of task `i`.
	fn latest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> IntVal {
		self.latest_start_time(i, actions) + self.durations[i]
	}

	#[inline]
	/// Return the data stored for explanation from propagation rule and task number.
	fn data_for_explanation(
		&self,
		task_no: usize,
		propagation_rule: DisjunctivePropagationRule,
	) -> u64 {
		((propagation_rule as u64) << 62) + task_no as u64
	}

	#[inline]
	/// Return the task number from the data stored for explanation.
	fn task_no_from_data(&self, data: u64) -> usize {
		((data << 2) >> 2) as usize
	}

	#[inline]
	/// Return the propagation rule from the data stored for explanation.
	fn propagation_rule_from_data(&self, data: u64) -> DisjunctivePropagationRule {
		(data >> 62).into()
	}

	/// Propagate overload checking propagation rule
	fn propagate_overload_checking<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
		// Clear the Omega-Theta tree
		self.ot_tree.clear();
		// Sort the tasks by non-decreasing latest completion time
		let tasks_sorted_by_lct = (0..self.start_times.len())
			.map(|i| (i, self.latest_completion_time(i, actions)))
			.sorted_by_key(|(_, lct)| *lct)
			.collect_vec();
		// Traverse all tasks ordered by latest completion time and check the overload checking propagation rule
		for (i, lct) in tasks_sorted_by_lct.iter() {
			let est_i = self.earliest_start_time(*i, actions);
			self.ot_tree.add_task(*i, est_i, self.durations[*i]);
			let ect = self.ot_tree.root().earliest_completion;
			// Checking resource overload for LCut(i): ect(LCut(i)) > lct(LCut(j)) => failure
			if ect > *lct {
				// resource overload detected, eagerly build the reason clause for conflict
				let binding_task = self
					.ot_tree
					.binding_task(self.ot_tree.root().earliest_completion, 0);
				let earliest_start = actions.get_int_lower_bound(self.start_times[binding_task]);
				let expl = self.explain_overload_checking(lct + 1);
				trace!(
					time_window =? (earliest_start, lct),
					"Resource overload"
				);
				actions.set_int_lower_bound(
					self.start_times[*i],
					ect - self.durations[*i],
					expl,
				)?;
			}
		}
		Ok(())
	}

	/// Explain resource overload within the time window [`earliest_start`, `time_bound`]
	fn explain_overload_checking<A: ExplanationActions>(
		&self,
		time_bound: i64,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let binding_task = self.ot_tree.binding_task(time_bound, 0);
			let earliest_start = actions.get_int_lower_bound(self.start_times[binding_task]);
			let mut slack = time_bound - earliest_start;
			let mut e_tasks = Vec::new();

			trace!(
				window =? (earliest_start, time_bound),
				"Explain Resource Overload"
			);
			// collect sufficient energy within the window [lb, time_bound)
			for i in 0..self.start_times.len() {
				if self.earliest_start_time(i, actions) >= earliest_start
					&& self.latest_completion_time(i, actions) < time_bound
				{
					e_tasks.push(i);
					slack -= self.durations[i];
					if slack <= 0 {
						break;
					}
				}
			}

			e_tasks
				.iter()
				.flat_map(|&i| {
					let (bv, _) = actions.get_int_lit_relaxed(
						self.start_times[i],
						IntLitMeaning::Less((time_bound - slack) - self.durations[i]),
					);
					[actions.get_int_lower_bound_lit(self.start_times[i]), bv]
				})
				.collect_vec()
		}
	}

	/// Propagate detectable precedence propagation rule
	fn propagate_detectable_precedence<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<bool, Conflict> {
		let mut propagated = false;
		// Clear the Omega-Theta tree
		self.ot_tree.clear();
		// Store the updated earliest start time of each task
		let mut updated_est = (0..self.start_times.len())
			.map(|i| self.earliest_start_time(i, actions))
			.collect_vec();
		// Store the task which push the earliest start time in the tree
		let mut binding_tasks = vec![None; self.start_times.len()];

		// Initialize a queue of all tasks sorted by their latest start time
		let latest_start_times = (0..self.start_times.len())
			.map(|i| self.latest_start_time(i, actions))
			.collect_vec();
		let earliest_completion_times = (0..self.start_times.len())
			.map(|i| self.earliest_completion_time(i, actions))
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
				// the latest start time of the front task is smaller than
				// the earliest completion of the current task, `front_task` << `ect_task` detected
				self.ot_tree.add_task(
					front_task,
					self.earliest_start_time(front_task, actions),
					self.durations[front_task],
				);
				trace!(
					successor = ect_task,
					predecessor = front_task,
					"Detected precedence",
				);
				lst_front_idx += 1;
			}

			// temporarily remove task `ect_task` from the tree
			let task_exists = self.ot_tree.remove_task(ect_task);

			// Check if the earliest completion time of tasks in the tree
			// is greater than the earliest completion time of task `ect_task`
			let tasks_in_tree_ect = self.ot_tree.root().earliest_completion;
			if tasks_in_tree_ect > self.earliest_start_time(ect_task, actions) {
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
					"Detectable precedence propagate"
				);
			}
			// add task `ect_task` back to the tree
			if task_exists {
				self.ot_tree.add_task(
					ect_task,
					self.earliest_start_time(ect_task, actions),
					self.durations[ect_task],
				);
			}
		}

		// Update the earliest start time for each task
		for (i, &v) in self.start_times.iter().enumerate() {
			if let Some(binding_task) = binding_tasks[i] {
				let earliest_start_time = self.earliest_start_time(i, actions);
				let earliest_completion_time = self.earliest_completion_time(i, actions);
				if updated_est[i] > earliest_start_time {
					let lb = actions.get_int_lower_bound(self.start_times[binding_task]);
					let _ = actions.set_trailed_int(self.trailed_info[i].earliest_start, lb);
					let _ = actions.set_trailed_int(
						self.trailed_info[i].latest_completion,
						earliest_completion_time,
					);
					let data = self.data_for_explanation(i, DisjunctivePropagationRule::Precedence);
					actions.set_int_lower_bound(
						v,
						updated_est[i],
						actions.deferred_reason(data),
					)?;
					propagated = true;
				}
			}
		}
		trace!(propagated, "Detectable precedence propagation completed");
		Ok(propagated)
	}

	/// Explain precedence propagation for task `i` with the earliest start time
	fn explain_precedence<E: ExplanationActions>(
		&mut self,
		actions: &mut E,
		task_no: usize,
		earliest_start: i64,
		latest_start: i64,
	) -> Vec<BoolView> {
		// Collect all tasks of which the earliest start time greater than `earliest_start`
		let precedence_set = (0..self.start_times.len())
			.filter(|&j| {
				j != task_no
					&& self.earliest_start_time(j, actions) >= earliest_start
					&& self.latest_start_time(j, actions) < latest_start
			})
			.collect_vec();

		trace!(
			task_no,
			window =? (earliest_start, latest_start),
			precedence_set = ?precedence_set,
			"Explain Detectable Precedence"
		);

		assert_ne!(precedence_set.len(), 0);
		// Compute the latest start time of the tasks in precedence_set
		let task_i_est = self.earliest_start_time(task_no, actions);

		// Explain the reason why task i must be scheduled after a certain time bound
		let mut clause = Vec::new();
		let (bv, _) = actions.get_int_lit_relaxed(
			self.start_times[task_no],
			IntLitMeaning::GreaterEq(task_i_est),
		);
		clause.push(bv);
		for j in precedence_set {
			let v = self.start_times[j];
			// (1) explain the reason why all tasks in precedence_set will stay in precedence_set
			let (bv, _) = actions.get_int_lit_relaxed(v, IntLitMeaning::GreaterEq(earliest_start));
			clause.push(bv);
			// (2) explain the reason why the earliest start time of task i is set to earliest completeion time of the precedence set
			let (bv, _) = actions
				.get_int_lit_relaxed(v, IntLitMeaning::Less(task_i_est + self.durations[task_no]));
			clause.push(bv);
		}
		clause
	}

	/// Propagate not-last propagation rule
	fn propagate_not_last<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<bool, Conflict> {
		let mut propagated = false;
		// Clear the Omega-Theta tree
		self.ot_tree.clear();

		// Store the updated latest completion time of each task
		let mut updated_lct = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(i, actions))
			.collect_vec();
		// Store the task which push the earliest start time in the tree
		let mut binding_tasks = vec![None; self.start_times.len()];

		// Initialize a queue of all tasks sorted by their latest start time
		let latest_start_times = (0..self.start_times.len())
			.map(|i| self.latest_start_time(i, actions))
			.collect_vec();
		let latest_completion_times = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(i, actions))
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
			// Add all tasks with latest start time less than lct to the Omega-Theta tree
			while lst_front_idx < self.tasks_sorted_by_latest_start.len()
				&& lct > latest_start_times[self.tasks_sorted_by_latest_start[lst_front_idx]]
			{
				let lst_task = self.tasks_sorted_by_latest_start[lst_front_idx];
				self.ot_tree.add_task(
					lst_task,
					self.earliest_start_time(lst_task, actions),
					self.durations[lst_task],
				);
				lst_front_idx += 1;
			}

			// temporarily remove task `ect_task` from the tree
			let task_exists = self.ot_tree.remove_task(lct_task);

			// Check if the earliest completion time of tasks in the tree
			// is greater than the earliest completion time of task `ect_task`
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
					"Not Last propagate"
				);
			}
			// add task `ect_task` back to the tree
			if task_exists {
				self.ot_tree.add_task(
					lct_task,
					self.earliest_start_time(lct_task, actions),
					self.durations[lct_task],
				);
			}
		}

		// Update the latest completion time for each task
		for (i, &v) in self.start_times.iter().enumerate() {
			if let Some(binding_task) = binding_tasks[i] {
				if updated_lct[i] < self.latest_completion_time(i, actions) {
					let lb = self.earliest_start_time(binding_task, actions);
					trace!(
						task = i,
						window =? (lb, updated_lct[i]),
						"Not Last propagation"
					);
					let _ = actions.set_trailed_int(self.trailed_info[i].earliest_start, lb);
					let _ = actions
						.set_trailed_int(self.trailed_info[i].latest_completion, updated_lct[i]);
					let data = self.data_for_explanation(i, DisjunctivePropagationRule::NotLast);
					actions.set_int_upper_bound(
						v,
						updated_lct[i] - self.durations[i],
						actions.deferred_reason(data),
					)?;
					propagated = true;
				}
			}
		}
		trace!(propagated, "Not Last propagation completed");
		Ok(propagated)
	}

	/// Explain Not-Last propagation for task `i` with the
	/// time window [`earliest_start`, `updated_lct_i`]
	fn explain_not_last<E: ExplanationActions>(
		&mut self,
		actions: &mut E,
		task_no: usize,
		earliest_start: i64,
		updated_lct_i: i64,
	) -> Vec<BoolView> {
		// Collect the set of tasks in NLset(i) = { j | lst_j < lct_i && est_j + p_j ≥ earliest_start & j ≠ i }
		let nlset = (0..self.start_times.len())
			.filter(|j| {
				{
					*j != task_no
						&& self.latest_start_time(*j, actions) <= updated_lct_i
						&& self.earliest_start_time(*j, actions) >= earliest_start
				}
			})
			.collect_vec();

		trace!(
			task_no,
			window =? (earliest_start, updated_lct_i),
			nlset = ? nlset.iter().map(|&j| (j, self.durations[j], self.earliest_start_time(j, actions), self.latest_start_time(j, actions))).collect_vec(),
			"Explain Not Last"
		);

		assert_ne!(nlset.len(), 0);

		// Explain the reason why task i cannot be the last task
		let mut clause = Vec::new();
		clause.push(actions.get_int_upper_bound_lit(self.start_times[task_no]));
		for j in nlset {
			// explain the reason why all tasks in NLset(i) will stay in NLset(i)
			// (1) If for all j in NLset(i) [est_j ≥ earliest_start], then ect_{\Omega} > lst_i, and NLset(i) \not\prec i
			let (bv, _) = actions.get_int_lit_relaxed(
				self.start_times[j],
				IntLitMeaning::GreaterEq(earliest_start),
			);
			clause.push(bv);
			// (2) explain the reason why the latest completion time of task i is set to latest_completion
			// If for all j in NLset(i) [lst_j ≤ lct_i'], then max{lst_j, j \in \Omega} ≤ lct_i', and lct_i' should be set
			let (bv, _) = actions
				.get_int_lit_relaxed(self.start_times[j], IntLitMeaning::Less(updated_lct_i + 1));
			clause.push(bv);
		}
		clause
	}

	/// Propagate edge finding propagation rule and overload checking
	fn propagate_edge_finding<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		check_overload: bool,
	) -> Result<bool, Conflict> {
		let mut propagated = false;
		// Add all tasks to the Omega-Theta tree
		let earliest_start: Vec<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect();
		self.ot_tree
			.fill(earliest_start.as_slice(), self.durations.as_slice());

		// Sort the tasks by non-increasing latest completion time
		let latest_completion_times: Vec<_> = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(i, actions))
			.collect();
		self.tasks_sorted_by_latest_completion
			.sort_by_key(|&i| -latest_completion_times[i]);

		// Traverse all tasks ordered by latest completion time and check the edge finding propagation rule
		// Invariant: (1) all non-gray tasks in `ot_tree` forms LCut(j) = { i | lct_i ≤ lct_j }
		//            (2) all gray tasks in `ot_tree` are in the set T \setminus LCut(j)
		for (j, &lct_task) in self.tasks_sorted_by_latest_completion.iter().enumerate() {
			let lct = self.latest_completion_time(lct_task, actions);
			// Assume that resource overload is not detected, i.e., ect(LCut(j)) <= lct_j
			let ect_in_tree = self.ot_tree.root().earliest_completion;
			if check_overload {
				// Checking resource overload for LCut(j): ect(LCut(j)) > lct_j => failure
				if ect_in_tree > lct {
					// Resource overload detected, eagerly build the reason clause for conflict
					let expl = self.explain_overload_checking(lct + 1);
					actions.set_int_lower_bound(
						self.start_times[lct_task],
						ect_in_tree - self.durations[lct_task],
						expl,
					)?;
				}
			} else {
				assert!(ect_in_tree <= lct);
			}
			// Checking the edge finding propagation rule:
			// ∀ i \in T \setminus LCut(j), ect(LCut(j) ∪ i) > lct_j => LCut(j) << i
			while j > 0 && self.ot_tree.root().earliest_completion_gray > lct {
				let ect_gray_in_tree = self.ot_tree.root().earliest_completion_gray;
				let blocked_task = self.ot_tree.blocked_task(ect_gray_in_tree);
				if actions.get_int_lower_bound(self.start_times[blocked_task]) < ect_in_tree {
					let gray_est_task = self.ot_tree.blocking_task(ect_gray_in_tree);
					let lb = actions.get_int_lower_bound(self.start_times[gray_est_task]);
					// set trailed integer for lazy explanation
					let _ =
						actions.set_trailed_int(self.trailed_info[blocked_task].earliest_start, lb);
					let _ = actions.set_trailed_int(
						self.trailed_info[blocked_task].latest_completion,
						ect_gray_in_tree - 1,
					);
					trace!(
						ect_in_tree,
						task = blocked_task,
						window =? (lb, ect_gray_in_tree - 1),
						"Propagate Edge Finding"
					);
					let data = self.data_for_explanation(
						blocked_task,
						DisjunctivePropagationRule::EdgeFinding,
					);
					actions.set_int_lower_bound(
						self.start_times[blocked_task],
						ect_in_tree,
						actions.deferred_reason(data),
					)?;
					propagated = true;
				}
				// Remove the blocked task as the maximum propagation has been achieved by LCut(j) where lct_j is maximum
				let _ = self.ot_tree.remove_task(blocked_task);
			}
			self.ot_tree.annotate_gray_task(lct_task);
		}
		trace!(propagated, "Edge Finding propagation completed");
		Ok(propagated)
	}

	/// Explain edge finding propagation for task `i` with the
	/// time window [`earliest_start`, `latest_completion`]
	fn explain_edge_finding<E: ExplanationActions>(
		&mut self,
		actions: &mut E,
		task_no: usize,
		earliest_start: i64,
		latest_completion: i64,
	) -> Vec<BoolView> {
		// explain why the set of tasks LCut(j) ∪ {i} cannot be completed before lct_j
		// since energy of the set of tasks (including i) within the time window [earliest_start, latest_completion] is overloaded
		let latest_completion_times = (0..self.start_times.len())
			.map(|i| self.latest_completion_time(i, actions))
			.collect_vec();
		let earliest_start_times = (0..self.start_times.len())
			.map(|i| self.earliest_start_time(i, actions))
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
			"Explain Edge Finding"
		);
		// collect at least latest_completion - earliest_start energy (including durations[task_no])
		// from tasks bracketed in [earliest_start, latest_completion] and form a set O
		// [start(t) >= latest_completion + 1] because
		// [start(t) >= earliest_start] /\ forall (t' in O) [start(t') >= earliest_start] /\ forall (t' in O) [end(t') <= latest_completion]
		let mut clause = Vec::new();
		let (bv, _) = actions.get_int_lit_relaxed(
			self.start_times[task_no],
			IntLitMeaning::GreaterEq(earliest_start),
		);
		clause.push(bv);
		let mut energy = latest_completion - earliest_start - self.durations[task_no];
		for i in 0..self.start_times.len() {
			if i != task_no
				&& earliest_start_times[i] >= earliest_start
				&& latest_completion_times[i] <= latest_completion
			{
				clause.push(actions.get_int_lower_bound_lit(self.start_times[i]));
				let (bv, _) = actions.get_int_lit_relaxed(
					self.start_times[i],
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

	/// Create a new [`DisjunctiveStrict`] propagator and post it in
	/// the solver.
	pub fn new_in<P>(
		solver: &mut P,
		start_times: Vec<IntView>,
		durations: Vec<IntVal>,
		edge_finding_enabled: bool,
		not_last_enabled: bool,
		detectable_precedence_enabled: bool,
	) where
		P: PropagatorInitActions + ?Sized,
	{
		let n = start_times.len();
		let trailed_info = (0..n)
			.map(|_| TaskInfo {
				earliest_start: solver.new_trailed_int(0),
				latest_completion: solver.new_trailed_int(0),
			})
			.collect();
		let prop = solver.add_propagator(
			Box::new(Self {
				start_times: start_times.clone(),
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
			}),
			PriorityLevel::Low,
		);

		for v in start_times {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}
}

impl<P, E> Propagator<P, E> for DisjunctiveStrictPropagator
where
	P: PropagationActions,
	E: ExplanationActions,
{
	/// Explain lower bound propagation for edge finding
	/// `data` is a bit vector where the leftmost 2 bits indicate the
	/// propagation rule, the next 62 bits indicate the task number
	#[tracing::instrument(name = "disjunctive_strict", level = "trace", skip(self, actions))]
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, data: u64) -> Conjunction {
		// explain why the set of tasks LCut(j) ∪ {i} cannot be completed before lct_j
		// since energy of the set of tasks (including i) within the time window [earliest_start, latest_completion] is overloaded
		let task_no = self.task_no_from_data(data);
		let earliest_start = actions.get_trailed_int(self.trailed_info[task_no].earliest_start);
		let latest_completion =
			actions.get_trailed_int(self.trailed_info[task_no].latest_completion);

		// explain the reason based on the propagation rule of disjunctive
		let clause = match self.propagation_rule_from_data(data) {
			DisjunctivePropagationRule::EdgeFinding => {
				self.explain_edge_finding(actions, task_no, earliest_start, latest_completion)
			}
			DisjunctivePropagationRule::NotLast => {
				self.explain_not_last(actions, task_no, earliest_start, latest_completion)
			}
			DisjunctivePropagationRule::Precedence => {
				self.explain_precedence(actions, task_no, earliest_start, latest_completion)
			}
		};
		clause
			.iter()
			.filter_map(|bv| match bv.0 {
				BoolViewInner::Lit(l) => Some(l),
				BoolViewInner::Const(true) => None,
				BoolViewInner::Const(false) => {
					unreachable!(
						"Unexpected false literal in the explanation of disjunctive edge finding"
					)
				}
			})
			.collect()
	}

	#[tracing::instrument(name = "disjunctive_strict", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// Sort the tasks by earliest start time and initialize the Omega-Theta tree
		let earliest_start: Vec<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect();
		self.ot_tree.initialize(earliest_start.as_slice());

		// Propagate edge finding propagation rule with overload checking
		// or perform overload checking only
		if self.edge_finding_enabled {
			if self.propagate_edge_finding(actions, true)? {
				return Ok(());
			}
		} else {
			self.propagate_overload_checking(actions)?;
		}
		// Propagate detectable precedence propagation rule
		if self.detectable_precedence_enabled && self.propagate_detectable_precedence(actions)? {
			return Ok(());
		}
		// Propagate not-last propagation rule
		if self.not_last_enabled && self.propagate_not_last(actions)? {
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

	/// Find the task responsible for pushing the earliest completion time of node
	/// with index `idx` beyond the `time_bound`
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

	/// Find the gray task, blocked by tasks in the tree, whose earliest start time (EST) needs to be updated.
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
				// The binding task is to the left, blocked task contributes only to the sum
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

	/// Find the task responsible for pushing the gray task’s earliest completion time (ECT),
	/// i.e., ECT(Ω ∪ i) > time_bound.
	fn blocking_task(&self, time_bound: i64) -> usize {
		assert!(self.nodes[0].earliest_completion <= time_bound);
		assert!(self.nodes[0].earliest_completion_gray >= time_bound);
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

	/// Initialize the tree to update the node index mapping by sorting the tasks
	/// with their earliest start time
	fn initialize(&mut self, earliest_start_time: &[i64]) {
		self.task_no.sort_by_key(|&i| earliest_start_time[i]);
		for i in 0..self.task_no.len() {
			self.node_index_offset[self.task_no[i]] = i;
		}
	}

	#[inline]
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

	#[inline]
	/// Get the node index of a task with number `i` in the tree.
	fn node_index(&self, i: usize) -> usize {
		assert!(i < self.task_no.len());
		self.leaves_start_idx + self.node_index_offset[i]
	}

	#[inline]
	/// Calculate the index of the parent of a node with index `i`
	fn parent(i: usize) -> usize {
		debug_assert_ne!(i, 0);
		(i - 1) >> 1
	}

	/// Update the node with index `i` and trigger the update of its parent recursively.
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

	#[inline]
	/// Calculate the index of the right child of a node `i`
	fn right_child(i: usize) -> usize {
		(i << 1) + 2
	}

	#[inline]
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
		self.nodes[i].earliest_completion = i64::max(
			right_earliest_completion,
			left_earliest_completion + right_total_durations,
		);
		self.nodes[i].total_durations_gray = i64::max(
			left_total_durations_gray + right_total_durations,
			left_total_durations + right_total_durations_gray,
		);
		self.nodes[i].earliest_completion_gray = i64::max(
			right_earliest_completion_gray,
			i64::max(
				left_earliest_completion + right_total_durations_gray,
				left_earliest_completion_gray + right_total_durations,
			),
		);
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		constraints::disjunctive_strict::DisjunctiveStrictPropagator,
		solver::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_disjunctive_strict_propagator() {
		for (edge_finding, not_last, detectable_precedence) in
			itertools::iproduct!([true, false], [true, false], [true, false])
		{
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
			DisjunctiveStrictPropagator::new_in(
				&mut slv,
				vec![a, b, c],
				durations.clone(),
				edge_finding,
				not_last,
				detectable_precedence,
			);
			DisjunctiveStrictPropagator::new_in(
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
