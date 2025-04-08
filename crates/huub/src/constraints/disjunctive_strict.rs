//! Structures and algorithms for the `disjunctive_strict` constraint, which
//! enforces that no two tasks overlap from a list of tasks.

use std::collections::VecDeque;

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
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, BoolViewInner,
		IntLitMeaning, IntView,
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `disjunctive_strict` constraint using the Strict Edge
/// Finding algorithm.
pub struct DisjunctiveStrictEdgeFinding {
	/// Start time variables of each task.
	start_times: Vec<IntView>,
	/// Durations of each task.
	durations: Vec<IntVal>,
	/// The Omega-Theta tree to compute the earliest completion time.
	ot_tree: OmegaThetaTree,
	/// Trailed earliest start and latest completion times of each task to aid in
	/// explaination.
	trailed_info: Vec<TaskInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propagator for the `disjunctive_strict` constraint using the Strict
/// Not-First/Not-Last algorithm.
pub struct DisjunctiveStrictNotLast {
	/// Start time variables of each task.
	start_times: Vec<IntView>,
	/// Durations of each task.
	durations: Vec<IntVal>,
	/// Omega-Theta tree to compute the earliest completion time.
	ot_tree: OmegaThetaTree,
	/// Trailed earliest start and latest completion times to aid in explaination.
	trailed_info: Vec<TaskInfo>,
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
	total_durations: i32,
	/// Earliest completion time of the tasks under the tree rooted at this node.
	earliest_completion: i32,

	/// Total duration of the tasks under the tree rooted at this node, with at
	/// most one gray node.
	total_durations_gray: i32,
	/// Earliest completion time of the tasks under the tree rooted at this node,
	/// with at most one gray node.
	earliest_completion_gray: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Internal structure to store trailed information about tasks.
struct TaskInfo {
	/// Earliest start time of the task.
	earliest_start: TrailedInt,
	/// Latest completion time of the task.
	latest_completion: TrailedInt,
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

		// Add not-last propagators
		DisjunctiveStrictNotLast::new_in(slv, start_times.clone(), self.durations.clone());
		DisjunctiveStrictNotLast::new_in(slv, symmetric_vars.clone(), self.durations.clone());

		// Add edge finding propagators
		DisjunctiveStrictEdgeFinding::new_in(slv, start_times.clone(), self.durations.clone());
		DisjunctiveStrictEdgeFinding::new_in(slv, symmetric_vars, self.durations.clone());
		Ok(())
	}
}

impl DisjunctiveStrictEdgeFinding {
	#[inline]
	/// Return the (current) earliest start time of task `i`.
	fn earliest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i32 {
		actions.get_int_lower_bound(self.start_times[i]) as i32
	}

	#[inline]
	/// Explain resource overload within the time window [`earliest_start`, `time_bound`]
	fn explain_overload<A: ExplanationActions>(
		&self,
		time_bound: i32,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let binding_task = self.ot_tree.binding_task(time_bound, 0);
			let earliest_start = actions.get_int_lower_bound(self.start_times[binding_task]) as i32;
			let mut slack = time_bound - earliest_start;
			let mut e_tasks = Vec::new();

			trace!(
				window =? (earliest_start, time_bound),
				"Explaination for overload"
			);
			// collect sufficient energy within the window [lb, time_bound)
			for i in 0..self.start_times.len() {
				if self.earliest_start_time(i, actions) >= earliest_start
					&& self.latest_completion_time(i, actions) < time_bound
				{
					e_tasks.push(i);
					slack -= self.durations[i] as i32;
					if slack <= 0 {
						break;
					}
				}
			}
			trace!(e_tasks = ?e_tasks, "tasks contributing to the overload");
			e_tasks
				.iter()
				.flat_map(|&i| {
					let (bv, _) = actions.get_int_lit_relaxed(
						self.start_times[i],
						IntLitMeaning::Less((time_bound - slack) as IntVal - self.durations[i]),
					);
					[actions.get_int_lower_bound_lit(self.start_times[i]), bv]
				})
				.collect_vec()
		}
	}

	#[inline]
	/// Return the (current) latest completion time of task `i`.
	fn latest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i32 {
		actions.get_int_upper_bound(self.start_times[i]) as i32 + self.durations[i] as i32
	}

	/// Create a new [`DisjunctiveStrictEdgeFinding`] propagator and post it in
	/// the solver.
	pub fn new_in<P>(solver: &mut P, start_times: Vec<IntView>, durations: Vec<IntVal>)
	where
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
			}),
			PriorityLevel::Low,
		);

		for v in start_times {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}
}

impl<P, E> Propagator<P, E> for DisjunctiveStrictEdgeFinding
where
	P: PropagationActions,
	E: ExplanationActions,
{
	/// Explain lower bound propagation for edge finding
	#[tracing::instrument(
		name = "disjunctive_edge_finding",
		level = "trace",
		skip(self, actions)
	)]
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, data: u64) -> Conjunction {
		// explain why the set of tasks LCut(j) ∪ {i} cannot be completed before lct_j
		// since energy of the set of tasks (including i) within the time window [earliest_start, latest_completion] is overloaded
		let task_no = data as usize;
		let earliest_start = actions.get_trailed_int(self.trailed_info[task_no].earliest_start);
		let latest_completion =
			actions.get_trailed_int(self.trailed_info[task_no].latest_completion);

		trace!(
			task_no,
			window =? (earliest_start, latest_completion),
			"Explaination"
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
				&& self.earliest_start_time(i, actions) >= earliest_start as i32
				&& self.latest_completion_time(i, actions) <= latest_completion as i32
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

	#[tracing::instrument(
		name = "disjunctive_edge_finding",
		level = "trace",
		skip(self, actions)
	)]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// Sort the tasks by earliest start time and initialize the Omega-Theta tree
		let earliest_start: Vec<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect();
		self.ot_tree.initialize(earliest_start.as_slice());
		for i in 0..self.start_times.len() {
			self.ot_tree.add_task(
				i,
				actions.get_int_lower_bound(self.start_times[i]) as i32,
				self.durations[i],
			);
		}

		// Sort the tasks in non-increasing order of their latest completion times
		let latest_completion: Vec<_> = self
			.start_times
			.iter()
			.enumerate()
			.map(|(i, v)| (actions.get_int_upper_bound(*v) + self.durations[i]))
			.collect();
		let tasks_sorted_latest_completion = (0..self.start_times.len())
			.sorted_by_key(|i| -latest_completion[*i])
			.collect_vec();

		// Traverse all tasks ordered by latest completion time and check the edge finding propagation rule
		// Invariant: (1) all non-gray tasks in `ot_tree` forms LCut(j) = { i | lct_i ≤ lct_j }
		//            (2) all gray tasks in `ot_tree` are in the set T \setminus LCut(j)
		for (j, &lct_task) in tasks_sorted_latest_completion.iter().enumerate() {
			let earliest_completion_time = self.ot_tree.root().earliest_completion;
			let lct = self.latest_completion_time(lct_task, actions);
			// Checking resource overload for LCut(j): ect(LCut(j)) > lct(LCut(j)) = lct_j => failure
			if earliest_completion_time > lct {
				// resource overload detected, eagerly build the reason clause for conflict
				let binding_task = self
					.ot_tree
					.binding_task(self.ot_tree.root().earliest_completion, 0);
				let earliest_start = actions.get_int_lower_bound(self.start_times[binding_task]);
				let expl = self.explain_overload(lct + 1);
				trace!(
					time_window =? (earliest_start, lct),
					"resource overload"
				);
				actions.set_int_lower_bound(
					self.start_times[lct_task],
					earliest_completion_time as i64 - self.durations[lct_task],
					expl,
				)?;
			}
			// Checking the edge finding propagation rule: ∀ i \in T \setminus LCut(j), ect(LCut(j) ∪ i) > lct_j => LCut(j) << i
			while j > 0 && self.ot_tree.root().earliest_completion_gray > lct {
				let ect_gray = self.ot_tree.root().earliest_completion_gray;
				let blocked_task = self
					.ot_tree
					.blocked_task(self.ot_tree.root().earliest_completion_gray);
				let earliest_completion = self.ot_tree.root().earliest_completion as i64;
				if actions.get_int_lower_bound(self.start_times[blocked_task]) < earliest_completion
				{
					let gray_est_task = self.ot_tree.blocking_task(ect_gray);
					let lb = actions.get_int_lower_bound(self.start_times[gray_est_task]);
					// set trailed integer for lazy explanation
					let _ =
						actions.set_trailed_int(self.trailed_info[blocked_task].earliest_start, lb);
					let _ = actions.set_trailed_int(
						self.trailed_info[blocked_task].latest_completion,
						(ect_gray - 1) as i64,
					);
					trace!(
						earliest_completion,
						task = blocked_task,
						window =? (lb, ect_gray - 1),
						"Propagation"
					);
					actions.set_int_lower_bound(
						self.start_times[blocked_task],
						earliest_completion,
						actions.deferred_reason(blocked_task as u64),
					)?;
				}
				// remove the blocked task as the maximum propagation has been achieved by LCut(j) where lct_j is maximum
				self.ot_tree.remove_task(blocked_task);
			}
			self.ot_tree.annotate_gray_task(lct_task);
		}
		Ok(())
	}
}

impl DisjunctiveStrictNotLast {
	/// Create a new [`DisjunctiveStrictNotLast`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(solver: &mut P, start_times: Vec<IntView>, durations: Vec<IntVal>)
	where
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
			}),
			PriorityLevel::Low,
		);

		for v in start_times {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}
}

impl<P, E> Propagator<P, E> for DisjunctiveStrictNotLast
where
	P: PropagationActions,
	E: ExplanationActions,
{
	/// Explain upper bound propagation for not-last propagation
	#[tracing::instrument(name = "disjunctive_not_last", level = "trace", skip(self, actions))]
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, i: u64) -> Conjunction {
		// explain why task i cannot be the last task within the set NLset(i) ∪ {i}
		let task_no = i as usize;
		let updated_lct_i = actions.get_trailed_int(self.trailed_info[task_no].latest_completion);
		let nlset_est = actions.get_trailed_int(self.trailed_info[task_no].earliest_start);
		trace!(
			task_no,
			window =? (nlset_est, updated_lct_i),
			"Explaination"
		);
		// collect the set of tasks in NLset(i) = { j | lst_j ≤ updated_lct_i & est_j + p_j ≥ nlset_ect & j ≠ i }
		let nlset = self
			.start_times
			.iter()
			.enumerate()
			.filter(|(j, &v)| {
				*j != task_no
					&& actions.get_int_upper_bound(v) <= updated_lct_i
					&& actions.get_int_lower_bound(v) >= nlset_est
			})
			.collect_vec();

		let task_lct =
			actions.get_int_upper_bound(self.start_times[task_no]) + self.durations[task_no];
		assert_ne!(nlset.len(), 0);
		// compute the total duration of the tasks in NLset(i)
		let total_duration = nlset
			.iter()
			.map(|(j, _)| self.durations[*j])
			.sum::<IntVal>();

		// explain the reason why task i cannot be the last task
		let mut clause = Vec::new();
		clause.push(actions.get_int_upper_bound_lit(self.start_times[task_no]));
		for (_, v) in nlset {
			// explain the reason why all tasks in NLset(i) will stay in NLset(i)
			// (1) If for all j in NLset(i) [est_j > lct_i + p_i - p_{\Omega}], then NLset(i) \not\prec i
			let (bv, _) = actions.get_int_lit_relaxed(
				*v,
				IntLitMeaning::GreaterEq(task_lct - self.durations[task_no] - total_duration + 1),
			);
			clause.push(bv);
			// (2) explain the reason why the latest completion time of task i is set to updated_lct_i
			// If for all j in NLset(i) [lct_j - p_j ≤ lct_i'], then lct_i' should be set
			let (bv, _) = actions.get_int_lit_relaxed(*v, IntLitMeaning::Less(updated_lct_i + 1));
			clause.push(bv);
		}
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

	#[tracing::instrument(name = "disjunctive_not_last", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// Sort the tasks by earliest start time and initialize the Omega-Theta tree
		let earliest_start: Vec<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect();
		self.ot_tree.initialize(earliest_start.as_slice());

		// Store the updated latest completion time of each task
		let mut updated_lct = self
			.start_times
			.iter()
			.enumerate()
			.map(|(i, &v)| actions.get_int_upper_bound(v) + self.durations[i])
			.collect_vec();

		// Sort the tasks by latest start time and latest completion time respectively
		let mut tasks_sorted_by_latest_start: VecDeque<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_upper_bound(*v))
			.enumerate()
			.sorted_by_key(|(_, v)| *v)
			.collect();
		let tasks_sorted_by_latest_completion: Vec<_> = self
			.start_times
			.iter()
			.enumerate()
			.map(|(i, v)| (i, actions.get_int_upper_bound(*v) + self.durations[i]))
			.sorted_by_key(|(_, v)| *v)
			.collect();

		self.ot_tree.clear();
		let mut front_task = 0;
		for (lct_task, lct) in tasks_sorted_by_latest_completion.iter() {
			while tasks_sorted_by_latest_start
				.front()
				.is_some_and(|(_, lst_front)| lct > lst_front)
			{
				// the latest start time of the front task is smaller than
				// the latest completion of the current task, add to the omega tree
				front_task = tasks_sorted_by_latest_start.pop_front().unwrap().0; // safe since front is not empty
				self.ot_tree.add_task(
					front_task,
					actions.get_int_lower_bound(self.start_times[front_task]) as i32,
					self.durations[front_task],
				);
			}

			// temporarily remove task `lct_task` from the tree
			self.ot_tree.remove_task(*lct_task);

			// the theta tree contains all other tasks with latest start time < lct
			// i.e. NLset(lct_task) = {j | lst_j < lct & j ≠ lct_task }
			// check if the earliest completion time of the tree is greater than
			// the latest start time of the current task
			let tasks_in_tree_ect = self.ot_tree.root().earliest_completion;
			if tasks_in_tree_ect > (*lct - self.durations[*lct_task]) as i32 {
				let lst_front = actions.get_int_upper_bound(self.start_times[front_task]);
				let binding_task = self.ot_tree.binding_task(tasks_in_tree_ect, 0);
				if lst_front < updated_lct[*lct_task] {
					let _ = actions.set_trailed_int(
						self.trailed_info[*lct_task].earliest_start,
						actions.get_int_lower_bound(self.start_times[binding_task]),
					);
					let _ = actions
						.set_trailed_int(self.trailed_info[*lct_task].latest_completion, lst_front);
					trace!(
						task = *lct_task,
						window =? (lst_front, updated_lct[*lct_task]),
						latest_start_time = lst_front,
						"Propagation"
					);
				}
				updated_lct[*lct_task] = updated_lct[*lct_task].min(lst_front);
			}

			// add task `lct_task` back to the tree
			self.ot_tree.add_task(
				*lct_task,
				actions.get_int_lower_bound(self.start_times[*lct_task]) as i32,
				self.durations[*lct_task],
			);
		}

		// Update the latest completion time for each task
		for (i, _) in tasks_sorted_by_latest_completion.iter() {
			actions.set_int_upper_bound(
				self.start_times[*i],
				updated_lct[*i] - self.durations[*i],
				actions.deferred_reason(*i as u64),
			)?;
		}
		Ok(())
	}
}

impl OmegaThetaTree {
	/// Add a task with number `task_no` to the tree.
	fn add_task(&mut self, task_no: usize, earliest_start_time: i32, duration: i64) {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		self.nodes[idx].total_durations = duration as i32;
		self.nodes[idx].earliest_completion = earliest_start_time + duration as i32;
		self.nodes[idx].total_durations_gray = duration as i32;
		self.nodes[idx].earliest_completion_gray = earliest_start_time + duration as i32;
		self.recursive_update(idx);
	}

	/// Annotate task with number `task_no` as gray, and update its ancestors.
	fn annotate_gray_task(&mut self, task_no: usize) {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i32::MIN;
		self.recursive_update(idx);
	}

	/// Finding the task responsible for pushing the earliest completion time of node with index `idx` beyond the time_bound
	fn binding_task(&self, time_bound: i32, idx: usize) -> usize {
		assert!(self.nodes[0].earliest_completion >= time_bound);
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

	/// Find the gray task responsible for pushing the earliest completion time, i.e. ect(\Omega ∪ i) > time_bound
	fn blocked_task(&self, time_bound: i32) -> usize {
		assert!(self.nodes[0].earliest_completion <= time_bound);
		assert!(self.nodes[0].earliest_completion_gray >= time_bound);
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

	/// Clear the tree and reset the earliest completion time.
	fn clear(&mut self) {
		for i in 0..self.nodes.len() {
			self.nodes[i].total_durations = 0;
			self.nodes[i].earliest_completion = i32::MIN;
			self.nodes[i].total_durations_gray = 0;
			self.nodes[i].earliest_completion_gray = i32::MIN;
		}
		// update internal nodes in a bottom-up fashion
		(0..self.leaves_start_idx).rev().for_each(|i| {
			self.update_internal_node(i);
		});
	}

	/// Finding the task responsible for min{est_S, est_i} where
	/// - S is the set of tasks in the tree
	/// - task i is one of the gray task in the tree
	fn blocking_task(&self, earliest_completion_time: i32) -> usize {
		assert!(self.nodes[0].earliest_completion <= earliest_completion_time);
		assert!(self.nodes[0].earliest_completion_gray >= earliest_completion_time);
		let mut node_id = 0;
		let mut earliest_completion_time = earliest_completion_time;
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
					earliest_completion: i32::MIN,
					total_durations_gray: 0,
					earliest_completion_gray: i32::MIN,
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
	fn remove_task(&mut self, task_no: usize) {
		assert!(task_no < self.task_no.len());
		let idx = self.node_index(task_no);
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i32::MIN;
		self.nodes[idx].total_durations_gray = 0;
		self.nodes[idx].earliest_completion_gray = i32::MIN;
		self.recursive_update(idx);
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
		self.nodes[i].earliest_completion = i32::max(
			right_earliest_completion,
			left_earliest_completion + right_total_durations,
		);
		self.nodes[i].total_durations_gray = i32::max(
			left_total_durations_gray + right_total_durations,
			left_total_durations + right_total_durations_gray,
		);
		self.nodes[i].earliest_completion_gray = i32::max(
			right_earliest_completion_gray,
			i32::max(
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
		constraints::disjunctive_strict::DisjunctiveStrictEdgeFinding,
		solver::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_disjunctive_sat() {
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
		DisjunctiveStrictEdgeFinding::new_in(&mut slv, vec![a, b, c], durations.clone());
		DisjunctiveStrictEdgeFinding::new_in(
			&mut slv,
			[a, b, c]
				.iter()
				.zip(durations.iter())
				.map(|(v, d)| -*v + (7 - d))
				.collect(),
			durations.clone(),
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
