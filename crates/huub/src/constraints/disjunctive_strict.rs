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

	// Internal state for propagation
	/// Indexes of the tasks sorted by earliest start time.
	tasks_sorted_earliest_start: Vec<usize>,
	/// Indexes of the tasks sorted by latest completion time.
	tasks_sorted_lastest_completion: Vec<usize>,
	/// Rank of the tasks by earliest start time.
	task_rankings_by_earliest_start: Vec<usize>,

	/// The Omega-Theta tree to compute the earliest completion time.
	ot_tree: OmegaThetaTree,

	/// Trailed earliest start and latest completion times of each task to aid in
	/// explaination.
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
		// Add propagator for lower bound propagation
		DisjunctiveStrictEdgeFinding::new_in(slv, start_times.clone(), self.durations.clone());

		// Add symmetric propagator for upper bound propagation
		let iter = start_times.iter().zip(self.durations.iter());
		let horizon = iter
			.clone()
			.map(|(v, d)| slv.get_int_upper_bound(*v) + d)
			.max()
			.unwrap();
		let symmetric_vars = iter.map(|(v, d)| -*v + (horizon - d)).collect();
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
	/// Explain why the current set of tasks in the tree must be completed after
	/// `time_bound`.
	fn explain_earliest_completion_time<A: ExplanationActions>(
		&self,
		time_bound: i32,
	) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let mut binding_task_idx = self.ot_tree.binding_task(time_bound, 0);
			let binding_task = self.tasks_sorted_earliest_start[binding_task_idx];
			let lb = self.earliest_start_time(binding_task, actions);
			let mut slack = time_bound - lb;
			let mut e_tasks = Vec::new();
			trace!(
				"conflict due to overload within the window [{}..{}]",
				lb,
				time_bound
			);
			// collect sufficient energy within the window [lb, time_bound)
			while binding_task_idx < self.tasks_sorted_earliest_start.len() {
				let xj = self.tasks_sorted_earliest_start[binding_task_idx];
				if self.earliest_start_time(xj, actions) >= lb
					&& self.latest_completion_time(xj, actions) < time_bound
				{
					e_tasks.push(xj);
					slack -= self.durations[xj] as i32;
					if slack <= 0 {
						break;
					}
				}
				binding_task_idx += 1;
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
				tasks_sorted_earliest_start: (0..n).collect(),
				tasks_sorted_lastest_completion: (0..n).collect(),
				task_rankings_by_earliest_start: (0..n).collect(),
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
	// todo: check whether this explanation can be generalized?
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, task_no: u64) -> Conjunction {
		// explain why the set of tasks Lcut(j) ∪ {i} cannot be completed before lct_j
		// since energy of the set of tasks (including i) within the time window [earliest_start, latest_completion] is overloaded
		// explain lower bound propagation for edge finding
		let task_no = task_no as usize;
		let mut clause = Vec::new();
		let earliest_start = actions.get_trailed_int(self.trailed_info[task_no].earliest_start);
		let latest_completion =
			actions.get_trailed_int(self.trailed_info[task_no].latest_completion);

		trace!(
			"explain lower bound of task {} due to overload within the window [{}..{}]",
			task_no,
			earliest_start,
			latest_completion
		);
		// collect at least latest_completion - earliest_start energy (including durations[task_no])
		// from tasks bracketed in [earliest_start, latest_completion] and form a set O
		// [start(t) >= latest_completion + 1] because
		// [start(t) >= earliest_start] /\ forall (t' in O) [start(t') >= earliest_start] /\ forall (t' in O) [end(t') <= latest_completion]
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
	#[tracing::instrument(name = "disjunctive_bounds", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// sort the tasks by earliest start time and construct the EF trees
		let earliest_start: Vec<_> = self
			.start_times
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect();
		let latest_completion: Vec<_> = self
			.start_times
			.iter()
			.enumerate()
			.map(|(i, v)| (actions.get_int_upper_bound(*v) + self.durations[i]))
			.collect();

		self.tasks_sorted_earliest_start
			.sort_by_key(|&i| earliest_start[i]);
		self.tasks_sorted_lastest_completion
			.sort_by_key(|&i| -latest_completion[i]);

		let sorted_earliest_start = self
			.tasks_sorted_earliest_start
			.iter()
			.map(|&i| earliest_start[i] as i32)
			.collect_vec();
		self.ot_tree.fill(
			&self.tasks_sorted_earliest_start,
			&sorted_earliest_start,
			&self.durations,
		);
		for ii in 0..self.tasks_sorted_earliest_start.len() {
			self.task_rankings_by_earliest_start[self.tasks_sorted_earliest_start[ii]] = ii;
		}

		// Check resource overload for all tasks
		let lct_task = self.tasks_sorted_lastest_completion[0];
		let time_bound = self.latest_completion_time(lct_task, actions);
		if self.ot_tree.root().earliest_completion > time_bound {
			actions.set_int_lower_bound(
				self.start_times[lct_task],
				self.ot_tree.root().earliest_completion as i64 - self.durations[lct_task],
				self.explain_earliest_completion_time(time_bound + 1),
			)?;
		}
		self.ot_tree
			.annotate_gray_task(self.task_rankings_by_earliest_start[lct_task]);

		// Run edge finding propagation for all tasks
		for j in 1..self.tasks_sorted_lastest_completion.len() {
			let earliest_completion_time = self.ot_tree.root().earliest_completion;
			let lct_task = self.tasks_sorted_lastest_completion[j];
			let time_bound = self.latest_completion_time(lct_task, actions);
			if earliest_completion_time > time_bound {
				// resource overload detected, eagerly build the reason clause for conflict
				let expl = self
					.explain_earliest_completion_time(time_bound + 1)
					.build_reason(actions);
				// trace!("resource overload detected, conflict clause: {:?}", clause);
				trace!("earliest completion time: {:?}", earliest_start);
				trace!("latest completion time: {:?}", latest_completion);
				let err = actions
					.set_int_lower_bound(
						self.start_times[lct_task],
						earliest_completion_time as i64 - self.durations[lct_task],
						expl,
					)
					.unwrap_err();
				return Err(err);
			}
			while self.ot_tree.root().earliest_completion_gray
				> self.latest_completion_time(lct_task, actions)
			{
				// there exists a gray task i such that ECT(Lcut(j) ∪ i) > lct_j, which implies Lcut(j) << i
				// identify the blocked task and blocking task
				let time_bound = self.ot_tree.root().earliest_completion_gray;
				let blocked_task_rank = self.ot_tree.blocked_task(time_bound);
				let blocked_task = self.tasks_sorted_earliest_start[blocked_task_rank];
				let earliest_completion = self.ot_tree.root().earliest_completion as i64;
				if actions.get_int_lower_bound(self.start_times[blocked_task]) < earliest_completion
				{
					let gray_est_task_rank = self.ot_tree.gray_est_responsible_task(time_bound);
					let gray_est_task = self.tasks_sorted_earliest_start[gray_est_task_rank];
					let lb = actions.get_int_lower_bound(self.start_times[gray_est_task]);
					// set trailed integer for lazy explanation
					let _ =
						actions.set_trailed_int(self.trailed_info[blocked_task].earliest_start, lb);
					let _ = actions.set_trailed_int(
						self.trailed_info[blocked_task].latest_completion,
						(time_bound - 1) as i64,
					);
					trace!(
						"set bound {} for task {}",
						earliest_completion,
						blocked_task
					);
					trace!("earliest completion time: {:?}", earliest_start);
					trace!("latest completion time: {:?}", latest_completion);
					actions.set_int_lower_bound(
						self.start_times[blocked_task],
						earliest_completion,
						actions.deferred_reason(blocked_task as u64),
					)?;
				}
				self.ot_tree.remove_task(blocked_task_rank);
			}
			self.ot_tree
				.annotate_gray_task(self.task_rankings_by_earliest_start[lct_task]);
		}
		Ok(())
	}
}

impl OmegaThetaTree {
	/// Annotate the leave node `i` as gray, and update its ancestors.
	fn annotate_gray_task(&mut self, i: usize) {
		assert!(self.leaves_start_idx + i < self.nodes.len());
		let idx = self.leaves_start_idx + i;
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i32::MIN;
		self.recursive_update(idx);
	}

	/// Finding the task responsible for pushing the earliest completion time beyond the time_bound
	fn binding_task(&self, time_bound: i32, node_id: usize) -> usize {
		assert!(self.nodes[0].earliest_completion >= time_bound);
		let mut node_id = node_id;
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
		node_id - self.leaves_start_idx
	}

	/// Find the gray task responsible for pushing the earliest completion time
	fn blocked_task(&self, earliest_completion_time: i32) -> usize {
		assert!(self.nodes[0].earliest_completion <= earliest_completion_time);
		assert!(self.nodes[0].earliest_completion_gray >= earliest_completion_time);
		let mut node_id = 0;
		let mut earliest_completion_time = earliest_completion_time;
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
		node_id - self.leaves_start_idx
	}

	/// Fill the tree with task are sorted by earliest start time.
	fn fill(&mut self, sorted_tasks: &[usize], sorted_time: &[i32], durations: &[i64]) {
		let n = sorted_tasks.len();
		// fill the leave nodes
		for i in 0..n {
			let idx = self.leaves_start_idx + i;
			let ect = sorted_time[i] + durations[sorted_tasks[i]] as i32;
			self.nodes[idx].total_durations = durations[sorted_tasks[i]] as i32;
			self.nodes[idx].earliest_completion = ect;
			self.nodes[idx].total_durations_gray = durations[sorted_tasks[i]] as i32;
			self.nodes[idx].earliest_completion_gray = ect;
		}

		// update internal nodes in a bottom-up fashion
		(0..self.leaves_start_idx).rev().for_each(|i| {
			self.update_internal_node(i);
		});
	}

	/// Finding the task responsible for min{est_S, est_i} where
	/// - S is the set of tasks in the tree
	/// - task i is one of the gray task in the tree
	fn gray_est_responsible_task(&self, earliest_completion_time: i32) -> usize {
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
		node_id - self.leaves_start_idx
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
		}
	}

	#[inline]
	/// Calculate the index of the parent of a node `i`
	fn parent(i: usize) -> usize {
		debug_assert_ne!(i, 0);
		(i - 1) >> 1
	}

	/// Update node `i` and trigger the update of its parent recursively.
	fn recursive_update(&mut self, i: usize) {
		if i == 0 {
			return;
		}
		let parent = Self::parent(i);
		self.update_internal_node(parent);
		self.recursive_update(parent);
	}

	/// Remove the task at index `i` from the tree.
	fn remove_task(&mut self, i: usize) {
		assert!(self.leaves_start_idx + i < self.nodes.len());
		let idx = self.leaves_start_idx + i;
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
