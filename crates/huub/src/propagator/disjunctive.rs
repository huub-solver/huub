use tracing::trace;

use crate::{
	actions::{
		explanation::ExplanationActions, initialization::InitializationActions,
		inspection::InspectionActions, trailing::TrailingActions,
	},
	propagator::{
		conflict::Conflict, int_event::IntEvent, reason::ReasonBuilder, PropagationActions,
		Propagator,
	},
	solver::{
		engine::{int_var::LitMeaning, queue::PriorityLevel, trail::TrailedInt},
		poster::{BoxedPropagator, Poster, QueuePreferences},
		view::{BoolView, BoolViewInner, IntView},
	},
	Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct OmegaThetaTreeNode {
	// precomputed values for the set of tasks under the tree rooted at this node
	total_durations: i32,
	earliest_completion: i32,

	// precomputed values for the set of tasks under the tree rooted at this node
	// at most one gray node can be used in the subtree rooted at this node
	total_durations_gray: i32,
	earliest_completion_gray: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct OmegaThetaTree {
	nodes: Vec<OmegaThetaTreeNode>,
	size: usize,
	levaes_start_idx: usize,
}

#[inline]
fn left_child(i: usize) -> usize {
	(i << 1) + 1
}

#[inline]
fn right_child(i: usize) -> usize {
	(i << 1) + 2
}

impl OmegaThetaTree {
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
			size: tree_size,
			levaes_start_idx: tree_size / 2,
		}
	}

	// task are sorted by earliest start time
	pub(crate) fn fill(&mut self, sorted_tasks: &[usize], sorted_time: &[i32], durations: &[i64]) {
		let n = sorted_tasks.len();
		// fill the leave nodes
		for i in 0..n {
			let idx = self.levaes_start_idx + i;
			let ect = sorted_time[i] + durations[sorted_tasks[i]] as i32;
			self.nodes[idx].total_durations = durations[sorted_tasks[i]] as i32;
			self.nodes[idx].earliest_completion = ect;
			self.nodes[idx].total_durations_gray = durations[sorted_tasks[i]] as i32;
			self.nodes[idx].earliest_completion_gray = ect;
		}

		// udpate internal nodes in a botoom-up fashion
		(0..self.levaes_start_idx).rev().for_each(|i| {
			self.update_internal_node(i);
		});
	}

	pub(crate) fn root(&self) -> &OmegaThetaTreeNode {
		&self.nodes[0]
	}

	pub(crate) fn remove_task(&mut self, i: usize) {
		assert!(self.levaes_start_idx + i < self.size);
		let idx = self.levaes_start_idx + i;
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i32::MIN;
		self.nodes[idx].total_durations_gray = 0;
		self.nodes[idx].earliest_completion_gray = i32::MIN;
		self.recursive_update(idx);
	}

	pub(crate) fn annotate_gray_task(&mut self, i: usize) {
		assert!(self.levaes_start_idx + i < self.size);
		let idx = self.levaes_start_idx + i;
		self.nodes[idx].total_durations = 0;
		self.nodes[idx].earliest_completion = i32::MIN;
		self.recursive_update(idx);
	}

	fn recursive_update(&mut self, i: usize) {
		if i == 0 {
			return;
		}
		let parent = (i - 1) >> 1;
		self.update_internal_node(parent);
		self.recursive_update(parent);
	}

	fn update_internal_node(&mut self, i: usize) {
		let left_child = left_child(i);
		let right_child = right_child(i);
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

	// Find the gray task responsible for pushing the earliest completion time
	pub(crate) fn blocked_task(&self, earliest_completion_time: i32) -> usize {
		assert!(self.nodes[0].earliest_completion < earliest_completion_time);
		assert!(self.nodes[0].earliest_completion_gray >= earliest_completion_time);
		let mut node_id = 0;
		let mut earliest_completion_time = earliest_completion_time;
		while node_id < self.levaes_start_idx {
			if self.nodes[left_child(node_id)].total_durations_gray == 0 {
				node_id = right_child(node_id);
			} else if self.nodes[right_child(node_id)].total_durations_gray == 0 {
				node_id = left_child(node_id);
			} else if self.nodes[right_child(node_id)].earliest_completion_gray
				>= earliest_completion_time
			{
				node_id = right_child(node_id);
			} else if self.nodes[left_child(node_id)].earliest_completion
				+ self.nodes[right_child(node_id)].total_durations_gray
				>= earliest_completion_time
			{
				// The binding task is to the left, blocked task contributes only to the sum
				earliest_completion_time -= self.nodes[left_child(node_id)].earliest_completion;
				node_id = right_child(node_id);
				while node_id < self.levaes_start_idx {
					if self.nodes[left_child(node_id)].total_durations_gray
						+ self.nodes[right_child(node_id)].total_durations
						== earliest_completion_time
					{
						earliest_completion_time -=
							self.nodes[right_child(node_id)].total_durations;
						node_id = left_child(node_id);
					} else if self.nodes[left_child(node_id)].total_durations
						+ self.nodes[right_child(node_id)].total_durations_gray
						>= earliest_completion_time
					{
						earliest_completion_time -= self.nodes[left_child(node_id)].total_durations;
						node_id = right_child(node_id);
					} else {
						unreachable!("unexpected case");
					}
				}
				break;
			} else {
				earliest_completion_time -= self.nodes[right_child(node_id)].total_durations;
				node_id = left_child(node_id);
			}
		}
		node_id - self.levaes_start_idx
	}

	// Finding the task responsible for pushing the earliest completion time beyond the time_bound
	pub(crate) fn binding_task(&self, time_bound: i32, node_id: usize) -> usize {
		assert!(self.nodes[0].earliest_completion >= time_bound);
		let mut node_id = node_id;
		let mut earliest_completion_time = time_bound;
		while node_id < self.levaes_start_idx {
			if self.nodes[right_child(node_id)].earliest_completion >= earliest_completion_time {
				node_id = right_child(node_id);
			} else {
				earliest_completion_time -= self.nodes[right_child(node_id)].total_durations;
				node_id = left_child(node_id);
			}
		}
		node_id - self.levaes_start_idx
	}

	// Finding the task responsible for min{est_S, est_i} where
	// - S is the set of tasks in the tree
	// - task i is one of the gray task in the tree
	pub(crate) fn gray_est_responsible_task(&self, earliest_completion_time: i32) -> usize {
		assert!(self.nodes[0].earliest_completion < earliest_completion_time);
		assert!(self.nodes[0].earliest_completion_gray >= earliest_completion_time);
		let mut node_id = 0;
		let mut earliest_completion_time = earliest_completion_time;
		while node_id < self.levaes_start_idx {
			let left_child = left_child(node_id);
			let right_child = right_child(node_id);
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
		node_id - self.levaes_start_idx
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TaskInfo {
	earliest_start: TrailedInt,
	latest_completion: TrailedInt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DisjunctiveEdgeFinding {
	// Parameters
	start_times: Vec<IntView>,
	durations: Vec<i64>,
	// Action List
	action_list: Vec<u32>,

	// Internal state for propagation
	tasks_sorted_earliest_start: Vec<usize>,
	tasks_sorted_lastest_completion: Vec<usize>,
	task_rankings_by_earliest_start: Vec<usize>,

	ot_tree: OmegaThetaTree,

	// Internal state for explanation
	trailed_info: Vec<TaskInfo>,
}

impl DisjunctiveEdgeFinding {
	pub(crate) fn prepare<V: Into<IntView>, I: IntoIterator<Item = V>>(
		start_times: I,
		durations: Vec<i64>,
	) -> impl Poster {
		let start_times: Vec<IntView> = start_times.into_iter().map(Into::into).collect();
		DisjunctiveEdgeFindingPoster {
			start_times,
			durations,
		}
	}

	#[inline]
	fn latest_completion_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i32 {
		actions.get_int_upper_bound(self.start_times[i]) as i32 + self.durations[i] as i32
	}

	#[inline]
	fn earliest_start_time<I: InspectionActions>(&self, i: usize, actions: &mut I) -> i32 {
		actions.get_int_lower_bound(self.start_times[i]) as i32
	}

	// Explain why the current set of tasks in the tree must be completed after time_bound
	#[inline]
	fn explain_earliest_completion_time<P: PropagationActions>(
		&self,
		time_bound: i32,
		actions: &mut P,
	) -> Vec<BoolView> {
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
		trace!(slack = slack, "slack");
		trace!(e_tasks = ?e_tasks, "tasks contributing to the overload");
		let r_end = time_bound - slack;
		e_tasks
			.iter()
			.map(|&i| {
				(
					actions.get_int_lit(self.start_times[i], LitMeaning::GreaterEq(lb as i64)),
					actions.get_int_lit(
						self.start_times[i],
						LitMeaning::Less(r_end as i64 - self.durations[i]),
					),
				)
			})
			.fold(Vec::new(), |acc, (a, b)| [acc, vec![a, b]].concat())
	}

	fn propagate_lower_bounds<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
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
			.sort_unstable_by_key(|&i| actions.get_int_lower_bound(self.start_times[i]));
		self.tasks_sorted_lastest_completion
			.sort_unstable_by_key(|&i| {
				-(actions.get_int_upper_bound(self.start_times[i]) + self.durations[i])
			});
		let sorted_ealiest_start = self
			.tasks_sorted_earliest_start
			.iter()
			.map(|&i| actions.get_int_lower_bound(self.start_times[i]) as i32)
			.collect::<Vec<_>>();
		self.ot_tree.fill(
			&self.tasks_sorted_earliest_start,
			&sorted_ealiest_start,
			&self.durations,
		);
		for ii in 0..self.tasks_sorted_earliest_start.len() {
			self.task_rankings_by_earliest_start[self.tasks_sorted_earliest_start[ii]] = ii;
		}

		// Check resource overload for all tasks
		let lct_task = self.tasks_sorted_lastest_completion[0];
		let time_bound = self.latest_completion_time(lct_task, actions);
		if self.ot_tree.root().earliest_completion > time_bound {
			let clause = self.explain_earliest_completion_time(time_bound + 1, actions);
			actions.set_int_lower_bound(
				self.start_times[lct_task],
				self.ot_tree.root().earliest_completion as i64 - self.durations[lct_task],
				&ReasonBuilder::Eager(clause),
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
				let clause = self.explain_earliest_completion_time(time_bound + 1, actions);
				trace!("resource overload detected, conflict clause: {:?}", clause);
				trace!("earliest completion time: {:?}", earliest_start);
				trace!("latest completion time: {:?}", latest_completion);
				actions.set_int_lower_bound(
					self.start_times[lct_task],
					earliest_completion_time as i64 - self.durations[lct_task],
					&ReasonBuilder::Eager(clause),
				)?;
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
						&ReasonBuilder::Lazy(blocked_task as u64),
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

impl<P, E, T> Propagator<P, E, T> for DisjunctiveEdgeFinding
where
	P: PropagationActions,
	E: ExplanationActions,
	T: TrailingActions,
{
	fn notify_event(&mut self, data: u32, _: &IntEvent, _: &mut T) -> bool {
		self.action_list.push(data);
		true
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear()
	}

	#[tracing::instrument(name = "disjunctive_bounds", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		self.propagate_lower_bounds(actions)?;
		Ok(())
	}

	fn explain(&mut self, actions: &mut E, task_no: u64) -> Conjunction {
		// explain why the set of tasks Lcut(j) ∪ {i} cannot be completed before lct_j
		// since energy of the set of tasks within the window [lb, time_bound) is overloaded
		// explain lower bound propagation for edge finding
		let task_no = task_no as usize;
		let mut clause = Vec::new();
		let earliest_start = actions.get_trailed_int(self.trailed_info[task_no].earliest_start);
		let latest_completion =
			actions.get_trailed_int(self.trailed_info[task_no].latest_completion);

		trace!(
			"explain lower bound due to overload within the window [{}..{}]",
			earliest_start,
			latest_completion
		);
		// [start(t) >= l] /\ forall (t' in O) [start(t') >= l] /\ forall (t' in O) [end(t') <= u] -> [start(t) >= u].
		// collect at least latest_completion - earliest_start - durations[task_no] energy, from tasks bracketed in [lb, ub]
		// todo: check whether this explanation can be generalized?
		clause.push(actions.get_int_lit(
			self.start_times[task_no],
			LitMeaning::GreaterEq(earliest_start),
		));
		let mut energy = latest_completion - earliest_start - self.durations[task_no];
		for i in 0..self.start_times.len() {
			if i != task_no
				&& self.earliest_start_time(i, actions) >= earliest_start as i32
				&& self.latest_completion_time(i, actions) <= latest_completion as i32
			{
				clause.push(actions.get_int_lower_bound_lit(self.start_times[i]));
				clause.push(actions.get_int_lit(
					self.start_times[i],
					LitMeaning::Less(latest_completion - self.durations[i] + 1),
				));
				energy -= self.durations[i];
				if energy <= 0 {
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
}

struct DisjunctiveEdgeFindingPoster {
	start_times: Vec<IntView>,
	durations: Vec<i64>,
}

impl Poster for DisjunctiveEdgeFindingPoster {
	fn post<I: InitializationActions>(
		self,
		actions: &mut I,
	) -> (BoxedPropagator, QueuePreferences) {
		let n = self.start_times.len();
		let prop = DisjunctiveEdgeFinding {
			start_times: self.start_times,
			durations: self.durations,
			action_list: Vec::new(),
			tasks_sorted_earliest_start: (0..n).collect(),
			tasks_sorted_lastest_completion: (0..n).collect(),
			task_rankings_by_earliest_start: (0..n).collect(),
			ot_tree: OmegaThetaTree::new(n),
			trailed_info: (0..n)
				.map(|_| TaskInfo {
					earliest_start: actions.new_trailed_int(0),
					latest_completion: actions.new_trailed_int(0),
				})
				.collect(),
		};

		for (i, v) in prop.start_times.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Bounds, i as u32)
		}

		(
			Box::new(prop),
			QueuePreferences {
				enqueue_on_post: true,
				priority: PriorityLevel::Low,
			},
		)
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		propagator::disjunctive::DisjunctiveEdgeFinding,
		solver::engine::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_disjunctive_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
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
		slv.add_propagator(DisjunctiveEdgeFinding::prepare(
			[a, b, c],
			durations.clone(),
		));
		slv.add_propagator(DisjunctiveEdgeFinding::prepare(
			[a, b, c]
				.iter()
				.zip(durations.iter())
				.map(|(v, d)| -*v + (7 - d)),
			durations.clone(),
		));

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
