//! `check` propagator for the `circuit` / `subcircuit` constraints.
//!
//! Follows each chain of fixed successors and fails on a closed sub-tour that
//! does not span every node.

use crate::{
	IntVal,
	actions::{
		InitActions, IntEvent, IntPropCond, IntPropagationActions, PostingActions,
		PropagationActions, ReasoningEngine,
	},
	constraints::{IntSolverActions, Propagator, circuit::graph::CircuitGraph},
	solver::{engine::Engine, queue::PriorityLevel},
};

/// Reusable scratch for the `check` algorithm.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct CheckScratch {
	/// Successor position of every fixed node (`None` if unfixed).
	fixed_succ: Vec<Option<usize>>,
	/// Nodes already assigned to a scanned chain.
	visited: Vec<bool>,
	/// The current fixed chain/cycle, in visit order, reused across starts.
	nodes: Vec<usize>,
	/// The complement of the current cycle (built only when one closes).
	outside: Vec<usize>,
	/// Membership of the current cycle over `0..n`, kept clean between cycles
	/// so the complement is one `O(n)` pass, not `O(n·|cycle|)` linear
	/// `contains`.
	in_cycle: Vec<bool>,
}

/// The `check` propagator for the `circuit` and `subcircuit` constraints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitCheck<I> {
	/// Successor graph plus the shared explanation helpers.
	pub(crate) graph: CircuitGraph<I>,
	/// Reusable scratch for the algorithm.
	scratch: CheckScratch,
	/// Recently fixed variables.
	actions_list: Vec<usize>,
	/// Whether the propagator is dirty and needs to run a full check.
	dirty: bool,
}

impl CheckScratch {
	/// Allocate scratch sized for an `n`-node support graph.
	pub(crate) fn new(n: usize) -> Self {
		Self {
			fixed_succ: vec![None; n],
			visited: vec![false; n],
			nodes: Vec::new(),
			outside: Vec::new(),
			in_cycle: vec![false; n],
		}
	}

	/// `check`: follow each chain of fixed successors and fail on a closed
	/// sub-tour that does not span every node.
	///
	/// Assumes the posted `alldifferent` already holds, so the fixed successors
	/// form a partial permutation.
	pub(crate) fn run<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		action_list: impl IntoIterator<Item = usize>,
		ctx: &mut C,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.n();
		self.visited.fill(false);

		// Iterate over recently fixed nodes to find new closed chains
		for start in action_list {
			if self.visited[start] || self.fixed_succ[start].is_none() {
				continue;
			}
			self.nodes.clear();
			let mut node = start;
			let mut closed = false;
			while let Some(next) = self.fixed_succ[node] {
				if self.visited[node] {
					break;
				}
				self.visited[node] = true;
				self.nodes.push(node);
				if next == start {
					closed = true;
					break;
				}
				node = next;
			}

			if !closed || self.nodes.len() >= n {
				continue;
			}
			// In `subcircuit`, a self-loop (length-1 cycle) marks an excluded node.
			if graph.subcircuit && self.nodes.len() == 1 {
				continue;
			}

			// Build the complement of the closed cycle in one `O(n)` pass.
			for &v in &self.nodes {
				self.in_cycle[v] = true;
			}
			self.outside.clear();
			for q in 0..n {
				if !self.in_cycle[q] {
					self.outside.push(q);
				}
			}
			for &v in &self.nodes {
				self.in_cycle[v] = false;
			}

			let cycle = &self.nodes;
			let outside = &self.outside;
			if graph.subcircuit {
				// In `subcircuit`, a closed proper subset force every outside node to
				// self-loop.
				let w_in = start;
				let mut reason = Vec::with_capacity(cycle.len() * outside.len() + 1);
				graph.push_no_edge(&mut reason, cycle, outside, None, ctx);
				graph.push_absent(&mut reason, w_in, graph.edge_val(w_in), ctx);
				for &k in &self.outside {
					graph.vars[k].fix(ctx, graph.edge_val(k), reason.clone())?;
				}
			} else {
				// In `circuit`, a closed proper subset is a sub-tour that cannot be completed
				// to a full cycle.
				let mut reason = Vec::with_capacity(cycle.len() * outside.len());
				graph.push_no_edge(&mut reason, cycle, outside, None, ctx);
				return Err(ctx.declare_conflict(reason));
			}
		}
		Ok(())
	}
}

impl<I> CircuitCheck<I> {
	/// Create a new [`CircuitCheck`] propagator.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal, subcircuit: bool) -> Self {
		let n = vars.len();
		Self {
			graph: CircuitGraph::new(vars, offset, subcircuit),
			scratch: CheckScratch::new(n),
			actions_list: Vec::with_capacity(n),
			dirty: false,
		}
	}

	/// Create a new [`CircuitCheck`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>, offset: IntVal, subcircuit: bool)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars, offset, subcircuit)));
	}
}

impl<E, I> Propagator<E> for CircuitCheck<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut <E as ReasoningEngine>::NotificationContext<'_>) {
		self.dirty = true;
		self.actions_list.clear();
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		i: u64,
		_: IntEvent,
	) -> bool {
		self.actions_list.push(i as usize);
		if !self.dirty {
			// Incrementally track the fixed successors of every node, since `check` only
			// reacts to `Fixed` events.
			self.scratch.fixed_succ[i as usize] = self.graph.vars[i as usize]
				.val(ctx)
				.and_then(|v| self.graph.val_to_pos(v));
		} else {
			self.graph
				.fixed_successors(ctx, &mut self.scratch.fixed_succ);
			self.dirty = false;
		}
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// `check` only needs to react when a successor becomes fixed.
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.vars.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		ctx.advise_on_backtrack();
		// Initialize the fixed successors with the currently fixed variables,
		// so we are ready for incremental propagation.
		self.actions_list.extend(0..self.graph.vars.len());
		self.graph
			.fixed_successors(ctx, &mut self.scratch.fixed_succ);
		ctx.enqueue_now(true);
	}

	#[tracing::instrument(
		name = "circuit_check",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		self.scratch
			.run(&self.graph, self.actions_list.drain(..), ctx)
	}
}
