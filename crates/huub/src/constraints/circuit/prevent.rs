//! `prevent` propagator for the `circuit` / `subcircuit` constraints.
//!
//! For every maximal fixed chain `a ... z`, forbids the closing edge `z → a`
//! Closing it early would form a sub-tour.

use crate::{
	IntVal,
	actions::{
		InitActions, IntEvent, IntPropCond, IntPropagationActions, PostingActions,
		PropagationActions, ReasoningEngine,
	},
	constraints::{IntSolverActions, Propagator, circuit::graph::CircuitGraph},
	solver::{engine::Engine, queue::PriorityLevel},
};

/// The `prevent` propagator for the `circuit` and `subcircuit` constraints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitPrevent<I> {
	/// Successor graph plus the shared explanation helpers.
	graph: CircuitGraph<I>,
	/// Reusable scratch for the algorithm.
	scratch: PreventScratch,
	/// Recently fixed variables.
	actions_list: Vec<usize>,
	/// Whether the incremental successor state needs a full refresh.
	dirty: bool,
}

/// Reusable scratch for the `prevent` algorithm.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PreventScratch {
	/// Successor position of every fixed node (`None` if unfixed).
	fixed_succ: Vec<Option<usize>>,
	/// Fixed predecessor of every node, used to walk back to a chain's start.
	fixed_pred: Vec<Option<usize>>,
	/// Chain starts already handled this round.
	visited: Vec<bool>,
	/// The current chain, reused across starts.
	nodes: Vec<usize>,
}

impl<I> CircuitPrevent<I> {
	/// Create a new [`CircuitPrevent`] propagator.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal, subcircuit: bool) -> Self {
		let n = vars.len();
		Self {
			graph: CircuitGraph::new(vars, offset, subcircuit),
			scratch: PreventScratch::new(n),
			actions_list: Vec::with_capacity(n),
			dirty: false,
		}
	}

	/// Create a new [`CircuitPrevent`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>, offset: IntVal, subcircuit: bool)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars, offset, subcircuit)));
	}
}

impl<E, I> Propagator<E> for CircuitPrevent<I>
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
		let i = i as usize;
		self.actions_list.push(i);
		if !self.dirty {
			let succ = self.graph.vars[i]
				.val(ctx)
				.and_then(|v| self.graph.val_to_pos(v));
			self.scratch.fixed_succ[i] = succ;
			if let Some(j) = succ {
				self.scratch.fixed_pred[j] = Some(i);
			}
		} else {
			self.graph
				.fixed_successors(ctx, &mut self.scratch.fixed_succ);
			self.scratch.rebuild_pred();
			self.dirty = false;
		}
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// `prevent` only needs to react when a successor becomes fixed.
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.vars.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		ctx.advise_on_backtrack();
		self.actions_list.extend(0..self.graph.vars.len());
		self.graph
			.fixed_successors(ctx, &mut self.scratch.fixed_succ);
		self.scratch.rebuild_pred();
		ctx.enqueue_now(true);
	}

	#[tracing::instrument(
		name = "circuit_prevent",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		self.scratch
			.run(&self.graph, self.actions_list.drain(..), ctx)
	}
}

impl PreventScratch {
	/// Allocate scratch sized for an `n`-node support graph.
	pub(crate) fn new(n: usize) -> Self {
		Self {
			fixed_succ: vec![None; n],
			fixed_pred: vec![None; n],
			visited: vec![false; n],
			nodes: Vec::new(),
		}
	}

	/// Rebuild `fixed_pred` from `fixed_succ` after a full successor refresh.
	fn rebuild_pred(&mut self) {
		self.fixed_pred.fill(None);
		for i in 0..self.fixed_succ.len() {
			if let Some(j) = self.fixed_succ[i] {
				self.fixed_pred[j] = Some(i);
			}
		}
	}

	/// `prevent`: for the chain of each newly fixed node, forbid the closing
	/// edge `z → a` of its maximal fixed chain `a … z` unless the chain spans
	/// all nodes.
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

		for action in action_list {
			if self.fixed_succ[action].is_none() {
				continue;
			}
			// Walk back to the chain start. A walk that never reaches an unfixed
			// predecessor is a closed cycle (handled by `check`), with nothing to forbid.
			let mut start = action;
			for _ in 0..n {
				match self.fixed_pred[start] {
					Some(p) => start = p,
					None => break,
				}
			}
			if self.fixed_pred[start].is_some() || self.visited[start] {
				continue;
			}
			self.visited[start] = true;

			self.nodes.clear();
			self.nodes.push(start);
			let mut node = start;
			let mut full_cycle = false;
			let end = loop {
				let succ = self.fixed_succ[node].unwrap();
				if succ == start {
					full_cycle = true;
					break node;
				}
				self.nodes.push(succ);
				if self.fixed_succ[succ].is_none() {
					break succ;
				}
				node = succ;
				if self.nodes.len() > n {
					full_cycle = true;
					break node;
				}
			};

			if full_cycle || self.nodes.len() >= n {
				continue;
			}

			// In `subcircuit` the prune is sound only with a forced-in node outside
			// the chain (witness that the chain must lie on a real cycle); this also
			// gates whether the prune applies, so it is computed eagerly.
			let witness = if graph.subcircuit {
				match (0..n).find(|&k| {
					!self.nodes.contains(&k) && !graph.vars[k].in_domain(ctx, graph.edge_val(k))
				}) {
					Some(k) => Some(k),
					None => continue,
				}
			} else {
				None
			};
			// Build the reason lazily — it is only needed if the edge is still live.
			// The chain is fixed, so `end` cannot also close back to `start`; explain
			// the fixed nodes with their bound literals.
			let nodes = &self.nodes;
			graph.vars[end].remove_val(ctx, graph.edge_val(start), |ctx: &mut C| {
				let mut reason = Vec::with_capacity(2 * nodes.len() + 1);
				for &i in nodes {
					if i != end {
						graph.push_fixed(&mut reason, i, ctx);
					}
				}
				if let Some(k) = witness {
					graph.push_absent(&mut reason, k, graph.edge_val(k), ctx);
				}
				reason
			})?;
		}
		Ok(())
	}
}
