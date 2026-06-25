//! `no_cycle` propagator for the `circuit` / `subcircuit` constraints.
//!
//! Prevents a premature cycle from forming as successor arcs are fixed. Walking
//! each maximal fixed successor chain once classifies it as either:
//!
//! - *open* (`a ... z` with `z`'s successor still unfixed): forbid its closing
//!   edge `z -> a`, or
//! - *closed* (a sub-tour `a ... a` that does not span every node): fail in
//!   `circuit`, or force every node outside the sub-tour to self-loop in
//!   `subcircuit`.

use crate::{
	IntVal,
	actions::{
		InitActions, IntEvent, IntInspectionActions, IntPropCond, IntPropagationActions,
		PostingActions, PropagationActions, ReasoningEngine,
	},
	constraints::{IntSolverActions, Propagator, circuit::CircuitGraph},
	solver::{engine::Engine, queue::PriorityLevel},
};

/// The `no_cycle` propagator for the `circuit` and `subcircuit` constraints
/// (`SUBCIRCUIT` selects the variant).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitNoCycle<const SUBCIRCUIT: bool, I> {
	/// Successor graph plus the shared explanation helpers (the canonical copy
	/// for the owning `Circuit`).
	pub(crate) graph: CircuitGraph<SUBCIRCUIT, I>,
	/// Reusable scratch for the algorithm.
	scratch: NoCycleScratch,
	/// Recently fixed variables.
	actions_list: Vec<usize>,
	/// Whether the incremental successor state needs a full refresh.
	dirty: bool,
}

/// Reusable scratch for the `no_cycle` algorithm.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct NoCycleScratch {
	/// Successor position of every fixed node (`None` if unfixed).
	fixed_succ: Vec<Option<usize>>,
	/// Fixed predecessor of every node, used to walk back to a chain's start.
	fixed_pred: Vec<Option<usize>>,
	/// Nodes already assigned to a scanned chain this round.
	visited: Vec<bool>,
	/// The current fixed chain/cycle, in visit order, reused across starts.
	nodes: Vec<usize>,
	/// The complement of the current closed sub-tour (built only when one
	/// closes, to resolve it).
	outside: Vec<usize>,
	/// Membership of the current closed sub-tour over `0..n`, kept clean
	/// between sub-tours so the complement is one `O(n)` pass, not
	/// `O(n·|cycle|)` linear `contains`.
	in_cycle: Vec<bool>,
}

impl<const SUBCIRCUIT: bool, I> CircuitNoCycle<SUBCIRCUIT, I> {
	/// Create a new [`CircuitNoCycle`] propagator.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal) -> Self {
		let n = vars.len();
		Self {
			graph: CircuitGraph::new(vars, offset),
			scratch: NoCycleScratch::new(n),
			actions_list: Vec::with_capacity(n),
			dirty: false,
		}
	}

	/// Create a new [`CircuitNoCycle`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>, offset: IntVal)
	where
		E: PostingActions + ?Sized,
		I: IntInspectionActions<E> + IntSolverActions<Engine>,
	{
		// The domain bounds for variables should exclude out-of-range values
		// that would otherwise satisfy the constraint without forming a valid cycle.
		let max_node = offset + vars.len() as IntVal - 1;
		assert!(
			vars.iter()
				.all(|v| v.min(solver) >= offset && v.max(solver) <= max_node),
			"variables' domains must exclude out-of-range values"
		);
		solver.add_propagator(Box::new(Self::new(vars, offset)));
	}
}

impl<const SUBCIRCUIT: bool, E, I> Propagator<E> for CircuitNoCycle<SUBCIRCUIT, I>
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
		// The incremental state is only updated if not dirty.
		if !self.dirty {
			let succ = self.graph.vars[i]
				.val(ctx)
				.and_then(|v| self.graph.val_to_pos(v));
			self.scratch.fixed_succ[i] = succ;
			if let Some(j) = succ {
				self.scratch.fixed_pred[j] = Some(i);
			}
		}
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// `no_cycle` only needs to react when a successor becomes fixed.
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.vars.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		ctx.advise_on_backtrack();
		self.graph
			.fixed_successors(ctx, &mut self.scratch.fixed_succ);
		self.scratch.rebuild_chain();

		// Enqueue the first propagation if any successors are already fixed.
		self.actions_list.clear();
		self.actions_list
			.extend((0..self.graph.vars.len()).filter(|&i| self.scratch.fixed_succ[i].is_some()));
		ctx.enqueue_now(!self.actions_list.is_empty());
	}

	#[tracing::instrument(
		name = "circuit_no_cycle",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let Self {
			graph,
			scratch,
			actions_list,
			dirty,
		} = self;
		// Lazily refresh the incremental state on the first propagate after a
		// backtrack.
		if *dirty {
			graph.fixed_successors(ctx, &mut scratch.fixed_succ);
			scratch.rebuild_chain();
			*dirty = false;
		}

		let n = graph.vars.len();
		scratch.visited.fill(false);
		for action in actions_list.drain(..) {
			// `action` only enters the list on a `Fixed` event.
			debug_assert!(
				scratch.fixed_succ[action].is_some(),
				"no_cycle actioned an unfixed node"
			);

			// Backward walk to the chain start.
			let mut start = action;
			for _ in 0..n {
				match scratch.fixed_pred[start] {
					Some(p) => start = p,
					None => break,
				}
			}
			if scratch.visited[start] {
				continue;
			}

			// Forward walk the fixed chain from `start`, collecting its nodes and
			// detecting whether the tour is closed.
			scratch.nodes.clear();
			scratch.nodes.push(start);
			scratch.visited[start] = true;
			let mut node = start;
			let mut closed = false;
			let end = loop {
				let succ = scratch.fixed_succ[node].unwrap();
				if succ == start {
					closed = true;
					break node;
				}
				scratch.nodes.push(succ);
				scratch.visited[succ] = true;
				if scratch.fixed_succ[succ].is_none() {
					break succ;
				}
				node = succ;
				if scratch.nodes.len() > n {
					closed = true;
					break node;
				}
			};

			// Skip for the complete (sub)circuit.
			if scratch.nodes.len() >= n {
				continue;
			}

			if closed {
				scratch.resolve_subtour(graph, start, ctx)?;
			} else {
				scratch.prevent_close(graph, start, end, ctx)?;
			}
		}
		Ok(())
	}
}

impl NoCycleScratch {
	/// Allocate scratch sized for an `n`-node support graph.
	pub(crate) fn new(n: usize) -> Self {
		Self {
			fixed_succ: vec![None; n],
			fixed_pred: vec![None; n],
			visited: vec![false; n],
			nodes: Vec::new(),
			outside: Vec::new(),
			in_cycle: vec![false; n],
		}
	}

	/// Forbid the closing edge `end -> start` of the open fixed chain held in
	/// `self.nodes`, whose interior nodes (`start ... end`) are all fixed.
	fn prevent_close<const SUBCIRCUIT: bool, C, I>(
		&mut self,
		graph: &CircuitGraph<SUBCIRCUIT, I>,
		start: usize,
		end: usize,
		ctx: &mut C,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.vars.len();
		// In `subcircuit` the prune is sound only with a forced-in node outside
		// the chain (witness that the chain must lie on a real cycle).
		let witness = if SUBCIRCUIT {
			match (0..n).find(|&k| {
				!self.nodes.contains(&k) && !graph.vars[k].in_domain(ctx, graph.edge_val(k))
			}) {
				Some(k) => Some(k),
				None => return Ok(()),
			}
		} else {
			None
		};

		let nodes = &self.nodes;
		graph.vars[end].remove_val(ctx, graph.edge_val(start), |ctx: &mut C| {
			let mut reason = Vec::with_capacity(2 * nodes.len() + 1);
			for &i in nodes {
				if i != end {
					// Every interior node of the chain is fixed, so its value literal exists.
					reason.push(graph.vars[i].val_lit(ctx).unwrap());
				}
			}
			if let Some(k) = witness {
				graph.push_forced_in(&mut reason, k, ctx);
			}
			reason
		})?;
		Ok(())
	}

	/// Rebuild `fixed_pred` from `fixed_succ` after a full successor refresh.
	fn rebuild_chain(&mut self) {
		self.fixed_pred.fill(None);
		for i in 0..self.fixed_succ.len() {
			if let Some(j) = self.fixed_succ[i] {
				self.fixed_pred[j] = Some(i);
			}
		}
	}

	/// The nodes in `self.nodes` form a closed sub-tour over a proper subset of
	/// the graph:
	/// - In `circuit` this is an unsatisfiable sub-tour;
	/// - In `subcircuit` it is the unique real cycle, forcing every outside
	///   node to self-loop.
	fn resolve_subtour<const SUBCIRCUIT: bool, C, I>(
		&mut self,
		graph: &CircuitGraph<SUBCIRCUIT, I>,
		start: usize,
		ctx: &mut C,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		// In `subcircuit`, a self-loop (length-1 cycle) marks an excluded node.
		if SUBCIRCUIT && self.nodes.len() == 1 {
			return Ok(());
		}

		// Build the complement of the closed sub-tour in one `O(n)` pass.
		let n = graph.vars.len();
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
		if SUBCIRCUIT {
			// `subcircuit`: every outside node is excluded and must self-loop.
			let w_in = start;
			let mut reason = Vec::with_capacity(cycle.len() * outside.len() + 1);
			graph.push_no_edge(&mut reason, cycle, outside, None, ctx);
			graph.push_forced_in(&mut reason, w_in, ctx);
			for &k in outside {
				graph.vars[k].fix(ctx, graph.edge_val(k), reason.clone())?;
			}
		} else {
			// `circuit`: raise conflict for a closed proper sub-tour.
			let mut reason = Vec::with_capacity(cycle.len() * outside.len());
			graph.push_no_edge(&mut reason, cycle, outside, None, ctx);
			return Err(ctx.declare_conflict(reason));
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		actions::{IntDecisionActions, IntInspectionActions},
		constraints::circuit::CircuitNoCycle,
		solver::{IntLitMeaning, LiteralStrategy, Solver, View as SolverView},
	};

	/// Build one successor decision with eager literals, so the exact
	/// propagated literals are observable.
	fn succ_decision(slv: &mut Solver, dom: IntSet) -> SolverView<IntVal> {
		slv.new_int_decision(dom)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view()
	}

	/// Build successor decisions (1-based values) from contiguous domains.
	fn succ_vars(
		slv: &mut Solver,
		doms: &[std::ops::RangeInclusive<IntVal>],
	) -> Vec<SolverView<IntVal>> {
		doms.iter()
			.map(|d| succ_decision(slv, IntSet::from_iter([d.clone()])))
			.collect()
	}

	/// Regression test: a closed sub-tour of length < n is a conflict for
	/// `circuit`.
	#[test]
	#[traced_test]
	fn test_no_cycle_detects_subtour() {
		let mut slv = Solver::default();
		let vars = succ_vars(&mut slv, &[2..=2, 1..=1, 1..=3]); // 0->1, 1->0, 2 free
		CircuitNoCycle::<false, _>::post(&mut slv, vars, 1);
		assert!(
			slv.propagate_next().is_err(),
			"no_cycle should fail on the 0<->1 sub-tour"
		);
	}

	/// Regression test: `post` requires the caller to have already narrowed
	/// every successor to the node range `[offset, offset + n - 1]`.
	#[test]
	#[should_panic(expected = "domains must exclude out-of-range values")]
	fn test_no_cycle_post_rejects_out_of_range_successor() {
		let mut slv = Solver::default();
		let vars = succ_vars(&mut slv, &[0..=3, 1..=3, 1..=3]);
		CircuitNoCycle::<false, _>::post(&mut slv, vars, 1);
	}

	/// Regression test: `no_cycle` forbids the closing edge of an open fixed
	/// chain.
	#[test]
	#[traced_test]
	fn test_no_cycle_removes_chain_closing_edge() {
		let mut slv = Solver::default();
		// 0->1 (val 2), 1->2 (val 3), 2 and 3 free.
		let vars = succ_vars(&mut slv, &[2..=2, 3..=3, 1..=4, 1..=4]);
		let s2 = vars[2];
		CircuitNoCycle::<false, _>::post(&mut slv, vars, 1);
		let propagated = slv
			.propagate_next()
			.expect("no_cycle must not conflict here");
		let forbid = s2.lit(&mut slv, IntLitMeaning::NotEq(1)); // succ[2] != node 0
		assert!(
			propagated.contains(&forbid),
			"no_cycle should forbid closing the chain (succ[2] != 1); got {propagated:?}"
		);
		assert!(
			!s2.in_domain(&slv, 1),
			"value 1 should be pruned from succ[2]"
		);
	}

	/// Regression test: a closed sub-tour of length < n is a conflict for
	/// `circuit`, but valid for `subcircuit`.
	#[test]
	#[traced_test]
	fn test_subcircuit_no_cycle_allows_valid_subtour() {
		let mut slv = Solver::default();
		let vars = succ_vars(&mut slv, &[2..=2, 1..=1, 1..=3]); // 0->1, 1->0, 2 free
		let s2 = vars[2];
		CircuitNoCycle::<true, _>::post(&mut slv, vars, 1);
		assert!(
			slv.propagate_next().is_ok(),
			"subcircuit no_cycle must accept the valid {{0,1}} sub-tour"
		);
		// Node 2 lies outside the {0,1} sub-tour, so it is forced to self-loop.
		assert!(
			!s2.in_domain(&slv, 1) && !s2.in_domain(&slv, 2),
			"node 2 outside the sub-tour must be forced to self-loop (succ[2] = 3)"
		);
	}
}
