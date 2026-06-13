//! `scc` propagator for the `circuit` / `subcircuit` constraints.
//!
//! One iterative DFS from the lowest-indexed unfixed root that explores the
//! root's children one subtree at a time, firing the strengthening rules as
//! each subtree finishes and failing the moment a closed sub-tour appears.

use crate::{
	IntVal,
	actions::{
		InitActions, IntEvent, IntInspectionActions, IntPropCond, IntPropagationActions,
		PostingActions, PropagationActions, ReasoningEngine,
	},
	constraints::{IntSolverActions, Propagator, circuit::graph::CircuitGraph},
	solver::{engine::Engine, queue::PriorityLevel},
};

/// Reusable scratch for the iterative single-root DFS.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct CircuitDfs {
	/// DFS index of each node; `-1` if unvisited.
	idx: Vec<i64>,
	/// Lowest DFS index reachable from each node.
	low: Vec<i64>,
	/// Root-child block of each node.
	subtree: Vec<usize>,
	/// Exclusive end DFS-index of each node's subtree.
	subtree_hi: Vec<usize>,
	/// Nodes in DFS-visit order.
	order: Vec<usize>,
	/// Shared neighbour buffer; each frame owns the slice `[nbr_start,
	/// nbr_end)`.
	neighbours: Vec<usize>,
	/// Explicit DFS work-stack, replacing native recursion.
	work_stack: Vec<DfsFrame>,
	/// Next DFS index to assign.
	next: usize,
}

/// The `scc` propagator for the `circuit` and `subcircuit` constraints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitScc<I> {
	/// Successor graph plus the shared explanation helpers.
	graph: CircuitGraph<I>,
	/// Reusable scratch for the algorithm.
	scratch: SccScratch,
}

/// One pending node in the DFS work-stack, replacing a native call frame.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct DfsFrame {
	/// Graph node this frame is exploring.
	node: usize,
	/// Start of this frame's neighbour slice in [`CircuitDfs::neighbours`]
	/// (truncated back to here on pop).
	nbr_start: usize,
	/// Exclusive end of this frame's neighbour slice.
	nbr_end: usize,
	/// Next neighbour to visit (the DFS resumption point).
	cursor: usize,
	/// First tree-edge child, for the prune-within rule.
	first_child: Option<usize>,
}

/// Reusable scratch for the `scc` algorithm: the iterative DFS plus the
/// incremental subtree sets the rules reference.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct SccScratch {
	/// The iterative DFS state.
	dfs: CircuitDfs,
	/// Nodes in all subtrees before `prev`.
	earlier: Vec<usize>,
	/// Nodes in the immediately previous root-child subtree.
	prev: Vec<usize>,
	/// Nodes in the subtree just explored.
	this_subtree: Vec<usize>,
	/// Still-unexplored nodes after the current subtree.
	later: Vec<usize>,
	/// Skip arcs found in the current subtree (source, earlier-target).
	skip_edges: Vec<(usize, usize)>,
	/// `(parent, first-child)` prune-within candidates found in the current
	/// subtree.
	within_edges: Vec<(usize, usize)>,
	/// Membership bitset reused when materialising a subtree node-set.
	membership: Vec<bool>,
	/// Root-successor buffer reused by the prune-root scan.
	root_succ: Vec<usize>,
}

impl CircuitDfs {
	/// Allocate scratch sized for an `n`-node support graph.
	fn new(n: usize) -> Self {
		Self {
			idx: vec![-1; n],
			low: vec![0; n],
			subtree: vec![0; n],
			subtree_hi: vec![0; n],
			order: Vec::with_capacity(n),
			neighbours: Vec::new(),
			work_stack: Vec::new(),
			next: 0,
		}
	}

	/// Visit `node` in block `subtree_num`: assign its index/low-link, buffer
	/// its successors, and push a frame.
	fn push<C, I>(&mut self, graph: &CircuitGraph<I>, ctx: &C, node: usize, subtree_num: usize)
	where
		C: PropagationActions,
		I: IntInspectionActions<C>,
	{
		self.idx[node] = self.next as i64;
		self.low[node] = self.next as i64;
		self.subtree[node] = subtree_num;
		self.order.push(node);
		self.next += 1;
		let start = self.neighbours.len();
		graph.scc_successors(ctx, node, &mut self.neighbours);
		let end = self.neighbours.len();
		self.work_stack.push(DfsFrame {
			node,
			nbr_start: start,
			nbr_end: end,
			cursor: start,
			first_child: None,
		});
	}

	/// Reset every per-search array in place, reusing the allocations.
	fn reset(&mut self) {
		self.idx.fill(-1);
		self.low.fill(0);
		self.subtree.fill(0);
		self.subtree_hi.fill(0);
		self.order.clear();
		self.neighbours.clear();
		self.work_stack.clear();
		self.next = 0;
	}
}

impl<I> CircuitScc<I> {
	/// Create a new [`CircuitScc`] propagator.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal, subcircuit: bool) -> Self {
		let n = vars.len();
		Self {
			graph: CircuitGraph::new(vars, offset, subcircuit),
			scratch: SccScratch::new(n),
		}
	}

	/// Create a new [`CircuitScc`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>, offset: IntVal, subcircuit: bool)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars, offset, subcircuit)));
	}
}

impl<E, I> Propagator<E> for CircuitScc<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_int_change(
		&mut self,
		_: &mut E::NotificationContext<'_>,
		_data: u64,
		_event: IntEvent,
	) -> bool {
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Lowest);
		// `scc` reasons about every remaining edge, so it watches any domain change.
		for v in &self.graph.vars {
			v.advise_when(ctx, IntPropCond::Domain, 0);
		}
		ctx.enqueue_now(true);
	}

	#[tracing::instrument(
		name = "circuit_scc",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		self.scratch.run(&self.graph, ctx)
	}
}

impl SccScratch {
	/// Apply the skip-prune rule for every skip arc found in the current
	/// subtree: an arc `c -> a` that jumps over at least one whole subtree
	/// cannot be used.
	fn apply_skip<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
		subtree_num: usize,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.n();
		for si in 0..self.skip_edges.len() {
			let (c, a) = self.skip_edges[si];
			let ta = self.dfs.subtree[a];
			// a_set ≤ ta ; b_set strictly between ta and this subtree ; c_set this
			// subtree and everything still unexplored.
			let a_set = self.blocks(n, |s| s <= ta);
			let b_set = self.blocks(n, |s| s > ta && s < subtree_num);
			let c_set: Vec<usize> = (0..n)
				.filter(|&q| self.dfs.subtree[q] == subtree_num || self.dfs.idx[q] == -1)
				.collect();
			let bc: Vec<usize> = b_set.iter().chain(&c_set).copied().collect();
			let wit = if graph.subcircuit {
				let Some(bw) = b_set.iter().copied().find(|&x| graph.forced_in(ctx, x)) else {
					continue;
				};
				Some(bw)
			} else {
				None
			};
			graph.vars[c].remove_val(ctx, graph.edge_val(a), move |ctx: &mut C| {
				let mut reason = Vec::new();
				if let Some(bw) = wit {
					graph.push_absent(&mut reason, bw, graph.edge_val(bw), ctx);
				}
				graph.push_no_edge(&mut reason, &a_set, &bc, None, ctx);
				graph.push_no_edge(&mut reason, &b_set, &c_set, None, ctx);
				reason
			})?;
		}
		self.skip_edges.clear();
		Ok(())
	}

	/// Apply require-edge / unique-exit for the current subtree: when it has
	/// exactly one back arc to the previous subtree (and no skip arc gives it
	/// another way back), that arc is forced.
	fn apply_unique_exit<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
		root: usize,
		backfrom: usize,
		backto: usize,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		if self.prev.is_empty() {
			// First subtree: its only exit is the back arc to the root.
			let c_set = self.this_subtree.clone();
			let mut outside = self.later.clone();
			outside.push(root);
			let wit = if graph.subcircuit {
				let (Some(bw), Some(cw)) = (
					c_set.iter().copied().find(|&x| graph.forced_in(ctx, x)),
					outside.iter().copied().find(|&x| graph.forced_in(ctx, x)),
				) else {
					return Ok(());
				};
				Some((bw, cw))
			} else {
				None
			};
			graph.vars[backfrom].fix(ctx, graph.edge_val(backto), move |ctx: &mut C| {
				let mut reason = Vec::new();
				if let Some((bw, cw)) = wit {
					graph.push_absent(&mut reason, bw, graph.edge_val(bw), ctx);
					graph.push_absent(&mut reason, cw, graph.edge_val(cw), ctx);
				}
				graph.push_no_edge(&mut reason, &c_set, &outside, Some((backfrom, backto)), ctx);
				reason
			})?;
			return Ok(());
		}
		// Subtrees A (earlier), B (prev), C (this), D (later).
		let a_set = self.earlier.clone();
		let b_set = self.prev.clone();
		let c_set = self.this_subtree.clone();
		let d_set = self.later.clone();
		let bcd: Vec<usize> = b_set.iter().chain(&c_set).chain(&d_set).copied().collect();
		let cd: Vec<usize> = c_set.iter().chain(&d_set).copied().collect();
		let bd: Vec<usize> = b_set.iter().chain(&d_set).copied().collect();
		let wit = if graph.subcircuit {
			let (Some(p), Some(q)) = (
				b_set.iter().copied().find(|&x| graph.forced_in(ctx, x)),
				c_set.iter().copied().find(|&x| graph.forced_in(ctx, x)),
			) else {
				return Ok(());
			};
			Some((p, q))
		} else {
			None
		};
		graph.vars[backfrom].fix(ctx, graph.edge_val(backto), move |ctx: &mut C| {
			let mut reason = Vec::new();
			if let Some((p, q)) = wit {
				graph.push_absent(&mut reason, p, graph.edge_val(p), ctx);
				graph.push_absent(&mut reason, q, graph.edge_val(q), ctx);
			}
			graph.push_no_edge(&mut reason, &a_set, &bcd, None, ctx);
			graph.push_no_edge(&mut reason, &b_set, &cd, None, ctx);
			graph.push_no_edge(&mut reason, &c_set, &bd, Some((backfrom, backto)), ctx);
			reason
		})?;
		Ok(())
	}

	/// Apply the prune-within rule for every candidate found in the current
	/// subtree. The child subtree's only link upward is its parent `p`, so the
	/// parent cannot enter it (`p -> c`) and no node outside the subtree may
	/// enter the parent (`o -> p`).
	fn apply_within<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.n();
		for wi in 0..self.within_edges.len() {
			let (p, c) = self.within_edges[wi];
			let lo = self.dfs.idx[c] as usize;
			let hi = self.dfs.subtree_hi[c];
			let c_set: Vec<usize> = self.dfs.order[lo..hi].to_vec();
			self.membership.fill(false);
			for &node in &c_set {
				self.membership[node] = true;
			}
			let a_set: Vec<usize> = (0..n).filter(|&q| !self.membership[q] && q != p).collect();
			let wit = if graph.subcircuit {
				let (Some(aw), Some(bw)) = (
					a_set.iter().copied().find(|&x| graph.forced_in(ctx, x)),
					c_set.iter().copied().find(|&x| graph.forced_in(ctx, x)),
				) else {
					continue;
				};
				Some((aw, bw))
			} else {
				None
			};
			// `c_set` reaches nothing outside but `p`, so one reason justifies pruning
			// both the down edge `p -> c` and every incoming edge `o -> p`. Build it once
			// and reuse it across all prunes (Chuffed shares the same clause).
			let mut reason = Vec::new();
			if let Some((aw, bw)) = wit {
				graph.push_absent(&mut reason, aw, graph.edge_val(aw), ctx);
				graph.push_absent(&mut reason, bw, graph.edge_val(bw), ctx);
			}
			graph.push_no_edge(&mut reason, &c_set, &a_set, None, ctx);
			if graph.vars[p].in_domain(ctx, graph.edge_val(c)) {
				graph.vars[p].remove_val(ctx, graph.edge_val(c), reason.clone())?;
			}
			// The strengthened incoming prune holds for `circuit` only: in
			// `subcircuit` an outside node may still enter `p` when `c_set` is excluded.
			if !graph.subcircuit {
				let pv = graph.edge_val(p);
				for &o in &a_set {
					if graph.vars[o].in_domain(ctx, pv) {
						graph.vars[o].remove_val(ctx, pv, reason.clone())?;
					}
				}
			}
		}
		self.within_edges.clear();
		Ok(())
	}

	/// Materialise the union of root-child subtrees whose block number
	/// satisfies `pred` (the root is always excluded).
	fn blocks(&self, n: usize, pred: impl Fn(usize) -> bool) -> Vec<usize> {
		(0..n)
			.filter(|&q| self.dfs.subtree[q] >= 1 && pred(self.dfs.subtree[q]))
			.collect()
	}

	/// If the subtree rooted at `v` is closed (and, for `subcircuit`, separates
	/// a forced-in node on each side), return the conflict that rejects it.
	fn closed_conflict<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
		v: usize,
	) -> Option<C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.n();
		let lo = self.dfs.idx[v] as usize;
		let hi = self.dfs.subtree_hi[v];
		let inside: Vec<usize> = self.dfs.order[lo..hi].to_vec();
		self.membership.fill(false);
		for &node in &inside {
			self.membership[node] = true;
		}
		let outside: Vec<usize> = (0..n).filter(|&q| !self.membership[q]).collect();
		let mut reason = Vec::new();
		if graph.subcircuit {
			// Only a contradiction if a forced-in node lies on each side.
			let (Some(w_in), Some(w_out)) = (
				inside.iter().copied().find(|&q| graph.forced_in(ctx, q)),
				outside.iter().copied().find(|&q| graph.forced_in(ctx, q)),
			) else {
				return None;
			};
			graph.push_absent(&mut reason, w_in, graph.edge_val(w_in), ctx);
			graph.push_absent(&mut reason, w_out, graph.edge_val(w_out), ctx);
		}
		graph.push_no_edge(&mut reason, &inside, &outside, None, ctx);
		Some(ctx.declare_conflict(reason))
	}

	/// Iteratively explore one root-child subtree rooted at `child`.
	/// Records the skip / prune-within candidates, counts the
	/// back arcs to the previous subtree `[prev_lo, prev_hi]`, and fails
	/// immediately on a closed sub-tour.
	fn explore_subtree<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
		child: usize,
		prev_lo: usize,
		prev_hi: usize,
		subtree_num: usize,
	) -> Result<(usize, usize, usize), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let mut numback = 0_usize;
		let mut backfrom = 0_usize;
		let mut backto = 0_usize;

		self.dfs.push(graph, ctx, child, subtree_num);
		while let Some(&DfsFrame {
			node,
			nbr_end,
			cursor,
			first_child,
			..
		}) = self.dfs.work_stack.last()
		{
			if cursor < nbr_end {
				// When there are still neighbours to visit, visit the next one.
				let w = self.dfs.neighbours[cursor];
				self.dfs.work_stack.last_mut().unwrap().cursor += 1;
				let iw = self.dfs.idx[w];
				if iw != -1 {
					// Visited neighbour: classify the arc, then fold its index into
					// the low-link.
					let iw = iw as usize;
					if iw >= prev_lo && iw <= prev_hi {
						// Back arc to the previous subtree (the root for the first one).
						numback += 1;
						backfrom = node;
						backto = w;
					} else if iw < prev_lo {
						// Arc to an earlier subtree (or the root for `t >= 2`): a skip arc.
						self.skip_edges.push((node, w));
					}
					if (iw as i64) < self.dfs.low[node] {
						self.dfs.low[node] = iw as i64;
					}
				} else {
					// Tree edge: a child in the same subtree block.
					if first_child.is_none() {
						self.dfs.work_stack.last_mut().unwrap().first_child = Some(w);
					}
					self.dfs.push(graph, ctx, w, subtree_num);
				}
			} else {
				// When all neighbours have been visited, check pruning rules.
				let frame = self.dfs.work_stack.pop().unwrap();
				self.dfs.neighbours.truncate(frame.nbr_start);
				self.dfs.subtree_hi[frame.node] = self.dfs.next;

				// prune-within: the first child's subtree reaches nothing above its
				// parent (`low[c] >= idx[parent]`).
				if let Some(c) = frame.first_child
					&& self.dfs.low[c] >= self.dfs.idx[frame.node]
				{
					self.within_edges.push((frame.node, c));
				}

				// Discovered a subtour and check conflict / pruning reasons for it.
				if self.dfs.low[frame.node] == self.dfs.idx[frame.node]
					&& let Some(conflict) = self.closed_conflict(graph, ctx, frame.node)
				{
					return Err(conflict);
				}

				// Fold this node's low-link into its parent (the post-recursion update).
				if let Some(parent) = self.dfs.work_stack.last() {
					let p = parent.node;
					if self.dfs.low[frame.node] < self.dfs.low[p] {
						self.dfs.low[p] = self.dfs.low[frame.node];
					}
				}
			}
		}

		Ok((numback, backfrom, backto))
	}

	/// Allocate scratch sized for an `n`-node support graph.
	pub(crate) fn new(n: usize) -> Self {
		Self {
			dfs: CircuitDfs::new(n),
			earlier: Vec::new(),
			prev: Vec::new(),
			this_subtree: Vec::new(),
			later: Vec::new(),
			skip_edges: Vec::new(),
			within_edges: Vec::new(),
			membership: vec![false; n],
			root_succ: Vec::new(),
		}
	}

	/// `scc`: one iterative DFS from the first unfixed root that explores the
	/// root's children one subtree at a time. As each subtree finishes it fires
	/// the four arc-level rules and fails the moment a closed sub-tour
	/// appears:
	///
	/// 1. **require-edge / unique-exit**: a subtree with exactly one back arc
	///    to its predecessor must use it.
	/// 2. **skip-prune**: an arc skipping ≥1 whole subtree cannot be used.
	/// 3. **prune-root**: the root may only enter the *last* subtree.
	/// 4. **prune-within**: a first child whose subtree reaches nothing above
	///    its parent cannot be entered through that parent, and the parent
	///    cannot be entered from outside the subtree.
	///
	/// The rules are non-monotonic (they depend on the chosen root), so reasons
	/// can be non-asserting — sound on CaDiCaL 3.0, which recomputes the
	/// backjump level; only each reason's validity matters.
	pub(crate) fn run<C, I>(
		&mut self,
		graph: &CircuitGraph<I>,
		ctx: &mut C,
	) -> Result<(), C::Conflict>
	where
		C: PropagationActions,
		I: IntPropagationActions<C>,
	{
		let n = graph.n();
		if n < 2 {
			return Ok(());
		}
		// Choose the first unfixed root as the DFS root
		let Some(root) = (0..graph.n()).find(|&i| graph.vars[i].val(ctx).is_none()) else {
			return Ok(());
		};

		self.dfs.reset();
		self.earlier.clear();
		self.prev.clear();
		self.skip_edges.clear();
		self.within_edges.clear();

		// The root is its own (block 0) node.
		// The first subtree's "previous" range is the single root index.
		self.dfs.idx[root] = 0;
		self.dfs.low[root] = 0;
		self.dfs.order.push(root);
		self.dfs.next = 1;
		let mut prev_lo = 0;
		let mut prev_hi = 0;
		let mut k = 0_usize;

		self.root_succ.clear();
		graph.scc_successors(ctx, root, &mut self.root_succ);
		for ri in 0..self.root_succ.len() {
			let child = self.root_succ[ri];
			if self.dfs.idx[child] != -1 {
				continue;
			}
			k += 1;
			let start_this = self.dfs.next;
			let (numback, backfrom, backto) =
				self.explore_subtree(graph, ctx, child, prev_lo, prev_hi, k)?;

			// Snapshot the subtree just explored and the still-unexplored nodes.
			self.this_subtree.clear();
			self.this_subtree
				.extend_from_slice(&self.dfs.order[start_this..self.dfs.next]);
			self.later.clear();
			self.later.extend((0..n).filter(|&q| self.dfs.idx[q] == -1));

			// Fire the per-subtree rules.
			let had_skip = !self.skip_edges.is_empty();
			self.apply_skip(graph, ctx, k)?;
			self.apply_within(graph, ctx)?;
			if !had_skip && numback == 1 {
				self.apply_unique_exit(graph, ctx, root, backfrom, backto)?;
			}

			// Advance the incremental window: prev becomes this subtree.
			let prev = std::mem::take(&mut self.prev);
			self.earlier.extend(prev);
			self.prev.clear();
			self.prev.extend_from_slice(&self.this_subtree);
			prev_lo = start_this;
			prev_hi = self.dfs.next - 1;
		}

		// Disconnection: an unreached node means the reached set is closed.
		if self.dfs.next < n {
			let reached: Vec<usize> = self.dfs.order.clone();
			let unreached: Vec<usize> = (0..n).filter(|&q| self.dfs.idx[q] == -1).collect();
			if !graph.subcircuit {
				let mut reason = Vec::new();
				graph.push_no_edge(&mut reason, &reached, &unreached, None, ctx);
				return Err(ctx.declare_conflict(reason));
			}
			// `subcircuit`: if a reached node must lie on the cycle, every unreached
			// node is off it and must self-loop. The reason is shared, so build once.
			if let Some(w_in) = reached.iter().copied().find(|&q| graph.forced_in(ctx, q)) {
				let mut reason = Vec::new();
				graph.push_absent(&mut reason, w_in, graph.edge_val(w_in), ctx);
				graph.push_no_edge(&mut reason, &reached, &unreached, None, ctx);
				// `fix` is sound when redundant and fails when the self-loop is absent
				// (an unreached forced-in node ⇒ a genuine conflict), so do not gate it.
				for &u in &unreached {
					graph.vars[u].fix(ctx, graph.edge_val(u), reason.clone())?;
				}
			}
			return Ok(());
		}

		// Prune-root: with ≥2 subtrees the root may only enter the last one. The
		// witness and reason are the same for every pruned root edge, so build once.
		if k >= 2 {
			let e_set = self.blocks(n, |s| s < k);
			let l_set = self.blocks(n, |s| s == k);
			let wit = if graph.subcircuit {
				match l_set.iter().copied().find(|&x| graph.forced_in(ctx, x)) {
					Some(l) => Some(l),
					None => return Ok(()), // no forced-in node in the last subtree ⇒ inapplicable
				}
			} else {
				None
			};
			let mut reason = Vec::new();
			if let Some(l) = wit {
				graph.push_absent(&mut reason, l, graph.edge_val(l), ctx);
			}
			graph.push_no_edge(&mut reason, &e_set, &l_set, None, ctx);
			self.root_succ.clear();
			graph.scc_successors(ctx, root, &mut self.root_succ);
			for ri in 0..self.root_succ.len() {
				let e = self.root_succ[ri];
				if self.dfs.subtree[e] == 0 || self.dfs.subtree[e] == k {
					continue; // root self-arc or already into the last subtree
				}
				let ev = graph.edge_val(e);
				if graph.vars[root].in_domain(ctx, ev) {
					graph.vars[root].remove_val(ctx, ev, reason.clone())?;
				}
			}
		}

		Ok(())
	}
}
