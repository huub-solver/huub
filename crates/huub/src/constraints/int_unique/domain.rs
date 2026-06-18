//! Domain-consistent propagator for the integer `unique` constraint.
//! The public algorithm overview and references live on
//! [`IntUniqueDomain`]; this module file contains the propagator and its
//! private graph/matching/Tarjan helpers.

use std::{cmp, mem, ops::Range};

use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;
use tracing::trace;

use crate::{
	Conjunction, IntVal,
	actions::{
		InitActions, IntEvent, IntInspectionActions, IntPropCond, PostingActions,
		PropagationActions, ReasoningContext, ReasoningEngine,
	},
	constraints::{IntSolverActions, Propagator},
	helpers::trailed_partition::TrailedPartition,
	solver::{IntLitMeaning, engine::Engine, queue::PriorityLevel},
};

/// Reusable scratch for BFS-based augmenting-path search on a bipartite
/// graph. Depends only on the number of left nodes.
#[derive(Clone, Debug)]
struct AugmentingPathScratch {
	/// BFS queue (over left nodes).
	queue: Vec<usize>,
	/// Per-left-node BFS parent pointer; `usize::MAX` means "no parent /
	/// root / not yet visited".
	parent: Vec<usize>,
}

/// Reusable scratch for the explain-time down-closure.
#[derive(Clone, Debug)]
struct ClosureScratch {
	/// Decision members `H` of the tight Hall set. Membership is marked in
	/// [`Self::dcn_in`]; the list lets the marks be cleared in O(closure).
	dcns: Vec<usize>,
	/// Value set `V` of the tight Hall set (marked in [`Self::val_in`]).
	vals: Vec<usize>,
	/// `dcn_in[v]` is `true` while decision `v` is in the down-closure being
	/// built (a re-entrancy-free dedup bitset).
	dcn_in: Vec<bool>,
	/// `val_in[i]` is `true` while value index `i` is in the down-closure.
	val_in: Vec<bool>,
}

/// The bipartite "decision <-> value" graph that Régin's algorithm operates on,
/// together with the current maximum matching between the two sides.
///
/// All decision/value bookkeeping lives here: the decision list, the
/// union-domain origin used to translate between integer values and right-side
/// indices, and the matching tables. Algorithms (augmenting-path search,
/// Tarjan, Hall-set reasoning) operate on this struct from the outside.
#[derive(Clone, Debug)]
struct DecisionValueMatching<I> {
	/// Left side: the integer decision variables.
	dcns: Vec<I>,
	/// Lower bound of the union of all initial decision domains. The
	/// right-side index `r` represents the integer value
	/// `union_domain_lb + r`, for `r` in `0..n_values()`.
	union_domain_lb: IntVal,
	/// Matching: decision index -> value index.
	dcn_to_val: Vec<Option<usize>>,
	/// Matching: value index -> decision index. Sized at construction time to
	/// the size of the union of initial decision domains.
	val_to_dcn: Vec<Option<usize>>,
}

/// Domain-consistent propagator for the integer `unique` constraint.
///
/// Implements Régin's bipartite-matching + Tarjan SCC algorithm (AAAI 1994):
/// maintain a maximum matching from decisions to values, repair it with
/// BFS-augmenting paths after domain changes, then run Tarjan's SCC on the
/// residual bipartite graph (with a single dummy node fanning out free
/// values so the residual graph stays linear in size) and remove any value
/// from a decision's domain whenever the decision and value land in
/// different SCCs.
///
/// **References**
///
/// - Régin, Jean-Charles. "A filtering algorithm for constraints of difference
///   in CSPs." AAAI 94 (1994): 362-367.
/// - Gent, Ian P., Ian Miguel, and Peter Nightingale. "Generalised arc
///   consistency for the AllDifferent constraint: An empirical survey."
///   Artificial Intelligence 172.18 (2008): 1973-2000.
/// - Downing, Nicholas, Thibaut Feydy, and Peter J. Stuckey. "Explaining
///   alldifferent." In Proceedings of the Australasian Computer Science
///   Conference (ACSC 2012), CRPIT Volume 122, pages 115--124, 2012.
#[derive(Clone, Debug)]
pub struct IntUniqueDomain<I> {
	/// Decisions, values, and their current matching.
	graph: DecisionValueMatching<I>,
	/// Set of decision indices whose domain has changed since the last
	/// propagation pass; cleared by `propagate` and `advise_of_backtrack`.
	dirty_dcns: FxHashSet<usize>,
	/// Decisions whose matched value left their domain and thus need their
	/// matching repaired, carried from phase 1 into phase 2.
	unmatched_dcns: FxHashSet<usize>,
	/// The SCC roots that changed and must be re-run through Tarjan, carried
	/// from phase 2 into phase 3.
	changed_scc: FxHashSet<usize>,
	/// Backtrackable partition of decision indices into current SCCs.
	partition: TrailedPartition,
	/// Per-call scratch for augmenting-path search.
	bfs: AugmentingPathScratch,
	/// Per-call scratch for Tarjan SCC.
	tarjan: TarjanScratch,
	/// Per-call scratch for the explain-time down-closure (Hall-set rebuild).
	closure: ClosureScratch,
}

/// One pending node in the explicit (heap-allocated) Tarjan DFS work-stack.
/// Replaces a native call frame: `i` is the resumption point into this node's
/// neighbour slice `[frame_start, frame_end)` of [`TarjanScratch::neighbours`].
#[derive(Clone, Debug)]
struct TarjanFrame {
	/// Graph node this frame is exploring.
	node: usize,
	/// Start of this frame's neighbour slice in [`TarjanScratch::neighbours`];
	/// the slice is truncated back to here when the frame is popped.
	frame_start: usize,
	/// Exclusive end of this frame's neighbour slice.
	frame_end: usize,
	/// Index of the next neighbour to visit (the DFS resumption point).
	i: usize,
}

/// Reusable scratch for Tarjan's SCC algorithm over a graph with `n` total
/// nodes. `dcns_buf` / `vals_buf` are sized for the bipartite use-case (one
/// buffer per side); a single-bucket variant would suit a non-bipartite
/// consumer.
#[derive(Clone, Debug)]
struct TarjanScratch {
	/// Stack for Tarjan's algorithm.
	dfs_stack: Vec<usize>,
	/// Whether a node is currently on the DFS stack.
	dfs_on_stack: Vec<bool>,
	/// DFS index assigned to each node during the current search.
	/// Value `0` means "not yet visited in this run".
	dfs_index: Vec<usize>,
	/// Lowest reachable DFS index from each node during the current search.
	/// Value `0` means "not yet visited in this run".
	low_link: Vec<usize>,
	/// Explicit Tarjan DFS work-stack: one frame per node currently
	/// being explored, replacing native recursion so deep graphs cannot
	/// overflow the call stack. Reuses one allocation across all DFS runs.
	work_stack: Vec<TarjanFrame>,
	/// Neighbour frame-stack: each pushed frame appends its node's
	/// neighbours, remembers `(start, end)` for its own slice, and truncates
	/// back on pop. Reuses one allocation across all DFS frames.
	neighbours: Vec<usize>,
	/// Scratch list of left nodes in the SCC currently being popped.
	dcns_buf: Vec<usize>,
	/// Scratch list of right nodes in the SCC currently being popped.
	vals_buf: Vec<usize>,
}

impl AugmentingPathScratch {
	/// Create scratch sized for a graph with `n_left` left-side nodes.
	fn new(n_left: usize) -> Self {
		Self {
			queue: Vec::new(),
			parent: vec![usize::MAX; n_left],
		}
	}
}

impl ClosureScratch {
	/// Clear the membership marks left by a down-closure computation, walking
	/// the `dcns` and `vals` lists so only O(closure) entries are touched.
	fn clear_marks(&mut self) {
		for &u in &self.dcns {
			self.dcn_in[u] = false;
		}
		for &vi in &self.vals {
			self.val_in[vi] = false;
		}
		self.vals.clear();
	}

	/// Create scratch for `n_dcns` decisions and `n_values` values.
	fn new(n_dcns: usize, n_values: usize) -> Self {
		Self {
			dcns: Vec::new(),
			vals: Vec::new(),
			dcn_in: vec![false; n_dcns],
			val_in: vec![false; n_values],
		}
	}
}

impl<I> DecisionValueMatching<I> {
	/// Rewire the matching along a freshly discovered BFS-augmenting path
	/// ending at `(end_dcn, end_val)`. Walks backwards through
	/// `bfs_parent`, flipping each edge until it reaches the path's root
	/// (a decision whose previous match was `None`).
	fn augment_along_path(&mut self, end_dcn: usize, end_val: usize, bfs_parent: &[usize]) {
		let mut cur_dcn = end_dcn;
		let mut cur_val = end_val;
		loop {
			let prev_val = self.dcn_to_val[cur_dcn];
			self.val_to_dcn[cur_val] = Some(cur_dcn);
			self.dcn_to_val[cur_dcn] = Some(cur_val);
			let Some(pv) = prev_val else {
				break;
			};
			cur_val = pv;
			let parent = bfs_parent[cur_dcn];
			debug_assert_ne!(parent, usize::MAX, "BFS parent missing");
			cur_dcn = parent;
		}
	}

	/// Number of left-side nodes (decisions).
	fn n_dcns(&self) -> usize {
		self.dcns.len()
	}

	/// Number of right-side nodes (values in the union of initial domains).
	fn n_values(&self) -> usize {
		self.val_to_dcn.len()
	}

	/// Build an initially empty matching for the given decisions, probing each
	/// one's bounds through `ctx` to size the value-side tables to the union of
	/// initial decision domains.
	fn new<C: ReasoningContext + ?Sized>(ctx: &mut C, dcns: Vec<I>) -> Self
	where
		I: IntInspectionActions<C>,
	{
		let n = dcns.len();
		let mut lb = IntVal::MAX;
		let mut ub = IntVal::MIN;
		for v in &dcns {
			let (l, u) = v.bounds(ctx);
			lb = cmp::min(lb, l);
			ub = cmp::max(ub, u);
		}
		debug_assert!(lb <= ub);
		Self {
			dcns,
			union_domain_lb: lb,
			dcn_to_val: vec![None; n],
			val_to_dcn: vec![None; (ub - lb + 1) as usize],
		}
	}

	/// Integer value at the given right-side index.
	fn value_at(&self, right_idx: usize) -> IntVal {
		self.union_domain_lb + right_idx as IntVal
	}

	/// Right-side index for a value already known to lie in
	/// `[union_domain_lb, union_domain_lb + n_values())`.
	fn value_index(&self, val: IntVal) -> usize {
		(val - self.union_domain_lb) as usize
	}
}

impl<I> IntUniqueDomain<I> {
	/// Attempt to repair the matching for `start_dcn` (whose previously matched
	/// value is no longer in its domain) by finding a BFS-augmenting path.
	///
	/// On success, rewires the matching along the discovered path and returns
	/// `Ok(())`. On failure, restores the previous matching and returns
	/// `Err(conflict)`. The conflict closure constructs a Hall-set explanation
	/// from the BFS-visited decisions, whose domain union has strictly fewer
	/// values than decisions.
	fn find_augmenting_path<E>(
		&mut self,
		start_dcn: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let matched_val_idx = self.graph.dcn_to_val[start_dcn];
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_dcn[val_idx] = None;
			self.graph.dcn_to_val[start_dcn] = None;
		}

		self.bfs.queue.clear();
		self.bfs.queue.push(start_dcn);
		self.bfs.parent.fill(usize::MAX);
		let mut queue_head = 0;
		while queue_head < self.bfs.queue.len() {
			let dcn_idx = self.bfs.queue[queue_head];
			queue_head += 1;
			for val in self.graph.dcns[dcn_idx].domain(ctx).iter().flatten() {
				let val_idx = self.graph.value_index(val);
				if let Some(matched_dcn) = self.graph.val_to_dcn[val_idx] {
					if self.bfs.parent[matched_dcn] == usize::MAX {
						self.bfs.queue.push(matched_dcn);
						self.bfs.parent[matched_dcn] = dcn_idx;
					}
				} else {
					self.graph
						.augment_along_path(dcn_idx, val_idx, &self.bfs.parent);
					return Ok(());
				}
			}
		}

		// No augmenting path: restore the previous matching and signal conflict
		// with a Hall-set explanation built from the BFS-visited decisions.
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_dcn[val_idx] = Some(start_dcn);
			self.graph.dcn_to_val[start_dcn] = Some(val_idx);
		}

		Err(ctx.declare_conflict(
			move |ctx: &mut E::PropagationContext<'_>| -> Vec<<E as ReasoningEngine>::Atom> {
				self.build_hall_set_reason(ctx, &self.bfs.queue, |dcn, ctx, meaning| {
					dcn.lit(ctx, meaning)
				})
			},
		))
	}

	/// Create a new [`IntUniqueDomain`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, dcns: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine> + IntInspectionActions<E>,
	{
		let graph = DecisionValueMatching::new(solver, dcns);
		let n = graph.n_dcns();
		let n_values = graph.n_values();
		let partition = TrailedPartition::new(solver, n);
		solver.add_propagator(Box::new(Self {
			graph,
			dirty_dcns: FxHashSet::default(),
			unmatched_dcns: FxHashSet::default(),
			changed_scc: FxHashSet::default(),
			partition,
			bfs: AugmentingPathScratch::new(n),
			tarjan: TarjanScratch::new(n, n_values),
			closure: ClosureScratch::new(n, n_values),
		}));
	}

	/// Process the SCC rooted at `start_idx`: pop nodes off the DFS stack into
	/// `tarjan.dcns_buf` / `vals_buf`, partition the decisions out of the live
	/// SCC, and remove the SCC's values from any decision outside it.
	fn process_scc_root<E>(
		&mut self,
		start_idx: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let n_dcns = self.graph.n_dcns();
		let dummy = self.tarjan.dummy_node();
		self.tarjan.dcns_buf.clear();
		self.tarjan.vals_buf.clear();

		// Pop the SCC off the DFS stack into the two bitsets. The dummy node is
		// not a real graph node, so it is dropped (but still terminates the loop
		// if it happens to be the SCC root).
		loop {
			let node = self.tarjan.dfs_stack.pop().expect("non-empty DFS stack");
			self.tarjan.dfs_on_stack[node] = false;
			if node < n_dcns {
				self.tarjan.dcns_buf.push(node);
			} else if node != dummy {
				self.tarjan.vals_buf.push(node - n_dcns);
			}
			if node == start_idx {
				break;
			}
		}

		// Every popped SCC must contain at least one decision, because the
		// 2-cycle construction makes every matched value share its decision's SCC.
		// This is to avoid value-only SCCs in classic Régin's algorithm,
		// which would require a separate pass to filter out.
		debug_assert!(
			!self.tarjan.dcns_buf.is_empty(),
			"a valid matching's 2-cycle construction guarantees every SCC contains a decision"
		);

		// Move the SCC's decisions into their own block. `split_off` keeps the
		// SCC's decisions in positions [new_root..orig_end); the *other* decisions from
		// the same original block now occupy [orig_root..new_root) — exactly
		// the decisions that still need this SCC's values stripped from them.
		let (orig_root, new_scc_root) = self.partition.split_off(&self.tarjan.dcns_buf, ctx);
		let Some(new_root) = new_scc_root else {
			// The new SCC absorbed the entire original block — no outside
			// decisions to strip values from.
			return Ok(());
		};

		// `new_root` is the SCC's block root for both matched and unmatched
		// values (a matched val's matched_dcn is in this SCC; for an unmatched
		// val, any in-SCC decision serves as the SCC representative). One scc_id
		// covers every value in the SCC.
		let scc_id = new_root;
		let val_reason = ctx.deferred_reason(scc_id as u64);
		for &val_idx in self.tarjan.vals_buf.iter() {
			let val = self.graph.value_at(val_idx);
			for pos in orig_root..new_root {
				let dcn_idx = self.partition.elements()[pos];
				let dcn = self.graph.dcns[dcn_idx].clone();
				if !dcn.in_domain(ctx, val) {
					continue;
				}
				dcn.remove_val(ctx, val, val_reason)?;
			}
		}
		Ok(())
	}

	/// Iterative Tarjan DFS on the bipartite decision/value residual graph,
	/// rooted at `start_idx`.
	///
	/// The implicit graph is constructed such that each decision and value
	/// has a node together with a dummy node. There are three types of edges:
	/// (1) If a decision is matched to a value, there is an arc from the
	/// decision node to the value node, and also a value node to a decision
	/// node. (2) For each matched value, there is an arc from the dummy node
	/// to the value node. (3) For each unmatched value, there is an arc from
	/// the value node to the dummy node. Note that this construction is
	/// slightly different from classical Regin's algorithm, but it guarantees
	/// that every SCC contains at least one decision, so no value-only SCC can
	/// arise, and thus avoids the need for a separate SCC pass to filter out
	/// value-only SCCs.
	fn tarjan_dfs<E>(
		&mut self,
		start_idx: usize,
		next_dfs_index: &mut usize,
		n_left_visited: &mut usize,
		scc_split_detected: &mut bool,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		// Visit `node`: assign its DFS index, append its residual-graph
		// neighbours to `tarjan.neighbours`, and push a `TarjanFrame`. The
		// iterative analogue of entering a recursive call.
		let push_frame = |this: &mut Self,
		                  node: usize,
		                  next_dfs_index: &mut usize,
		                  n_left_visited: &mut usize,
		                  ctx: &mut E::PropagationContext<'_>| {
			let n_dncs = this.graph.n_dcns();
			if node < n_dncs {
				*n_left_visited += 1;
			}
			this.tarjan.dfs_stack.push(node);
			this.tarjan.dfs_on_stack[node] = true;
			this.tarjan.dfs_index[node] = *next_dfs_index;
			this.tarjan.low_link[node] = *next_dfs_index;
			*next_dfs_index += 1;

			let frame_start = this.tarjan.neighbours.len();
			let dummy = this.tarjan.dummy_node();
			if node < n_dncs {
				// 2-cycle: edges to ALL domain values incl. the matched one, so
				// every matched pair shares an SCC and no value-only SCC arises.
				for val in this.graph.dcns[node].domain(ctx).iter().flatten() {
					let val_idx = this.graph.value_index(val);
					this.tarjan.neighbours.push(n_dncs + val_idx);
				}
			} else if node == dummy {
				// Dummy: forwards every free value to all matched values. Built
				// once per run (the dummy is visited at most once).
				for vi in 0..this.graph.n_values() {
					if this.graph.val_to_dcn[vi].is_some() {
						this.tarjan.neighbours.push(n_dncs + vi);
					}
				}
			} else {
				let val_idx = node - n_dncs;
				if let Some(dcn_idx) = this.graph.val_to_dcn[val_idx] {
					// Matched value: matching edge back to its decision.
					this.tarjan.neighbours.push(dcn_idx);
				} else {
					// Free value: a single edge to the shared dummy node, which
					// fans out to every matched value on its behalf.
					this.tarjan.neighbours.push(dummy);
				}
			}
			let frame_end = this.tarjan.neighbours.len();
			this.tarjan.work_stack.push(TarjanFrame {
				node,
				frame_start,
				frame_end,
				i: frame_start,
			});
		};

		let n_dcns = self.graph.n_dcns();
		push_frame(self, start_idx, next_dfs_index, n_left_visited, ctx);

		while let Some(&TarjanFrame {
			node, frame_end, i, ..
		}) = self.tarjan.work_stack.last()
		{
			if i < frame_end {
				// Advance this frame's cursor, then explore the neighbour. A
				// not-yet-visited neighbour pushes a new frame (the recursive
				// call); when we later pop it, the `else` branch below folds its
				// low-link back into this frame — exactly the post-recursion
				// update of the original code.
				let nb = self.tarjan.neighbours[i];
				self.tarjan.work_stack.last_mut().unwrap().i += 1;
				if self.tarjan.dfs_index[nb] != 0 {
					if self.tarjan.dfs_on_stack[nb] {
						self.tarjan.low_link[node] =
							cmp::min(self.tarjan.low_link[node], self.tarjan.dfs_index[nb]);
					}
				} else {
					push_frame(self, nb, next_dfs_index, n_left_visited, ctx);
				}
				continue;
			}

			// Frame exhausted: pop it (the recursive return) and release its
			// neighbour slice.
			let frame = self.tarjan.work_stack.pop().unwrap();
			self.tarjan.neighbours.truncate(frame.frame_start);

			// SCC root?
			if self.tarjan.low_link[frame.node] == self.tarjan.dfs_index[frame.node] {
				// Either we entered the DFS in the middle (low_link > 1) or some
				// left nodes weren't reached from this root -> graph is not one
				// single SCC. The counter avoids re-scanning `dfs_index` on every
				// SCC-root pop.
				if self.tarjan.low_link[frame.node] > 1 || *n_left_visited < n_dcns {
					*scc_split_detected = true;
				}
				if *scc_split_detected {
					self.process_scc_root::<E>(frame.node, ctx)?;
				}
			}

			// Fold this node's low-link into its parent (the post-recursion
			// update the caller would have done).
			if let Some(&TarjanFrame { node: parent, .. }) = self.tarjan.work_stack.last() {
				self.tarjan.low_link[parent] = cmp::min(
					self.tarjan.low_link[parent],
					self.tarjan.low_link[frame.node],
				);
			}
		}
		Ok(())
	}
}

impl<I> IntUniqueDomain<I> {
	/// Build a Hall-set explanation over `members`.
	///
	/// For the set `S = members`, computes
	///   `dom_lb = min_{v in S} lb(v)`,
	///   `dom_ub = max_{v in S} ub(v)`,
	///   `holes  = { x in [dom_lb, dom_ub] : x not in dom(v) for any v in S }`,
	/// and emits, for each `v in S`: `v >= dom_lb`, `v <= dom_ub`, and `v != x`
	/// for every `x in holes`. Equivalently, the emitted reason is the clause
	///
	/// ```text
	///   R(S) = AND_{v in S} ( v >= dom_lb /\ v <= dom_ub /\ AND_{x in holes} v != x )
	/// ```
	///
	/// where each per-member group is exactly `dom(v) subseteq V`, for
	/// `V = [dom_lb, dom_ub] \ holes` (the union of the member domains).
	/// Because `|S|` distinct decisions are pinned into the `|V| == |S|`
	/// values of `V` they exhaust it, so `R(S)` entails the explained literal:
	/// `w != d` for any outside decision `w` and `d in V` (value removal), or
	/// `false` when `S` itself is the over-tight Hall set (UNSAT conflict).
	///
	/// This is the form Régin's algorithm requires for both UNSAT conflicts
	/// (no augmenting path) and value-removal explanations (SCC pruning).
	/// `get_lit` lets the caller choose between `lit` (propagation) and
	/// `lit_relaxed` (explanation), which live in different traits with
	/// different context mutability.
	fn build_hall_set_reason<C, A, F>(
		&self,
		ctx: &mut C,
		members: &[usize],
		mut get_lit: F,
	) -> Vec<A>
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
		F: FnMut(&I, &mut C, IntLitMeaning) -> A,
	{
		// Pass 1: dom_lb / dom_ub from bounds only — cheap and lets us size
		// the union bitset to the [dom_lb, dom_ub] window (typically far
		// smaller than the absolute union-domain span).
		let mut dom_lb = IntVal::MAX;
		let mut dom_ub = IntVal::MIN;
		for &vid in members {
			let (lb, ub) = self.graph.dcns[vid].bounds(ctx);
			dom_lb = cmp::min(dom_lb, lb);
			dom_ub = cmp::max(dom_ub, ub);
		}
		let window = (dom_ub - dom_lb + 1) as usize;

		// Pass 2: union of member domains, window-indexed.
		let mut union_bits = FxHashSet::default();
		for &vid in members {
			for val in self.graph.dcns[vid].domain(ctx).iter().flatten() {
				union_bits.insert((val - dom_lb) as usize);
			}
		}

		// Pass 3: emit per-member literals, deriving holes inline from the
		// bitset's zero positions (no separate holes Vec).
		let n_holes = window - union_bits.len();
		let mut reason: Vec<A> = Vec::with_capacity(members.len() * (2 + n_holes));
		for &did in members {
			let dcn = &self.graph.dcns[did];
			reason.push(get_lit(dcn, ctx, IntLitMeaning::GreaterEq(dom_lb)));
			reason.push(get_lit(dcn, ctx, IntLitMeaning::Less(dom_ub + 1)));
			for i in dom_lb..=dom_ub {
				if !union_bits.contains(&((i - dom_lb) as usize)) {
					reason.push(get_lit(dcn, ctx, IntLitMeaning::NotEq(i)));
				}
			}
		}
		reason
	}

	/// Rebuild the down-closure of the SCC whose decision members occupy the
	/// partition positions `block`, leaving the closed decision set `H` in
	/// `closure.dcns` and the value set `V` in `closure.vals`.
	/// The closure is the tight Hall set used for explanation:
	/// ```text
	///   V := U_{h in H} dom(h)              // values any member can still take
	///   H := H_scc U { match(v) : v in V }  // decisions matched to those values
	/// ```
	/// computed to a least fixpoint from `H = {SCC decisions}`. The matching is
	/// a bijection between `H` and `V`, so `|H| == |V|`. With `dom(h) subseteq
	/// V` for every `h in H` (the first line at fixpoint) this makes the Hall
	/// set tight: `|U_{h in H} dom(h)| == |H|`.
	///
	/// Seeding from the SCC's decisions suffices: the 2-cycle graph keeps every
	/// matched value inside its decision's SCC, and the shared dummy node fans
	/// out to every matched value, so neither an out-of-closure value nor a
	/// free (unmatched) value is reachable without leaving the SCC.
	fn compute_scc_closure_for_explain<C>(&mut self, ctx: &mut C, block: Range<usize>)
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
	{
		self.closure.dcns.clear();
		self.closure.vals.clear();
		for pos in block {
			let u = self.partition.elements()[pos];
			if !self.closure.dcn_in[u] {
				self.closure.dcn_in[u] = true;
				self.closure.dcns.push(u);
			}
		}

		let mut head = 0;
		while head < self.closure.dcns.len() {
			let u = self.closure.dcns[head];
			head += 1;
			for val in self.graph.dcns[u].domain(ctx).iter().flatten() {
				let vi = self.graph.value_index(val);
				if self.closure.val_in[vi] {
					continue;
				}
				self.closure.val_in[vi] = true;
				self.closure.vals.push(vi);
				// Every value reachable in the down-closure is matched (see the
				// method doc); a free value would make the Hall set non-tight.
				let matched = self.graph.val_to_dcn[vi];
				debug_assert!(
					matched.is_some(),
					"reached free value from a proper SCC down-closure"
				);
				if let Some(w) = matched
					&& !self.closure.dcn_in[w]
				{
					self.closure.dcn_in[w] = true;
					self.closure.dcns.push(w);
				}
			}
		}
	}

	/// Phase 1 of `propagate` to remove fixed values from others' domains.
	/// Records, in [`Self::unmatched_dcns`], the decisions whose matched value
	/// was removed from their domain and thus need their matching repaired in
	/// phase 2.
	fn propagate_fixed<E>(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		self.unmatched_dcns.clear();
		for &i in self.dirty_dcns.iter() {
			let dcn = &self.graph.dcns[i];
			let matched_val_index = self.graph.dcn_to_val[i];
			// If the previously matched value is no longer in the domain, this decision is
			// now unmatched.
			if matched_val_index
				.is_none_or(|val_idx| !dcn.in_domain(ctx, self.graph.value_at(val_idx)))
			{
				self.unmatched_dcns.insert(i);
			}
			// Fixed decisions: strip their fixed value from the rest of their SCC.
			if let Some(val) = self.graph.dcns[i].val(ctx) {
				let scc_id = self.partition.block_root(i, ctx);
				let scc_end = self.partition.block_end(scc_id, ctx);
				for pos in scc_id..scc_end {
					let idx = self.partition.elements()[pos];
					let reason_lit = self.graph.dcns[i].lit(ctx, IntLitMeaning::Eq(val));
					if idx != i {
						self.graph.dcns[idx].remove_val(
							ctx,
							val,
							[reason_lit.clone()].as_slice(),
						)?;
						// If `val` was the matched value for decision at `idx`, then it is now
						// unmatched.
						if self.graph.dcn_to_val[idx]
							.is_none_or(|val_idx| val == self.graph.value_at(val_idx))
						{
							self.unmatched_dcns.insert(idx);
						}
					}
				}
			}
		}
		self.dirty_dcns.clear();
		Ok(())
	}

	/// Phase 2 of `propagate`. For each decision in [`Self::unmatched_dcns`]:
	/// repair its matching entry if its previous match left the domain, then
	/// mark the surrounding SCC as needing a Tarjan re-run.
	///
	/// Records the SCC roots that need to be revisited in
	/// [`Self::changed_scc`].
	fn repair_matching<E>(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		self.changed_scc.clear();
		// Detach the unmatched set so the loop body can take `&mut self` for the
		// matching repair; restored below to keep its allocation across calls.
		let unmatched_dcns = mem::take(&mut self.unmatched_dcns);
		for &i in unmatched_dcns.iter() {
			let needs_augment = match self.graph.dcn_to_val[i] {
				None => true,
				Some(val_idx) => !self.graph.dcns[i].in_domain(ctx, self.graph.value_at(val_idx)),
			};
			if needs_augment && let Err(conflict) = self.find_augmenting_path::<E>(i, ctx) {
				self.unmatched_dcns = unmatched_dcns;
				return Err(conflict);
			}
			let scc_id = self.partition.block_root(i, ctx);
			self.changed_scc.insert(scc_id);
		}
		self.unmatched_dcns = unmatched_dcns;
		Ok(())
	}

	/// Phase 3 of `propagate`. Runs Tarjan on every SCC root flagged in
	/// `changed_scc`. Tarjan walks the residual bipartite graph and, for each
	/// non-trivial SCC discovered, partitions the decisions out and removes
	/// the SCC's values from decisions outside it.
	fn run_tarjan_on_changed_sccs<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		self.tarjan.reset();
		let mut next_dfs_index: usize = 1;
		let mut n_left_visited: usize = 0;
		let mut scc_split_detected = false;
		// Detach the changed-SCC set so the loop body can take `&mut self` for
		// the Tarjan DFS; restored below to keep its allocation across calls.
		let changed_scc = mem::take(&mut self.changed_scc);
		for &i in changed_scc.iter() {
			let scc_end = self.partition.block_end(i, ctx);
			for dcn_idx in i..scc_end {
				if self.tarjan.dfs_index[dcn_idx] == 0
					&& let Err(conflict) = self.tarjan_dfs::<E>(
						dcn_idx,
						&mut next_dfs_index,
						&mut n_left_visited,
						&mut scc_split_detected,
						ctx,
					) {
					self.changed_scc = changed_scc;
					return Err(conflict);
				}
			}
		}
		self.changed_scc = changed_scc;
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntUniqueDomain<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationContext<'_>) {
		self.dirty_dcns.clear();
	}

	/// When a decision's domain changes, mark it as dirty and only enqueue
	/// propagation if its domain size is now less than the number of decisions.
	/// Larger domains cannot participate in any non-trivial Hall set, so there
	/// is nothing to propagate.
	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		_event: IntEvent,
	) -> bool {
		// safe to unwrap: `card()` only returns `None` if the number of steps would
		// overflow `usize`
		let domain_size = self.graph.dcns[data as usize].domain(ctx).card().unwrap();
		self.dirty_dcns.insert(data as usize);
		domain_size < self.graph.n_dcns()
	}

	fn explain(
		&mut self,
		ctx: &mut E::ExplanationContext<'_>,
		_lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let scc_id = data as usize;
		let scc_end = self.partition.block_end(scc_id, ctx);

		// Rebuild the SCC's down-closure from the restored partition block: a
		// decision set `H` provably confined to an equal-sized value set `V` in
		// the current domains. Note that the raw SCC members alone are unsound:
		// a member can still hold an out-of-SCC value (a cross-SCC edge that a
		// downstream prune/backtrack left behind), making the Hall set non-tight and
		// the nogood too weak. The closure absorbs every such escape so
		// `|H| == |V|` by construction.
		self.compute_scc_closure_for_explain(ctx, scc_id..scc_end);
		debug_assert_eq!(
			self.closure.dcns.len(),
			self.closure.vals.len(),
			"down-closure Hall set is not tight"
		);
		let reason = self.build_hall_set_reason(ctx, &self.closure.dcns, |dcn, ctx, meaning| {
			let (atom, _) = dcn.lit_relaxed(ctx, meaning);
			atom
		});
		// Reset the membership marks (O(closure)) so the bitsets are clean for
		// the next explain. The `dcns`/`vals` lists are the only record of which
		// entries were marked, so this must run after the reason is built.
		self.closure.clear_marks();
		reason
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		for i in 0..self.graph.n_dcns() {
			self.dirty_dcns.insert(i);
		}
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.dcns.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Domain, i as u64);
		}
		ctx.advise_on_backtrack();
		ctx.enqueue_now(true);
	}

	#[tracing::instrument(
		name = "int_unique_domain",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		trace!(target: "int_unique", dirty_dcns =? self.dirty_dcns, "dirty decisions");
		// Phase 1: check whether each dirty decision is now fixed, and
		// collect the set of unmatched decisions into `self.unmatched_dcns`.
		self.propagate_fixed(ctx)?;
		trace!(target: "int_unique", unmatched_decisions =? self.unmatched_dcns, "unmatched decisions");
		// Phase 2: repair the matching for each dirty decision, and
		// collect the set of changed SCCs into `self.changed_scc`.
		self.repair_matching(ctx)?;
		debug_assert!(
			(0..self.graph.dcns.len()).all(|i| self.graph.dcn_to_val[i].is_some()),
			"all decisions should be matched after propagation"
		);
		trace!(target: "int_unique", changed_sccs =? self.changed_scc, "changed SCCs");
		// Phase 3: re-run Tarjan on every SCC that changed in phase 2.
		self.run_tarjan_on_changed_sccs(ctx)
	}
}

impl TarjanScratch {
	/// Index of the auxiliary "dummy" node in the residual graph: the single
	/// slot immediately after the real (decision and value) nodes. Every free
	/// (unmatched) value points at this node, which in turn points at every
	/// matched value, keeping the free-value fanout linear in the number of
	/// values rather than quadratic. It is not a real graph node: it is skipped
	/// when an SCC is extracted in [`IntUniqueDomain::process_scc_root`].
	fn dummy_node(&self) -> usize {
		self.dfs_on_stack.len() - 1
	}

	/// Create scratch sized to fit `n_dcns` decision nodes and `n_values` value
	/// nodes, plus the auxiliary dummy node (see [`Self::dummy_node`]).
	fn new(n_dcns: usize, n_values: usize) -> Self {
		let n_slots = n_dcns + n_values + 1;
		Self {
			dfs_stack: Vec::new(),
			dfs_on_stack: vec![false; n_slots],
			dfs_index: vec![0; n_slots],
			low_link: vec![0; n_slots],
			work_stack: Vec::new(),
			neighbours: Vec::new(),
			dcns_buf: Vec::new(),
			vals_buf: Vec::new(),
		}
	}

	/// Reset bookkeeping before a fresh DFS run. After this call,
	/// `dfs_index[v] == 0` signals "not yet visited" (indices are assigned
	/// starting at `1`).
	fn reset(&mut self) {
		self.dfs_stack.clear();
		self.dfs_on_stack.fill(false);
		self.dfs_index.fill(0);
		self.low_link.fill(0);
		self.work_stack.clear();
		self.neighbours.clear();
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		constraints::int_unique::IntUniqueDomain,
		solver::{LiteralStrategy, Solver},
	};

	#[test]
	#[traced_test]
	fn test_domain_deep_chain() {
		// Staircase that forces a long DFS over the residual graph: `x_i in
		// {i, i+1}` for `i < N`, with the top pinned to `x_N = N`. All-different
		// forces a downward cascade `x_i = i`, but reaching that fixpoint walks
		// a chain whose length is proportional to `N`.
		const N: IntVal = 300;
		let mut slv = Solver::default();
		let dcns: Vec<_> = (1..=N)
			.map(|i| {
				let dom = if i == N { N..=N } else { i..=i + 1 };
				slv.new_int_decision(dom)
					.order_literals(LiteralStrategy::Eager)
					.direct_literals(LiteralStrategy::Eager)
					.view()
			})
			.collect();
		IntUniqueDomain::post(&mut slv, dcns.clone());
		slv.assert_all_solutions(&dcns, |sol| {
			sol.iter()
				.enumerate()
				.all(|(i, v)| *v == crate::solver::Value::Int(i as IntVal + 1))
		});
	}

	#[test]
	#[traced_test]
	fn test_domain_filtering() {
		// Régin-style example: {1,2}, {1,2}, {1,2,3}. The Hall set {a,b} on
		// {1,2} should prune 1 and 2 from c, leaving c = 3.
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| {
			sol.iter().all_unique() && sol[2] == crate::solver::Value::Int(3)
		});
	}

	#[test]
	#[traced_test]
	fn test_domain_interior_hole() {
		// One test covering the distinguishing behaviours of the domain
		// propagator at once:
		// - The universe (1..=6) exceeds the decision count, so the matching leaves
		//   free values (2, 5, 6) and the residual graph routes through the dummy node.
		// - The Hall set {a, b} occupies {3, 4}, so domain consistency must remove the
		//   *interior* values 3 and 4 from `e`, leaving the disconnected set {1, 2, 5,
		//   6}. A bounds-consistent propagator could not do this: e's bounds stay (1,
		//   6) and only the holes change.
		// - We assert the exact set of literals propagated, not just the resulting
		//   domain.
		use crate::actions::{IntDecisionActions, IntInspectionActions};

		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let e = slv
			.new_int_decision(1..=6)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, e]);
		let propagated = slv.propagate_next().unwrap();

		assert_eq!(a.domain(&slv), IntSet::from(3..=4));
		assert_eq!(b.domain(&slv), IntSet::from(3..=4));
		assert_eq!(e.domain(&slv), IntSet::from_iter([1..=2, 5..=6]));
		assert!(!e.in_domain(&slv, 3));
		assert!(!e.in_domain(&slv, 4));
		// Bounds are untouched; only the interior was pruned.
		assert_eq!(e.bounds(&slv), (1, 6));

		// The only inferences are the interior removals "e != 3" and "e != 4".
		let expected = [
			e.lit(&mut slv, crate::solver::IntLitMeaning::NotEq(3)),
			e.lit(&mut slv, crate::solver::IntLitMeaning::NotEq(4)),
		];
		assert_eq!(propagated.len(), expected.len());
		for lit in expected {
			assert!(
				propagated.contains(&lit),
				"missing propagated literal {lit:?}"
			);
		}
	}

	#[test]
	#[traced_test]
	fn test_domain_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_domain_unsat() {
		// Three decisions on {1,2}: Hall set, no matching exists.
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_unsatisfiable();
	}

	/// Regression: the Hall-set explanation must stay sound. When an SCC's
	/// values are pruned from outside decisions, the reason is only valid if
	/// every Hall-set member is confined to the SCC's value set `V`. If a
	/// member still holds an out-of-`V` value (a residual edge left behind by a
	/// prune/backtrack), the Hall set is non-tight and the nogood is too weak,
	/// wrongly cutting feasible assignments. Minimizing `x[0]` below, the true
	/// optimum is 2 (witness `[2, 1, 4, 3, 7, 5, 8]`, all-different); the buggy
	/// propagator excluded `x[0] = 2` and proved 3.
	///
	/// Minimization (rather than enumeration) is what exercises the bug:
	/// proving the optimum forces conflict analysis to request the deferred
	/// SCC-pruning reason via `explain`, which is where the unsound Hall set
	/// was built.
	#[test]
	#[traced_test]
	fn test_hall_set_soundness() {
		// The explicit type pins the `Sat` parameter, which the `minimize` call
		// below (unlike the propagate/enumerate helpers) does not constrain.
		let mut slv: Solver = Solver::default();
		let domains: [&[IntVal]; 7] = [
			&[2, 3, 4, 5, 6],
			&[1, 2, 5],
			&[2, 4],
			&[1, 3, 7],
			&[7],
			&[2, 5, 7],
			&[1, 3, 8],
		];
		let views: Vec<_> = domains
			.iter()
			.map(|d| {
				slv.new_int_decision(IntSet::from_iter(d.iter().map(|&v| v..=v)))
					.order_literals(LiteralStrategy::Eager)
					.direct_literals(LiteralStrategy::Eager)
					.view()
			})
			.collect();
		IntUniqueDomain::post(&mut slv, views.clone());
		let (status, opt) = slv.solve().minimize(views[0]);
		assert_eq!(status, crate::solver::Status::Complete);
		assert_eq!(
			opt,
			Some(2),
			"unsound Hall-set reason: domain propagator proved a wrong optimum"
		);
	}
}
