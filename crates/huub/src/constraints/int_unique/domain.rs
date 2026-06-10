//! Domain-consistent propagator for the integer `unique` constraint.
//! The public algorithm overview and references live on
//! [`IntUniqueDomain`]; this module file contains the propagator and its
//! private graph/matching/Tarjan helpers.

use std::cmp;

use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;

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

/// Reusable scratch for the explain-time down-closure: the tight Hall set
/// rebuilt in [`IntUniqueDomain::compute_scc_closure_for_explain`].
#[derive(Clone, Debug)]
struct ClosureScratch {
	/// Variable members `H` of the tight Hall set. Membership is marked in
	/// [`Self::var_in`]; the list lets the marks be cleared in O(closure).
	vars: Vec<usize>,
	/// Value set `V` of the tight Hall set (marked in [`Self::val_in`]).
	vals: Vec<usize>,
	/// `var_in[v]` is `true` while variable `v` is in the down-closure being
	/// built (a re-entrancy-free dedup bitset).
	var_in: Vec<bool>,
	/// `val_in[i]` is `true` while value index `i` is in the down-closure.
	val_in: Vec<bool>,
}

/// Domain-consistent propagator for the integer `unique` constraint.
///
/// Implements Régin's bipartite-matching + Tarjan SCC algorithm (AAAI 1994):
/// maintain a maximum matching from variables to values, repair it with
/// BFS-augmenting paths after domain changes, then run Tarjan's SCC on the
/// residual bipartite graph (with a single dummy node fanning out free
/// values so the residual graph stays linear in size) and remove any value
/// from a variable's domain whenever the variable and value land in
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
	/// Variables, values, and their current matching.
	graph: VariableValueMatching<I>,
	/// Set of variable indices whose domain has changed since the last
	/// propagation pass; cleared by `propagate` and `advise_of_backtrack`.
	dirty_vars: FxHashSet<usize>,
	/// Backtrackable partition of variable indices into current SCCs.
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
/// nodes. `vars_buf` / `vals_buf` are sized for the bipartite use-case (one
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
	/// Explicit Tarjan DFS work-stack: one [`TarjanFrame`] per node currently
	/// being explored, replacing native recursion so deep graphs cannot
	/// overflow the call stack. Reuses one allocation across all DFS runs.
	work_stack: Vec<TarjanFrame>,
	/// Neighbour frame-stack: each pushed [`TarjanFrame`] appends its node's
	/// neighbours, remembers `(start, end)` for its own slice, and truncates
	/// back on pop. Reuses one allocation across all DFS frames.
	neighbours: Vec<usize>,
	/// Scratch list of left nodes in the SCC currently being popped.
	vars_buf: Vec<usize>,
	/// Scratch list of right nodes in the SCC currently being popped.
	vals_buf: Vec<usize>,
}

/// The bipartite "variable <-> value" graph that Régin's algorithm operates on,
/// together with the current maximum matching between the two sides.
///
/// All variable/value bookkeeping lives here: the variable list, the
/// union-domain origin used to translate between integer values and right-side
/// indices, and the matching tables. Algorithms (augmenting-path search,
/// Tarjan, Hall-set reasoning) operate on this struct from the outside.
#[derive(Clone, Debug)]
struct VariableValueMatching<I> {
	/// Left side: the integer decision variables.
	vars: Vec<I>,
	/// Lower bound of the union of all initial variable domains. The
	/// right-side index `r` represents the integer value
	/// `union_domain_lb + r`, for `r` in `0..n_values()`.
	union_domain_lb: IntVal,
	/// Matching: variable index -> value index.
	var_to_val: Vec<Option<usize>>,
	/// Matching: value index -> variable index. Sized at construction time to
	/// the size of the union of initial variable domains.
	val_to_var: Vec<Option<usize>>,
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
	/// Create scratch for `n_vars` variables and `n_values` values.
	fn new(n_vars: usize, n_values: usize) -> Self {
		Self {
			vars: Vec::new(),
			vals: Vec::new(),
			var_in: vec![false; n_vars],
			val_in: vec![false; n_values],
		}
	}
}

impl<I> IntUniqueDomain<I> {
	/// Attempt to repair the matching for `start_var` (whose previously matched
	/// value is no longer in its domain) by finding a BFS-augmenting path.
	///
	/// On success, rewires the matching along the discovered path and returns
	/// `Ok(())`. On failure, restores the previous matching and returns
	/// `Err(conflict)`. The conflict closure constructs a Hall-set explanation
	/// from the BFS-visited variables, whose domain union has strictly fewer
	/// values than variables.
	fn find_augmenting_path<E>(
		&mut self,
		start_var: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let matched_val_idx = self.graph.var_to_val[start_var];
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_var[val_idx] = None;
			self.graph.var_to_val[start_var] = None;
		}

		self.bfs.queue.clear();
		self.bfs.queue.push(start_var);
		self.bfs.parent.fill(usize::MAX);
		let mut queue_head = 0;
		while queue_head < self.bfs.queue.len() {
			let var_idx = self.bfs.queue[queue_head];
			queue_head += 1;
			for val in self.graph.vars[var_idx].domain(ctx).iter().flatten() {
				let val_idx = self.graph.value_index(val);
				if let Some(matched_var) = self.graph.val_to_var[val_idx] {
					if self.bfs.parent[matched_var] == usize::MAX {
						self.bfs.queue.push(matched_var);
						self.bfs.parent[matched_var] = var_idx;
					}
				} else {
					self.graph
						.augment_along_path(var_idx, val_idx, &self.bfs.parent);
					return Ok(());
				}
			}
		}

		// No augmenting path: restore the previous matching and signal conflict
		// with a Hall-set explanation built from the BFS-visited variables.
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_var[val_idx] = Some(start_var);
			self.graph.var_to_val[start_var] = Some(val_idx);
		}

		Err(ctx.declare_conflict(
			move |ctx: &mut E::PropagationContext<'_>| -> Vec<<E as ReasoningEngine>::Atom> {
				self.build_hall_set_reason(ctx, &self.bfs.queue, |var, ctx, meaning| {
					var.lit(ctx, meaning)
				})
			},
		))
	}

	/// Create a new [`IntUniqueDomain`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine> + IntInspectionActions<E>,
	{
		let graph = VariableValueMatching::new(solver, vars);
		let n = graph.n_vars();
		let n_values = graph.n_values();
		let partition = TrailedPartition::new(solver, n);
		solver.add_propagator(Box::new(Self {
			graph,
			dirty_vars: FxHashSet::default(),
			partition,
			bfs: AugmentingPathScratch::new(n),
			tarjan: TarjanScratch::new(n, n_values),
			closure: ClosureScratch::new(n, n_values),
		}));
	}

	/// Process the SCC rooted at `start_idx`: pop nodes off the DFS stack into
	/// `tarjan.vars_buf` / `vals_buf`, partition the variables out of the live
	/// SCC, and remove the SCC's values from any variable outside it.
	fn process_scc_root<E>(
		&mut self,
		start_idx: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let n_vars = self.graph.n_vars();
		let dummy = self.tarjan.dummy_node();
		self.tarjan.vars_buf.clear();
		self.tarjan.vals_buf.clear();

		// Pop the SCC off the DFS stack into the two bitsets. The dummy node is
		// not a real graph node, so it is dropped (but still terminates the loop
		// if it happens to be the SCC root).
		loop {
			let node = self.tarjan.dfs_stack.pop().expect("non-empty DFS stack");
			self.tarjan.dfs_on_stack[node] = false;
			if node < n_vars {
				self.tarjan.vars_buf.push(node);
			} else if node != dummy {
				self.tarjan.vals_buf.push(node - n_vars);
			}
			if node == start_idx {
				break;
			}
		}

		// Every popped SCC must contain at least one variable, because the
		// 2-cycle construction makes every matched value share its variable's SCC.
		// This is to avoid value-only SCC in classic Régin's algorithm,
		// which would require a separate pass to filter out
		debug_assert!(
			!self.tarjan.vars_buf.is_empty(),
			"2-cycle construction guarantees every SCC contains a variable"
		);

		// Move the SCC's variables into their own block. `split_off` keeps the
		// SCC's vars in positions [new_root..orig_end); the *other* vars from
		// the same original block now occupy [orig_root..new_root) — exactly
		// the variables that still need this SCC's values stripped from them.
		let (orig_root, new_scc_root) = self.partition.split_off(&self.tarjan.vars_buf, ctx);
		let Some(new_root) = new_scc_root else {
			// The new SCC absorbed the entire original block — no outside
			// variables to strip values from.
			return Ok(());
		};

		// `new_root` is the SCC's block root for both matched and unmatched
		// values (a matched val's matched_var is in this SCC; for an unmatched
		// val, any in-SCC var serves as the SCC representative). One scc_id
		// covers every value in the SCC.
		let scc_id = new_root;
		let val_reason = ctx.deferred_reason(scc_id as u64);
		for &val_idx in self.tarjan.vals_buf.iter() {
			let val = self.graph.value_at(val_idx);
			for pos in orig_root..new_root {
				let var_idx = self.partition.elements()[pos];
				let var = self.graph.vars[var_idx].clone();
				if !var.in_domain(ctx, val) {
					continue;
				}
				var.remove_val(ctx, val, val_reason)?;
			}
		}
		Ok(())
	}

	/// Iterative Tarjan DFS on the bipartite var/value residual graph, rooted
	/// at `start_idx`. Uses an explicit heap work-stack ([`TarjanFrame`])
	/// instead of native recursion, so the maximum DFS depth (up to `2 *
	/// n_vars`) does not consume the call stack. When the root of a
	/// non-trivial SCC is popped and the run already detected an SCC split,
	/// delegates filtering to [`Self::process_scc_root`].
	///
	/// The implicit graph is constructed such that each variables and values
	/// has a node together with a dummy node. There are three types of edges:
	/// (1) If a variable is matched to a value, there is an arc from the
	/// variable  node to the value node, and also a value node to a variable
	/// node. (2) For each matched value, there is an arc from the dummy node
	/// to the value node. (3) For each unmatched value, there is an arc from
	/// the value node to the dummy node. Note that this construction is
	/// slightly different from classical Regin's algorithm, but it guarantees
	/// that every SCC contains at least one variable, so no value-only SCC can
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
			let n_vars = this.graph.n_vars();
			if node < n_vars {
				*n_left_visited += 1;
			}
			this.tarjan.dfs_stack.push(node);
			this.tarjan.dfs_on_stack[node] = true;
			this.tarjan.dfs_index[node] = *next_dfs_index;
			this.tarjan.low_link[node] = *next_dfs_index;
			*next_dfs_index += 1;

			let frame_start = this.tarjan.neighbours.len();
			let dummy = this.tarjan.dummy_node();
			if node < n_vars {
				// 2-cycle: edges to ALL domain values incl. the matched one, so
				// every matched pair shares an SCC and no value-only SCC arises.
				for val in this.graph.vars[node].domain(ctx).iter().flatten() {
					let val_idx = this.graph.value_index(val);
					this.tarjan.neighbours.push(n_vars + val_idx);
				}
			} else if node == dummy {
				// Dummy: forwards every free value to all matched values. Built
				// once per run (the dummy is visited at most once).
				for vi in 0..this.graph.n_values() {
					if this.graph.val_to_var[vi].is_some() {
						this.tarjan.neighbours.push(n_vars + vi);
					}
				}
			} else {
				let val_idx = node - n_vars;
				if let Some(var_idx) = this.graph.val_to_var[val_idx] {
					// Matched value: matching edge back to its variable.
					this.tarjan.neighbours.push(var_idx);
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

		let n_vars = self.graph.n_vars();
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
				if self.tarjan.low_link[frame.node] > 1 || *n_left_visited < n_vars {
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
	/// Because `|S|` distinct variables are pinned into the `|V| == |S|`
	/// values of `V` they exhaust it, so `R(S)` entails the explained literal:
	/// `w != d` for any outside variable `w` and `d in V` (value removal), or
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
			let (lb, ub) = self.graph.vars[vid].bounds(ctx);
			dom_lb = cmp::min(dom_lb, lb);
			dom_ub = cmp::max(dom_ub, ub);
		}
		let window = (dom_ub - dom_lb + 1) as usize;

		// Pass 2: union of member domains, window-indexed.
		let mut union_bits = FxHashSet::default();
		for &vid in members {
			for val in self.graph.vars[vid].domain(ctx).iter().flatten() {
				union_bits.insert((val - dom_lb) as usize);
			}
		}

		// Pass 3: emit per-member literals, deriving holes inline from the
		// bitset's zero positions (no separate holes Vec).
		let n_holes = window - union_bits.len();
		let mut reason: Vec<A> = Vec::with_capacity(members.len() * (2 + n_holes));
		for &vid in members {
			let var = &self.graph.vars[vid];
			reason.push(get_lit(var, ctx, IntLitMeaning::GreaterEq(dom_lb)));
			reason.push(get_lit(var, ctx, IntLitMeaning::Less(dom_ub + 1)));
			for i in dom_lb..=dom_ub {
				if !union_bits.contains(&((i - dom_lb) as usize)) {
					reason.push(get_lit(var, ctx, IntLitMeaning::NotEq(i)));
				}
			}
		}
		reason
	}

	/// Rebuild the down-closure of the SCC whose variable members occupy the
	/// partition positions `block`, leaving the closed variable set `H` in
	/// `closure.vars` and the value set `V` in `closure.vals`.
	/// The closure is the tight Hall set used for explanation:
	/// ```text
	///   V := U_{h in H} dom(h)              // values any member can still take
	///   H := H_scc U { match(v) : v in V }  // variables matched to those values
	/// ```
	/// computed to a least fixpoint from `H = {SCC variables}`. The matching is
	/// a bijection between `H` and `V`, so `|H| == |V|`. With `dom(h) subseteq
	/// V` for every `h in H` (the first line at fixpoint) this makes the Hall
	/// set tight: `|U_{h in H} dom(h)| == |H|`.
	///
	/// Seeding from the SCC's variables suffices: the 2-cycle graph keeps every
	/// matched value inside its variable's SCC, and the shared dummy node fans
	/// out to every matched value, so neither an out-of-closure value nor a
	/// free (unmatched) value is reachable without leaving the SCC.
	fn compute_scc_closure_for_explain<C>(&mut self, ctx: &mut C, block: std::ops::Range<usize>)
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
	{
		self.closure.vars.clear();
		self.closure.vals.clear();
		for pos in block {
			let u = self.partition.elements()[pos];
			if !self.closure.var_in[u] {
				self.closure.var_in[u] = true;
				self.closure.vars.push(u);
			}
		}

		let mut head = 0;
		while head < self.closure.vars.len() {
			let u = self.closure.vars[head];
			head += 1;
			for val in self.graph.vars[u].domain(ctx).iter().flatten() {
				let vi = self.graph.value_index(val);
				if self.closure.val_in[vi] {
					continue;
				}
				self.closure.val_in[vi] = true;
				self.closure.vals.push(vi);
				match self.graph.val_to_var[vi] {
					Some(w) => {
						if !self.closure.var_in[w] {
							self.closure.var_in[w] = true;
							self.closure.vars.push(w);
						}
					}
					None => {
						debug_assert!(false, "free value reachable from a proper SCC down-closure");
					}
				}
			}
		}
	}

	/// Phase 1 of `propagate`. For each dirty variable: repair its matching
	/// entry if its previous match left the domain, then either propagate the
	/// "newly fixed" case (singleton domain -> strip its value from the rest of
	/// its SCC) or mark the surrounding SCC as needing a Tarjan re-run.
	///
	/// Returns the set of SCC roots that need to be revisited in phase 2. Takes
	/// the dirty set by reference (rather than reading `self.dirty_vars`) so
	/// the caller can own the take/restore and guarantee the set is put back
	/// on every exit path.
	fn repair_matching_and_propagate_fixed<E>(
		&mut self,
		dirty: &FxHashSet<usize>,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<FxHashSet<usize>, E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut changed_scc = FxHashSet::default();
		for &i in dirty.iter() {
			let scc_id = self.partition.block_root(i, ctx);
			let needs_augment = match self.graph.var_to_val[i] {
				None => true,
				Some(val_idx) => !self.graph.vars[i].in_domain(ctx, self.graph.value_at(val_idx)),
			};
			if needs_augment {
				self.find_augmenting_path::<E>(i, ctx)?;
			}

			// If the variable is now fixed, propagate the newly fixed event.
			// Otherwise, mark its involved SCC as dirty for phase 2.
			if let Some(val) = self.graph.vars[i].val(ctx) {
				changed_scc.insert(scc_id);
				let (orig_scc, new_scc) = self.partition.split_off(&[i], ctx);
				if new_scc.is_some() {
					let orig_scc_end = self.partition.block_end(orig_scc, ctx);
					let reason_lit = self.graph.vars[i].lit(ctx, IntLitMeaning::Eq(val));
					for pos in orig_scc..orig_scc_end {
						let idx = self.partition.elements()[pos];
						let v = self.graph.vars[idx].clone();
						v.remove_val(ctx, val, [reason_lit.clone()].as_slice())?;
					}
					if orig_scc_end - orig_scc > 1 {
						changed_scc.insert(orig_scc);
					}
				}
			} else {
				let scc_end = self.partition.block_end(scc_id, ctx);
				if scc_end - scc_id > 1 {
					changed_scc.insert(scc_id);
				}
			}
		}
		Ok(changed_scc)
	}

	/// Phase 2 of `propagate`. Runs Tarjan on every SCC root flagged in
	/// `changed_scc`. Tarjan walks the residual bipartite graph and, for each
	/// non-trivial SCC discovered, partitions the variables out and removes
	/// the SCC's values from variables outside it.
	fn run_tarjan_on_changed_sccs<E>(
		&mut self,
		changed_scc: &FxHashSet<usize>,
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
		for &i in changed_scc.iter() {
			let scc_end = self.partition.block_end(i, ctx);
			for var_idx in i..scc_end {
				if self.tarjan.dfs_index[var_idx] == 0 {
					self.tarjan_dfs::<E>(
						var_idx,
						&mut next_dfs_index,
						&mut n_left_visited,
						&mut scc_split_detected,
						ctx,
					)?;
				}
			}
		}
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntUniqueDomain<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationContext<'_>) {
		self.dirty_vars.clear();
	}

	/// When a variable's domain changes, mark it as dirty and only enqueue
	/// propagation if its domain size is now less than the number of variables.
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
		let domain_size = self.graph.vars[data as usize].domain(ctx).card().unwrap();
		self.dirty_vars.insert(data as usize);
		domain_size < self.graph.n_vars()
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
		// variable set `H` provably confined to an equal-sized value set `V` in
		// the current domains. Note that the raw SCC members alone are unsound:
		// a member can still hold an out-of-SCC value (a cross-SCC edge that a
		// downstream prune/backtrack left behind), making the Hall set non-tight and
		// the nogood too weak. The closure absorbs every such escape so
		// `|H| == |V|` by construction.
		self.compute_scc_closure_for_explain(ctx, scc_id..scc_end);
		debug_assert_eq!(
			self.closure.vars.len(),
			self.closure.vals.len(),
			"down-closure Hall set is not tight"
		);

		let members = std::mem::take(&mut self.closure.vars);
		let reason = self.build_hall_set_reason(ctx, &members, |var, ctx, meaning| {
			let (atom, _) = var.lit_relaxed(ctx, meaning);
			atom
		});

		// Clear the closure marks (O(closure)) and hand the scratch vec back.
		for &u in &members {
			self.closure.var_in[u] = false;
		}
		for &vi in &self.closure.vals {
			self.closure.val_in[vi] = false;
		}
		self.closure.vals.clear();
		self.closure.vars = members;
		reason
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		for i in 0..self.graph.n_vars() {
			self.dirty_vars.insert(i);
		}
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.vars.iter().enumerate() {
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
		// Phase 1: drain dirty variables, fix the matching, and collect the
		// set of SCC roots whose residual graph may have changed.
		//
		// Borrow the dirty set out so phase 1 can take `&mut self` while reading
		// it. Put the emptied set back on every path, including on conflict from
		// `?`, so its capacity is reused next round.
		let mut dirty = std::mem::take(&mut self.dirty_vars);
		let result = self.repair_matching_and_propagate_fixed(&dirty, ctx);
		dirty.clear();
		self.dirty_vars = dirty;
		let changed_scc = result?;

		// Phase 2: re-run Tarjan on every SCC that changed in phase 1.
		self.run_tarjan_on_changed_sccs(&changed_scc, ctx)
	}
}

impl TarjanScratch {
	/// Index of the auxiliary "dummy" node in the residual graph: the single
	/// slot immediately after the real (variable and value) nodes. Every free
	/// (unmatched) value points at this node, which in turn points at every
	/// matched value, keeping the free-value fanout linear in the number of
	/// values rather than quadratic. It is not a real graph node: it is skipped
	/// when an SCC is extracted in [`IntUniqueDomain::process_scc_root`].
	fn dummy_node(&self) -> usize {
		self.dfs_on_stack.len() - 1
	}

	/// Create scratch sized to fit `n_vars` variable nodes and `n_values` value
	/// nodes, plus the auxiliary dummy node (see [`Self::dummy_node`]).
	fn new(n_vars: usize, n_values: usize) -> Self {
		let n_slots = n_vars + n_values + 1;
		Self {
			dfs_stack: Vec::new(),
			dfs_on_stack: vec![false; n_slots],
			dfs_index: vec![0; n_slots],
			low_link: vec![0; n_slots],
			work_stack: Vec::new(),
			neighbours: Vec::new(),
			vars_buf: Vec::new(),
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

impl<I> VariableValueMatching<I> {
	/// Rewire the matching along a freshly discovered BFS-augmenting path
	/// ending at `(end_var, end_val)`. Walks backwards through
	/// `bfs_parent`, flipping each edge until it reaches the path's root
	/// (a variable whose previous match was `None`).
	fn augment_along_path(&mut self, end_var: usize, end_val: usize, bfs_parent: &[usize]) {
		let mut cur_var = end_var;
		let mut cur_val = end_val;
		loop {
			let prev_val = self.var_to_val[cur_var];
			self.val_to_var[cur_val] = Some(cur_var);
			self.var_to_val[cur_var] = Some(cur_val);
			let Some(pv) = prev_val else {
				break;
			};
			cur_val = pv;
			let parent = bfs_parent[cur_var];
			debug_assert_ne!(parent, usize::MAX, "BFS parent missing");
			cur_var = parent;
		}
	}

	/// Number of right-side nodes (values in the union of initial domains).
	fn n_values(&self) -> usize {
		self.val_to_var.len()
	}

	/// Number of left-side nodes (variables).
	fn n_vars(&self) -> usize {
		self.vars.len()
	}

	/// Build an initially empty matching for the given variables, probing each
	/// one's bounds through `ctx` to size the value-side tables to the union of
	/// initial variable domains.
	fn new<C: ReasoningContext + ?Sized>(ctx: &mut C, vars: Vec<I>) -> Self
	where
		I: IntInspectionActions<C>,
	{
		let n = vars.len();
		let mut lb = IntVal::MAX;
		let mut ub = IntVal::MIN;
		for v in &vars {
			let (l, u) = v.bounds(ctx);
			lb = cmp::min(lb, l);
			ub = cmp::max(ub, u);
		}
		debug_assert!(lb <= ub);
		Self {
			vars,
			union_domain_lb: lb,
			var_to_val: vec![None; n],
			val_to_var: vec![None; (ub - lb + 1) as usize],
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
	fn test_all_different_domain_deep_chain() {
		// Staircase that forces a long DFS over the residual graph: `x_i in
		// {i, i+1}` for `i < N`, with the top pinned to `x_N = N`. All-different
		// forces a downward cascade `x_i = i`, but reaching that fixpoint walks
		// a chain whose length is proportional to `N`.
		const N: IntVal = 300;
		let mut slv = Solver::default();
		let vars: Vec<_> = (1..=N)
			.map(|i| {
				let dom = if i == N { N..=N } else { i..=i + 1 };
				slv.new_int_decision(dom)
					.order_literals(LiteralStrategy::Eager)
					.direct_literals(LiteralStrategy::Eager)
					.view()
			})
			.collect();
		IntUniqueDomain::post(&mut slv, vars.clone());
		slv.assert_all_solutions(&vars, |sol| {
			sol.iter()
				.enumerate()
				.all(|(i, v)| *v == crate::solver::Value::Int(i as IntVal + 1))
		});
	}

	#[test]
	#[traced_test]
	fn test_all_different_domain_filtering() {
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
	fn test_all_different_domain_hall_set_reason_soundness() {
		// Regression: the Hall-set explanation must stay sound. When an SCC's
		// values are pruned from outside variables, the reason is only valid if
		// every Hall-set member is confined to the SCC's value set `V`. If a
		// member still holds an out-of-`V` value (a residual edge left behind by a
		// prune/backtrack), the Hall set is non-tight and the nogood is too weak,
		// wrongly cutting feasible assignments. Minimizing `x[0]` below, the true
		// optimum is 2 (witness `[2, 1, 4, 3, 7, 5, 8]`, all-different); the buggy
		// propagator excluded `x[0] = 2` and proved 3.
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

	#[test]
	#[traced_test]
	fn test_all_different_domain_interior_hole() {
		// One test covering the distinguishing behaviours of the domain
		// propagator at once:
		// - The universe (1..=6) exceeds the variable count, so the matching leaves
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
	fn test_all_different_domain_sat() {
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
	fn test_all_different_domain_unsat() {
		// Three variables on {1,2}: Hall set, no matching exists.
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
}
