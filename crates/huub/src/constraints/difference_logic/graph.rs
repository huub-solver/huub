//! The difference logic graph and the incremental algorithms over it.
//!
//! Both layers share this, generic over how nodes are named: the model uses its
//! own views while it simplifies, the solver the solver's during search. The
//! algorithms are the paper's `IncSat`, `IncLB`, and `IncUB`, which repair the
//! potential function and push bounds along shortest paths as edges activate.

use std::mem;

use itertools::Itertools;
use rustc_hash::FxHashSet;
use tracing::trace;

use crate::{
	DeepClone, IntVal,
	actions::{
		ConstructionActions, IntEvent, IntInspectionActions, PropagationActions,
		PropagationContext, ReasonActions, ReasoningContext, ReasoningEngine, Trailed,
		TrailingActions,
	},
	constraints::{BoolSolverActions, IntSolverActions, reason_ty},
	helpers::{
		priority_queue::IndexedPriorityQueue, trailed_list::TrailedList,
		trailed_open_list::TrailedOpenList,
	},
	lower::LoweringContext,
	solver::IntLitMeaning,
};

/// An edge of the difference logic graph: `int_dcns[from] - int_dcns[to] ≤
/// val`, conditional on `bool_dcns[bool_dcn]` when it is set.
#[derive(Clone, Debug, DeepClone)]
pub(super) struct DiffEdge {
	/// Source node.
	pub(super) from: usize,
	/// Target node.
	pub(super) to: usize,
	/// Weight, i.e. the bound on the difference.
	pub(super) val: IntVal,
	/// The Boolean that must hold for this edge to be active, or `None` if the
	/// edge is globally active.
	pub(super) bool_dcn: Option<usize>,
	/// Position of this edge in `bool_implications[bool_dcn]`.
	pub(super) bool_index: usize,
	/// Position of this edge in `open_out[from]`.
	pub(super) out_index: usize,
	/// Position of this edge in `open_in[to]`.
	pub(super) in_index: usize,
	/// Position of this edge in `active_out[from]`, while it is active.
	pub(super) active_out_index: usize,
	/// Position of this edge in `active_in[to]`, while it is active.
	pub(super) active_in_index: usize,
}

/// The difference logic graph, generic over how its nodes and gates are named:
/// [`ModelNode`](crate::constraints::difference_logic::ModelNode) and model
/// Boolean views while the model is simplified,
/// [`SolverNode`](crate::constraints::difference_logic::SolverNode) and solver
/// Boolean decisions during search.
///
/// Each node keeps four adjacency lists — active and implied, incoming and
/// outgoing — and each Boolean keeps the implied edges it gates. An implied
/// edge is therefore in three lists at once, and stores its position in each so
/// that closing it is constant time in all three.
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct DifferenceLogicGraph<I, B> {
	/// The integer view each node stands for.
	pub(super) int_dcns: Vec<I>,
	/// The Boolean view each gate stands for.
	pub(super) bool_dcns: Vec<B>,
	/// Active outgoing edges per node.
	pub(super) active_out: Vec<TrailedList<usize>>,
	/// Active incoming edges per node.
	pub(super) active_in: Vec<TrailedList<usize>>,
	/// Implied outgoing edges per node that are still open.
	pub(super) open_out: Vec<TrailedOpenList<usize>>,
	/// Implied incoming edges per node that are still open.
	pub(super) open_in: Vec<TrailedOpenList<usize>>,
	/// Implied edges per Boolean that are still open.
	pub(super) bool_implications: Vec<TrailedOpenList<usize>>,
	/// Every edge, active or implied, referenced by index from the lists above.
	pub(super) edges: Vec<DiffEdge>,
	/// Johnson potential function, keeping reduced edge weights non-negative so
	/// Dijkstra can be used on a graph with negative weights.
	pub(super) pi: Vec<IntVal>,
	/// A cache of the lower bound of each node, to spare the hot loops a
	/// lookup of the decision.
	///
	/// It holds the bound that the graph last derived or was last told about,
	/// and is never filled from a lookup: an unreported change, such as a jump
	/// over a hole in the domain, would then look like no change when its
	/// report arrives. The cache may therefore be weaker than the bound of the
	/// decision, which is safe. A reported bound equal to the cached one is
	/// the graph's own change and needs no propagation.
	pub(super) derived_min: Vec<Option<IntVal>>,
	/// A cache of the upper bound of each node; see [`Self::derived_min`].
	pub(super) derived_max: Vec<Option<IntVal>>,
	/// Nodes with an entry in `derived_min`, to reset it cheaply.
	pub(super) derived_min_updates: Vec<usize>,
	/// Nodes with an entry in `derived_max`, to reset it cheaply.
	pub(super) derived_max_updates: Vec<usize>,
	/// Nodes whose lower bound changed and that still need propagating.
	pub(super) min_changes: FxHashSet<usize>,
	/// Nodes whose upper bound changed and that still need propagating.
	pub(super) max_changes: FxHashSet<usize>,
	/// Booleans reported fixed that still need propagating.
	pub(super) fixed_bools: FxHashSet<usize>,
	/// Predecessor of each node on the shortest path most recently found, used
	/// to reconstruct the reason for a propagation or a negative cycle.
	pub(super) backtrace: Vec<Option<(usize, Option<usize>)>>,
	/// Whether each node has been settled by the running search.
	pub(super) visited: Vec<bool>,
	/// Nodes marked in `visited`, to reset it cheaply.
	pub(super) visited_updates: Vec<usize>,
	/// The potential of each node before the running `inc_sat` changed it.
	pub(super) pi_undo: Vec<(usize, IntVal)>,
	/// Scratch queue, reused across searches to avoid reallocating it on every
	/// propagation.
	pub(super) queue: IndexedPriorityQueue<IntVal>,
}

impl DiffEdge {
	/// The gate of an implied edge. Panics on a globally active edge.
	pub(super) fn gate(&self) -> usize {
		self.bool_dcn.expect("edge is globally active")
	}

	/// Create an edge, with its positions in the lists still unset.
	pub(super) fn new(from: usize, to: usize, val: IntVal, bool_dcn: Option<usize>) -> Self {
		Self {
			from,
			to,
			val,
			bool_dcn,
			bool_index: 0,
			out_index: 0,
			in_index: 0,
			active_out_index: 0,
			active_in_index: 0,
		}
	}
}

impl<I, B> DifferenceLogicGraph<I, B> {
	/// Extend the graph with a node, without any edges.
	pub(super) fn add_node(&mut self, ctx: &mut (impl ConstructionActions + ?Sized)) {
		self.active_out.push(TrailedList::new(ctx));
		self.active_in.push(TrailedList::new(ctx));
		self.open_out.push(TrailedOpenList::new(ctx));
		self.open_in.push(TrailedOpenList::new(ctx));
		self.pi.push(0);
		self.derived_min.push(None);
		self.derived_max.push(None);
		self.backtrace.push(None);
		self.visited.push(false);
		let n = self.pi.len() - 1;
		// A fresh node has never been propagated, so both of its bounds count
		// as changed.
		let _ = self.min_changes.insert(n);
		let _ = self.max_changes.insert(n);
	}

	/// Every live edge with `n` as an endpoint, active or implied.
	///
	/// The trailed lengths are read through `trailed`, because the model reads
	/// its own trail where lowering reads the model's from the solver side.
	/// A self-loop is left out: it constrains no other node.
	pub(super) fn edges_at(
		&self,
		n: usize,
		trailed: impl Fn(Trailed<usize>) -> usize,
	) -> Vec<usize> {
		let mut edges = Vec::new();
		for list in [&self.active_out[n], &self.active_in[n]] {
			edges.extend(list.iter_upto(trailed(list.len_slot())).copied());
		}
		for list in [&self.open_out[n], &self.open_in[n]] {
			edges.extend(
				list.open_indices_from(trailed(list.closed_slot()))
					.map(|i| *list.at(i)),
			);
		}
		edges.retain(|&e| self.edges[e].from != self.edges[e].to);
		edges
	}

	/// Whether an edge is implied and still open.
	pub(super) fn is_open(&self, ctx: &(impl TrailingActions + ?Sized), e: usize) -> bool {
		let edge = &self.edges[e];
		edge.bool_dcn.is_some()
			&& edge.out_index >= ctx.trailed(self.open_out[edge.from].closed_slot())
	}

	/// The number of nodes, active or not.
	pub(super) fn num_nodes(&self) -> usize {
		self.int_dcns.len()
	}

	/// Whether every given edge has a non-negative reduced cost under
	/// [`Self::pi`], the invariant that the shortest path searches rely on.
	pub(super) fn potential_is_feasible(&self, edges: impl IntoIterator<Item = usize>) -> bool {
		edges.into_iter().all(|e| {
			let edge = &self.edges[e];
			self.pi[edge.from] + edge.val >= self.pi[edge.to]
		})
	}

	/// Forget every cached bound and pending bound change.
	pub(super) fn reset_bounds(&mut self) {
		self.min_changes.clear();
		self.max_changes.clear();
		for &n in &self.derived_min_updates {
			self.derived_min[n] = None;
		}
		for &n in &self.derived_max_updates {
			self.derived_max[n] = None;
		}
		self.derived_min_updates.clear();
		self.derived_max_updates.clear();
	}

	/// Forget the visited marks, in time proportional to the number set.
	pub(super) fn reset_visit(&mut self) {
		for &n in &self.visited_updates {
			self.visited[n] = false;
		}
		self.visited_updates.clear();
	}

	/// Record an upper bound for a node, unless a tighter one is cached.
	pub(super) fn update_max(&mut self, n: usize, val: IntVal) {
		match &mut self.derived_max[n] {
			Some(cached) => *cached = val.min(*cached),
			cached @ None => {
				*cached = Some(val);
				self.derived_max_updates.push(n);
			}
		}
	}

	/// Record a lower bound for a node, unless a tighter one is cached.
	pub(super) fn update_min(&mut self, n: usize, val: IntVal) {
		match &mut self.derived_min[n] {
			Some(cached) => *cached = val.max(*cached),
			cached @ None => {
				*cached = Some(val);
				self.derived_min_updates.push(n);
			}
		}
	}

	/// Mark a node as settled.
	pub(super) fn visit(&mut self, n: usize) {
		if !self.visited[n] {
			self.visited_updates.push(n);
		}
		self.visited[n] = true;
	}
}

impl<I: Clone, B: Clone> DifferenceLogicGraph<I, B> {
	/// Add an edge to the active lists of its endpoints. An implied edge must
	/// first be closed with [`Self::close_imp_edge`].
	pub(super) fn activate_imp_edge(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		index: usize,
	) {
		self.push_active_out(ctx, index);
		self.push_active_in(ctx, index);
	}

	/// Close an implied edge in all three lists it belongs to.
	pub(super) fn close_imp_edge(&mut self, ctx: &mut (impl TrailingActions + ?Sized), e: usize) {
		let edge = &self.edges[e];
		let (b, from, to) = (edge.gate(), edge.from, edge.to);
		let (bool_index, out_index, in_index) = (edge.bool_index, edge.out_index, edge.in_index);
		// Each list reports the elements it moved so the edges' reverse indices
		// stay correct. `&` rather than `&&` so all three always run.
		let was_open = self.bool_implications[b]
			.close(ctx, bool_index, |&e, i| self.edges[e].bool_index = i)
			& self.open_out[from].close(ctx, out_index, |&e, i| self.edges[e].out_index = i)
			& self.open_in[to].close(ctx, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert!(was_open, "closing an edge that was already closed");
	}

	/// Add an edge and return its index. An edge with a gate starts out
	/// implied; one without is active from the start.
	pub(super) fn new_edge(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		mut edge: DiffEdge,
	) -> usize {
		let index = self.edges.len();
		if let Some(b) = edge.bool_dcn {
			edge.bool_index = self.bool_implications[b].total_len();
			self.bool_implications[b].push(index);
			edge.out_index = self.open_out[edge.from].total_len();
			self.open_out[edge.from].push(index);
			edge.in_index = self.open_in[edge.to].total_len();
			self.open_in[edge.to].push(index);
			self.edges.push(edge);
		} else {
			self.edges.push(edge);
			self.activate_imp_edge(ctx, index);
		}
		index
	}

	/// Append an edge to the active incoming list of its target.
	pub(super) fn push_active_in(&mut self, ctx: &mut (impl TrailingActions + ?Sized), e: usize) {
		let to = self.edges[e].to;
		self.edges[e].active_in_index = self.active_in[to].push(ctx, e);
	}

	/// Append an edge to the active outgoing list of its source.
	pub(super) fn push_active_out(&mut self, ctx: &mut (impl TrailingActions + ?Sized), e: usize) {
		let from = self.edges[e].from;
		self.edges[e].active_out_index = self.active_out[from].push(ctx, e);
	}

	/// Remove an active edge from both of its lists. Root only, as its two
	/// halves are.
	pub(super) fn remove_active_edge(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		e: usize,
	) {
		self.remove_active_out(ctx, e);
		self.remove_active_in(ctx, e);
	}

	/// Remove an active edge from the incoming list of its target.
	///
	/// This removal is permanent, so it may only be used at the root; see
	/// [`TrailedList`].
	pub(super) fn remove_active_in(&mut self, ctx: &mut (impl TrailingActions + ?Sized), e: usize) {
		let (to, i) = (self.edges[e].to, self.edges[e].active_in_index);
		debug_assert_eq!(*self.active_in[to].index(ctx, i), e);
		if let Some(&moved) = self.active_in[to].swap_remove(ctx, i) {
			self.edges[moved].active_in_index = i;
		}
	}

	/// Remove an active edge from the outgoing list of its source.
	///
	/// This removal is permanent, so it may only be used at the root; see
	/// [`TrailedList`].
	pub(super) fn remove_active_out(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		e: usize,
	) {
		let (from, i) = (self.edges[e].from, self.edges[e].active_out_index);
		debug_assert_eq!(*self.active_out[from].index(ctx, i), e);
		if let Some(&moved) = self.active_out[from].swap_remove(ctx, i) {
			self.edges[moved].active_out_index = i;
		}
	}
}

impl<I, B> DifferenceLogicGraph<I, B> {
	/// The upper bound of a node, from the cache when it has one.
	pub(super) fn cur_max<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.derived_max[n].unwrap_or_else(|| self.int_dcns[n].max(ctx))
	}

	/// The lower bound of a node, from the cache when it has one.
	pub(super) fn cur_min<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.derived_min[n].unwrap_or_else(|| self.int_dcns[n].min(ctx))
	}

	/// Note the bound changes an integer event reports for node `n`, reporting
	/// whether any of them is new.
	pub(super) fn notify_int_change<Ctx>(&mut self, ctx: &Ctx, n: usize, event: IntEvent) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		let mut enqueue = false;
		if matches!(
			event,
			IntEvent::LowerBound | IntEvent::Bounds | IntEvent::Fixed
		) {
			enqueue = self.notify_min_change(ctx, n);
		}
		if matches!(
			event,
			IntEvent::UpperBound | IntEvent::Bounds | IntEvent::Fixed
		) {
			enqueue |= self.notify_max_change(ctx, n);
		}
		enqueue
	}

	/// Note an upper bound change, reporting whether it is new.
	pub(super) fn notify_max_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		let max = self.int_dcns[n].max(ctx);
		if self.derived_max[n].is_none_or(|cached| cached > max) {
			self.update_max(n, max);
			return self.max_changes.insert(n);
		}
		false
	}

	/// Note a lower bound change, reporting whether it is new.
	pub(super) fn notify_min_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		let min = self.int_dcns[n].min(ctx);
		if self.derived_min[n].is_none_or(|cached| cached < min) {
			self.update_min(n, min);
			return self.min_changes.insert(n);
		}
		false
	}
}

impl<I, B> DifferenceLogicGraph<I, B>
where
	I: Clone,
	B: Clone,
{
	/// Build the solver's graph from the model's, keeping only the nodes,
	/// Booleans, and edges that survived simplification.
	///
	/// The source's trailed lengths live on the *model* trail, read through
	/// [`LoweringContext::model_trailed`](crate::lower::LoweringContext::model_trailed);
	/// the new graph's live on the solver trail this writes to.
	pub(super) fn from_model<I1, B1>(
		src: &DifferenceLogicGraph<I1, B1>,
		ctx: &mut LoweringContext<'_>,
		int_dcns: Vec<I>,
		bool_dcns: Vec<B>,
		node_map: &[Option<usize>],
		bool_map: &[Option<usize>],
		offsets: &[IntVal],
	) -> Self {
		// Whether each source edge is active (1) or still implied (2) for a
		// node that survived.
		let mut edge_state = vec![0_u8; src.edges.len()];
		for (n, _) in node_map.iter().enumerate().filter(|(_, m)| m.is_some()) {
			let active = ctx.model_trailed(src.active_out[n].len_slot());
			for &e in src.active_out[n].iter_upto(active) {
				edge_state[e] = 1;
			}
			let closed = ctx.model_trailed(src.open_out[n].closed_slot());
			for i in src.open_out[n].open_indices_from(closed) {
				edge_state[*src.open_out[n].at(i)] = 2;
			}
		}

		// The adjacency is known up front and nothing is trailed yet, so the
		// lists are built at their final length.
		let (num_nodes, num_bools) = (int_dcns.len(), bool_dcns.len());
		let mut active_out = vec![Vec::new(); num_nodes];
		let mut active_in = vec![Vec::new(); num_nodes];
		let mut open_out = vec![Vec::new(); num_nodes];
		let mut open_in = vec![Vec::new(); num_nodes];
		let mut bool_implications = vec![Vec::new(); num_bools];
		let mut edges = Vec::new();

		for (e, edge) in src.edges.iter().enumerate() {
			if edge_state[e] == 0 {
				continue;
			}
			// An edge onto a node that did not survive has already been encoded
			// as clauses by `DifferenceLogicModel::encode_dissolved_node`.
			let (Some(from), Some(to)) = (node_map[edge.from], node_map[edge.to]) else {
				continue;
			};
			let index = edges.len();
			// `from - to ≤ w` over nodes carrying the offsets lowering gave
			// them is `S_from - S_to ≤ w - o_from + o_to` over the bare ones.
			let val = edge.val - offsets[edge.from] + offsets[edge.to];
			let mut new_edge = DiffEdge::new(from, to, val, None);
			if edge_state[e] == 1 {
				new_edge.active_out_index = active_out[from].len();
				active_out[from].push(index);
				new_edge.active_in_index = active_in[to].len();
				active_in[to].push(index);
			} else {
				let b = bool_map[edge.gate()].expect("implied edge on a removed Boolean");
				new_edge.bool_dcn = Some(b);
				new_edge.bool_index = bool_implications[b].len();
				bool_implications[b].push(index);
				new_edge.out_index = open_out[from].len();
				open_out[from].push(index);
				new_edge.in_index = open_in[to].len();
				open_in[to].push(index);
			}
			edges.push(new_edge);
		}

		let graph = Self {
			// The solver reports the bound changes it makes from here on, so
			// nothing starts out queued as changed.
			min_changes: FxHashSet::default(),
			max_changes: FxHashSet::default(),
			// The offsets moved into the edge weights shift the potential by
			// the same amount, which keeps every reduced cost unchanged.
			pi: src
				.pi
				.iter()
				.zip(offsets)
				.zip(node_map)
				.filter_map(|((&pi, &offset), mapped)| mapped.map(|_| pi + offset))
				.collect_vec(),
			active_out: active_out
				.into_iter()
				.map(|l| TrailedList::from_active(ctx, l))
				.collect(),
			active_in: active_in
				.into_iter()
				.map(|l| TrailedList::from_active(ctx, l))
				.collect(),
			open_out: open_out
				.into_iter()
				.map(|l| TrailedOpenList::from_open(ctx, l))
				.collect(),
			open_in: open_in
				.into_iter()
				.map(|l| TrailedOpenList::from_open(ctx, l))
				.collect(),
			bool_implications: bool_implications
				.into_iter()
				.map(|l| TrailedOpenList::from_open(ctx, l))
				.collect(),
			edges,
			int_dcns,
			bool_dcns,
			derived_min: vec![None; num_nodes],
			derived_max: vec![None; num_nodes],
			derived_min_updates: Vec::new(),
			derived_max_updates: Vec::new(),
			fixed_bools: FxHashSet::default(),
			backtrace: vec![None; num_nodes],
			visited: vec![false; num_nodes],
			visited_updates: Vec::new(),
			pi_undo: Vec::new(),
			queue: IndexedPriorityQueue::default(),
		};
		// Only the active edges bind the potential; an implied edge is checked
		// by `inc_sat` when it activates.
		debug_assert!(
			graph.potential_is_feasible(
				(0..graph.edges.len()).filter(|&e| graph.edges[e].bool_dcn.is_none())
			),
			"lowering left an active edge with a negative reduced cost"
		);
		graph
	}
}

impl<I, B> DifferenceLogicGraph<I, B>
where
	I: Clone,
	B: Clone,
{
	/// The reason for a negative cycle: the gates of the implied edges along
	/// it.
	pub(super) fn cycle_reason<Ctx>(
		&self,
		node: usize,
	) -> impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>)
	where
		Ctx: PropagationContext + ?Sized,
		B: Into<Ctx::Atom>,
	{
		let mut atoms = Vec::new();
		let mut node = node;
		while let Some((prev, b)) = self.backtrace[node] {
			if let Some(b) = b {
				atoms.push(self.bool_dcns[b].clone().into());
			}
			node = prev;
		}
		move |_, reason| reason.extend(atoms)
	}

	/// Propagate lower bounds forward along the shortest paths from the nodes
	/// whose lower bound changed.
	pub(super) fn inc_lb<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		trace!(target: "diff_logic", changes = ?self.min_changes, "running inc_lb");
		self.reset_visit();
		let pi0 = self
			.min_changes
			.iter()
			.map(|&n| self.cur_min(ctx, n) + self.pi[n])
			.max()
			.expect("inc_lb called without any lower bound change");

		let mut queue = mem::take(&mut self.queue);
		queue.clear();
		for &n in &self.min_changes {
			queue.push(n, pi0 - self.cur_min(ctx, n) - self.pi[n]);
		}
		let mut result = Ok(());
		while let Some((s, gamma_s)) = queue.pop() {
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			let min = self.cur_min(ctx, s);
			if bound <= min && !self.min_changes.contains(&s) {
				continue;
			}
			self.update_min(s, bound);
			if bound > min {
				trace!(target: "diff_logic", n = ?s, bound = ?bound, "updating lower bound");
				let (prev, b) = self.backtrace[s].expect("propagated node has no predecessor");
				let lb = self.cur_min(ctx, prev);
				result = self.set_min(ctx, s, bound, b, prev, lb);
				if result.is_err() {
					break;
				}
				let _ = self.min_changes.insert(s);
			}
			for &e in self.active_out[s].iter(ctx) {
				let edge = &self.edges[e];
				let (to, val, gate) = (edge.to, edge.val, edge.bool_dcn);
				if !self.visited[to] {
					let path = gamma_s + self.pi[s] + val - self.pi[to];
					if queue.push_decrease(to, path) {
						self.backtrace[to] = Some((s, gate));
					}
				}
			}
		}
		self.queue = queue;
		result
	}

	/// Repair the potential function for an edge that became active, or raise
	/// a conflict when the edge closes a negative cycle.
	pub(super) fn inc_sat<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
		new_index: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let new_edge = self.edges[new_index].clone();
		trace!(target: "diff_logic", from = new_edge.from, to = new_edge.to, val = new_edge.val, "inc_sat");
		// The potential is updated in place for each settled node, and the
		// old values kept so that a negative cycle can undo the update.
		self.reset_visit();
		self.pi_undo.clear();
		self.backtrace[new_edge.to] = None;

		let mut queue = mem::take(&mut self.queue);
		queue.clear();
		let gamma_v = self.pi[new_edge.from] + new_edge.val - self.pi[new_edge.to];
		if gamma_v < 0 {
			queue.push(new_edge.to, gamma_v);
		}
		while !queue.contains(new_edge.from)
			&& let Some((s, gamma_s)) = queue.pop()
		{
			self.visit(s);
			self.pi_undo.push((s, self.pi[s]));
			self.pi[s] += gamma_s;
			for &e in self.active_out[s].iter(ctx) {
				let edge = &self.edges[e];
				let (to, val, gate) = (edge.to, edge.val, edge.bool_dcn);
				if self.visited[to] {
					continue;
				}
				let gamma_t = self.pi[s] + val - self.pi[to];
				if gamma_t < 0 && queue.push_decrease(to, gamma_t) {
					self.backtrace[to] = Some((s, gate));
				}
			}
		}
		let cycle = queue.contains(new_edge.from);
		self.queue = queue;

		if cycle {
			for &(n, pi) in &self.pi_undo {
				self.pi[n] = pi;
			}
			trace!(target: "diff_logic", gate = ?new_edge.bool_dcn, "cycle of negative length");
			let reason = self.cycle_reason(new_edge.from);
			// The gate of an active edge holds, so falsifying it is the
			// conflict, with the gate in its reason.
			return match new_edge.bool_dcn {
				Some(b) => self.bool_dcns[b].clone().fix(ctx, false, reason),
				None => Err(ctx.declare_conflict(reason)),
			};
		}
		Ok(())
	}

	/// Propagate upper bounds backward along the shortest paths into the nodes
	/// whose upper bound changed.
	pub(super) fn inc_ub<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		trace!(target: "diff_logic", changes = ?self.max_changes, "running inc_ub");
		self.reset_visit();
		let pi0 = self
			.max_changes
			.iter()
			.map(|&n| self.cur_max(ctx, n) + self.pi[n])
			.min()
			.expect("inc_ub called without any upper bound change");

		let mut queue = mem::take(&mut self.queue);
		queue.clear();
		for &n in &self.max_changes {
			queue.push(n, self.pi[n] + self.cur_max(ctx, n) - pi0);
		}
		let mut result = Ok(());
		while let Some((s, gamma_s)) = queue.pop() {
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			let max = self.cur_max(ctx, s);
			if bound >= max && !self.max_changes.contains(&s) {
				continue;
			}
			self.update_max(s, bound);
			if bound < max {
				trace!(target: "diff_logic", n = ?s, bound = ?bound, "updating upper bound");
				let (prev, b) = self.backtrace[s].expect("propagated node has no predecessor");
				let ub = self.cur_max(ctx, prev);
				result = self.set_max(ctx, s, bound, b, prev, ub);
				if result.is_err() {
					break;
				}
				let _ = self.max_changes.insert(s);
			}
			for &e in self.active_in[s].iter(ctx) {
				let edge = &self.edges[e];
				let (from, val, gate) = (edge.from, edge.val, edge.bool_dcn);
				if !self.visited[from] {
					let path = gamma_s + self.pi[from] + val - self.pi[s];
					if queue.push_decrease(from, path) {
						self.backtrace[from] = Some((s, gate));
					}
				}
			}
		}
		self.queue = queue;
		result
	}

	/// Activate the edges of Booleans fixed to true and drop those of Booleans
	/// fixed to false.
	pub(super) fn propagate_booleans<E, const UPDATE_LOCAL_BOUNDS: bool>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let mut fixed_bools = mem::take(&mut self.fixed_bools);
		let result = fixed_bools.drain().try_for_each(|b| {
			let val = self.bool_dcns[b]
				.val(ctx)
				.expect("Boolean reported as fixed is unassigned");
			trace!(target: "diff_logic", b = ?b, val = ?val, "Boolean fixed");
			// Closing the edge at `j` only swaps in an edge from before `j`, so
			// every later position still holds an edge not yet visited.
			for j in self.bool_implications[b].open_indices(ctx) {
				let e = *self.bool_implications[b].at(j);
				self.close_imp_edge(ctx, e);
				if val {
					self.activate_imp_edge(ctx, e);
					self.propagate_edge_addition::<E, UPDATE_LOCAL_BOUNDS>(ctx, e)?;
				}
			}
			Ok(())
		});
		debug_assert!(self.fixed_bools.is_empty());
		self.fixed_bools = fixed_bools;
		result
	}

	/// Propagate every pending bound change, then check the open edges that the
	/// new bounds entail or falsify.
	pub(super) fn propagate_bounds<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		if !self.min_changes.is_empty() {
			self.inc_lb(ctx)?;
		}
		if !self.max_changes.is_empty() {
			self.inc_ub(ctx)?;
		}

		let mut min_changes = mem::take(&mut self.min_changes);
		let result = min_changes.drain().try_for_each(|n| {
			let lb = self.cur_min(ctx, n);
			for i in self.open_out[n].open_indices(ctx) {
				let e = *self.open_out[n].at(i);
				let edge = &self.edges[e];
				let (to, val) = (edge.to, edge.val);
				if lb - self.cur_max(ctx, to) > val {
					trace!(target: "diff_logic", e = ?e, "edge is falsified by its bounds");
					self.set_bool_false(ctx, e, true)?;
					self.close_imp_edge(ctx, e);
				}
			}
			for i in self.open_in[n].open_indices(ctx) {
				let e = *self.open_in[n].at(i);
				let edge = &self.edges[e];
				let (from, val) = (edge.from, edge.val);
				if self.cur_max(ctx, from) - lb <= val {
					trace!(target: "diff_logic", e = ?e, "edge is entailed by its bounds");
					self.close_imp_edge(ctx, e);
				}
			}
			Ok(())
		});
		debug_assert!(self.min_changes.is_empty());
		self.min_changes = min_changes;
		result?;

		let mut max_changes = mem::take(&mut self.max_changes);
		let result = max_changes.drain().try_for_each(|n| {
			let ub = self.cur_max(ctx, n);
			for i in self.open_out[n].open_indices(ctx) {
				let e = *self.open_out[n].at(i);
				let edge = &self.edges[e];
				let (to, val) = (edge.to, edge.val);
				if ub - self.cur_min(ctx, to) <= val {
					trace!(target: "diff_logic", e = ?e, "edge is entailed by its bounds");
					self.close_imp_edge(ctx, e);
				}
			}
			for i in self.open_in[n].open_indices(ctx) {
				let e = *self.open_in[n].at(i);
				let edge = &self.edges[e];
				let (from, val) = (edge.from, edge.val);
				if self.cur_min(ctx, from) - ub > val {
					trace!(target: "diff_logic", e = ?e, "edge is falsified by its bounds");
					self.set_bool_false(ctx, e, false)?;
					self.close_imp_edge(ctx, e);
				}
			}
			Ok(())
		});
		debug_assert!(self.max_changes.is_empty());
		self.max_changes = max_changes;
		result
	}

	/// Check the consequences of an edge becoming active: a negative cycle is a
	/// conflict, and otherwise the bounds of its endpoints are tightened across
	/// the edge.
	///
	/// With `UPDATE_LOCAL_BOUNDS`, the new bounds are noted as changes right
	/// away, for an engine that does not advise the caller of its own changes.
	pub(super) fn propagate_edge_addition<E, const UPDATE_LOCAL_BOUNDS: bool>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
		e: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		self.inc_sat(ctx, e)?;

		let (from, to, val, gate) = {
			let edge = &self.edges[e];
			(edge.from, edge.to, edge.val, edge.bool_dcn)
		};
		let source_lb = self.cur_min(ctx, from);
		let target_lb = source_lb - val;
		if target_lb > self.cur_min(ctx, to) {
			self.set_min(ctx, to, target_lb, gate, from, source_lb)?;
			if UPDATE_LOCAL_BOUNDS {
				let _ = self.notify_min_change(ctx, to);
			}
		}
		let target_ub = self.cur_max(ctx, to);
		let source_ub = target_ub + val;
		if source_ub < self.cur_max(ctx, from) {
			self.set_max(ctx, from, source_ub, gate, to, target_ub)?;
			if UPDATE_LOCAL_BOUNDS {
				let _ = self.notify_max_change(ctx, from);
			}
		}
		Ok(())
	}

	/// Falsify the gate of an implied edge that the bounds have ruled out.
	///
	/// `min_triggered` records whether the source's lower bound was the
	/// trigger, so that the other bound can be lifted to the weakest value
	/// that still falsifies the edge.
	pub(super) fn set_bool_false<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
		e: usize,
		min_triggered: bool,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let edge = &self.edges[e];
		let mut lb = self.cur_min(ctx, edge.from);
		let mut ub = self.cur_max(ctx, edge.to);
		if min_triggered {
			ub = lb - edge.val - 1;
		} else {
			lb = ub + edge.val + 1;
		}
		let (from, to) = (
			self.int_dcns[edge.from].clone(),
			self.int_dcns[edge.to].clone(),
		);
		let reason = reason_ty::<E::PropagationContext<'_>, _>(move |ctx, reason| {
			let lb_lit = from.lit(ctx, IntLitMeaning::GreaterEq(lb));
			let ub_lit = to.lit(ctx, IntLitMeaning::Less(ub + 1));
			ReasonActions::push(reason, lb_lit);
			ReasonActions::push(reason, ub_lit);
		});
		self.bool_dcns[edge.gate()].clone().fix(ctx, false, reason)
	}

	/// Tighten `int_dcns[n]` to at most `value`, because `int_dcns[cause_node]`
	/// is at most `cause_max` and the gate holds.
	pub(super) fn set_max<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		n: usize,
		value: IntVal,
		bool_dcn: Option<usize>,
		cause_node: usize,
		cause_max: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let cause = self.int_dcns[cause_node].clone();
		let gate = bool_dcn.map(|b| self.bool_dcns[b].clone());
		self.int_dcns[n].tighten_max(ctx, value, move |ctx, reason| {
			let lit = cause.lit(ctx, IntLitMeaning::Less(cause_max + 1));
			ReasonActions::push(reason, lit);
			if let Some(gate) = gate {
				ReasonActions::push(reason, gate.into());
			}
		})
	}

	/// Tighten `int_dcns[n]` to at least `value`, because
	/// `int_dcns[cause_node]` is at least `cause_min` and the gate holds.
	pub(super) fn set_min<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		n: usize,
		value: IntVal,
		bool_dcn: Option<usize>,
		cause_node: usize,
		cause_min: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let cause = self.int_dcns[cause_node].clone();
		let gate = bool_dcn.map(|b| self.bool_dcns[b].clone());
		self.int_dcns[n].tighten_min(ctx, value, move |ctx, reason| {
			let lit = cause.lit(ctx, IntLitMeaning::GreaterEq(cause_min));
			ReasonActions::push(reason, lit);
			if let Some(gate) = gate {
				ReasonActions::push(reason, gate.into());
			}
		})
	}
}

impl<I, B> Default for DifferenceLogicGraph<I, B> {
	fn default() -> Self {
		Self {
			int_dcns: Vec::new(),
			bool_dcns: Vec::new(),
			active_out: Vec::new(),
			active_in: Vec::new(),
			open_out: Vec::new(),
			open_in: Vec::new(),
			bool_implications: Vec::new(),
			edges: Vec::new(),
			pi: Vec::new(),
			derived_min: Vec::new(),
			derived_max: Vec::new(),
			derived_min_updates: Vec::new(),
			derived_max_updates: Vec::new(),
			min_changes: FxHashSet::default(),
			max_changes: FxHashSet::default(),
			fixed_bools: FxHashSet::default(),
			backtrace: Vec::new(),
			visited: Vec::new(),
			visited_updates: Vec::new(),
			pi_undo: Vec::new(),
			queue: IndexedPriorityQueue::default(),
		}
	}
}
