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

/// An edge of the difference logic graph: `int_vars[from] - int_vars[to] ≤
/// val`, conditional on `bool_vars[bool_var]` when it is set.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub(super) struct DiffEdge {
	/// Source node.
	pub(super) from: usize,
	/// Target node.
	pub(super) to: usize,
	/// Weight, i.e. the bound on the difference.
	pub(super) val: IntVal,
	/// The Boolean that must hold for this edge to be active, or `None` if the
	/// edge is globally active.
	pub(super) bool_var: Option<usize>,
	/// Position of this edge in `bool_implications[bool_var]`.
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

/// The difference logic graph, generic over how its integer and Boolean nodes
/// are named: [`model::View`] while the model is simplified,
/// [`solver::View`] during search.
///
/// Each node keeps four adjacency lists — active and implied, incoming and
/// outgoing — and each Boolean keeps the implied edges it gates. An implied
/// edge is therefore in three lists at once, and stores its position in each so
/// that closing it is constant time in all three.
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct DifferenceLogicGraph<I, B> {
	/// The integer view each node stands for.
	pub(super) int_vars: Vec<I>,
	/// The Boolean view each gate stands for.
	pub(super) bool_vars: Vec<B>,
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
	/// Lower bound derived for each node during the current propagation, ahead
	/// of what the solver has been told.
	pub(super) lower_bound: Vec<Option<IntVal>>,
	/// Upper bound derived for each node during the current propagation, ahead
	/// of what the solver has been told.
	pub(super) upper_bound: Vec<Option<IntVal>>,
	/// Nodes with an entry in `lower_bound`, to reset it cheaply.
	pub(super) lb_updates: Vec<usize>,
	/// Nodes with an entry in `upper_bound`, to reset it cheaply.
	pub(super) ub_updates: Vec<usize>,
	/// Nodes whose lower bound changed and still need propagating.
	pub(super) lower_bound_changes: FxHashSet<usize>,
	/// Nodes whose upper bound changed and still need propagating.
	pub(super) upper_bound_changes: FxHashSet<usize>,
	/// Booleans reported fixed and still need propagating.
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
		self.bool_var.expect("edge is globally active")
	}

	/// Create an edge, with its positions in the lists still unset.
	pub(super) fn new(from: usize, to: usize, val: IntVal, bool_var: Option<usize>) -> Self {
		Self {
			from,
			to,
			val,
			bool_var,
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
		self.lower_bound.push(None);
		self.upper_bound.push(None);
		self.backtrace.push(None);
		self.visited.push(false);
		let n = self.pi.len() - 1;
		// A fresh node has never been propagated, so both of its bounds count
		// as changed.
		let _ = self.lower_bound_changes.insert(n);
		let _ = self.upper_bound_changes.insert(n);
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

	/// Forget the bounds derived during the last propagation, keeping the
	/// pending bound changes.
	///
	/// Every derived bound has already been passed on to the decision, so the
	/// decision's own bound is at least as strong from here on.
	pub(super) fn forget_derived_bounds(&mut self) {
		for &n in &self.lb_updates {
			self.lower_bound[n] = None;
		}
		for &n in &self.ub_updates {
			self.upper_bound[n] = None;
		}
		self.lb_updates.clear();
		self.ub_updates.clear();
	}

	/// Whether an edge is implied and still open.
	pub(super) fn is_open(&self, ctx: &(impl TrailingActions + ?Sized), e: usize) -> bool {
		let edge = &self.edges[e];
		edge.bool_var.is_some()
			&& edge.out_index >= ctx.trailed(self.open_out[edge.from].closed_slot())
	}

	/// Create an empty graph over the given views.
	pub(super) fn new(
		ctx: &mut (impl ConstructionActions + ?Sized),
		int_vars: Vec<I>,
		bool_vars: Vec<B>,
	) -> Self {
		let num_int = int_vars.len();
		let num_bool = bool_vars.len();
		Self {
			int_vars,
			bool_vars,
			active_out: (0..num_int).map(|_| TrailedList::new(ctx)).collect(),
			active_in: (0..num_int).map(|_| TrailedList::new(ctx)).collect(),
			open_out: (0..num_int).map(|_| TrailedOpenList::new(ctx)).collect(),
			open_in: (0..num_int).map(|_| TrailedOpenList::new(ctx)).collect(),
			bool_implications: (0..num_bool).map(|_| TrailedOpenList::new(ctx)).collect(),
			edges: Vec::new(),
			pi: vec![0; num_int],
			lower_bound: vec![None; num_int],
			upper_bound: vec![None; num_int],
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			lower_bound_changes: (0..num_int).collect(),
			upper_bound_changes: (0..num_int).collect(),
			fixed_bools: FxHashSet::default(),
			backtrace: vec![None; num_int],
			visited: vec![false; num_int],
			visited_updates: Vec::new(),
			pi_undo: Vec::new(),
			queue: IndexedPriorityQueue::default(),
		}
	}

	/// The number of nodes, active or not.
	pub(super) fn num_nodes(&self) -> usize {
		self.int_vars.len()
	}

	/// Whether every given edge has a non-negative reduced cost under
	/// [`Self::pi`], the invariant that the shortest path searches rely on.
	pub(super) fn potential_is_feasible(&self, edges: impl IntoIterator<Item = usize>) -> bool {
		edges.into_iter().all(|e| {
			let edge = &self.edges[e];
			self.pi[edge.from] + edge.val >= self.pi[edge.to]
		})
	}

	/// Forget the bounds derived during the last propagation, and any pending
	/// bound change.
	pub(super) fn reset_bounds(&mut self) {
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		self.forget_derived_bounds();
	}

	/// Forget the visited marks, in time proportional to the number set.
	pub(super) fn reset_visit(&mut self) {
		for &n in &self.visited_updates {
			self.visited[n] = false;
		}
		self.visited_updates.clear();
	}

	/// Record a derived lower bound for a node.
	pub(super) fn update_lb(&mut self, n: usize, val: IntVal) {
		if self.lower_bound[n].is_none() {
			self.lb_updates.push(n);
		}
		self.lower_bound[n] = Some(val);
	}

	/// Record a derived upper bound for a node.
	pub(super) fn update_ub(&mut self, n: usize, val: IntVal) {
		if self.upper_bound[n].is_none() {
			self.ub_updates.push(n);
		}
		self.upper_bound[n] = Some(val);
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
	/// Make an implied edge active. Its gate must already have been closed with
	/// [`Self::close_imp_edge`].
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
		if let Some(b) = edge.bool_var {
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

	/// Remove an active edge from both of its lists.
	///
	/// This removal is permanent, so it may only be used at the root; see
	/// [`TrailedList`].
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
	/// The lower bound derived for a node during this propagation, or the
	/// solver's if none has been.
	pub(super) fn get_cur_lower_bound<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.lower_bound[n].unwrap_or_else(|| self.int_vars[n].min(ctx))
	}

	/// The upper bound derived for a node during this propagation, or the
	/// solver's if none has been.
	pub(super) fn get_cur_upper_bound<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		self.upper_bound[n].unwrap_or_else(|| self.int_vars[n].max(ctx))
	}

	/// Note the bound changes an integer event reports for node `n`, reporting
	/// whether any of them is new.
	pub(super) fn notify_int_change<Ctx>(&mut self, ctx: &Ctx, n: usize, event: IntEvent) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		let mut enqueue = false;
		if matches!(event, IntEvent::LowerBound | IntEvent::Fixed) {
			enqueue = self.notify_lb_change(ctx, n);
		}
		if matches!(event, IntEvent::UpperBound | IntEvent::Fixed) {
			enqueue |= self.notify_ub_change(ctx, n);
		}
		enqueue
	}

	/// Note a lower bound change, reporting whether it is new.
	pub(super) fn notify_lb_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		if self.lower_bound[n].is_none_or(|v| v < self.int_vars[n].min(ctx)) {
			return self.lower_bound_changes.insert(n);
		}
		false
	}

	/// Note an upper bound change, reporting whether it is new.
	pub(super) fn notify_ub_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		if self.upper_bound[n].is_none_or(|v| v > self.int_vars[n].max(ctx)) {
			return self.upper_bound_changes.insert(n);
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
		int_vars: Vec<I>,
		bool_vars: Vec<B>,
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
		let (num_nodes, num_bools) = (int_vars.len(), bool_vars.len());
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
				new_edge.bool_var = Some(b);
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
			lower_bound_changes: FxHashSet::default(),
			upper_bound_changes: FxHashSet::default(),
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
			int_vars,
			bool_vars,
			lower_bound: vec![None; num_nodes],
			upper_bound: vec![None; num_nodes],
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
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
				(0..graph.edges.len()).filter(|&e| graph.edges[e].bool_var.is_none())
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
		let mut var = node;
		while let Some((cur, b)) = self.backtrace[var] {
			if let Some(b) = b {
				atoms.push(self.bool_vars[b].clone().into());
			}
			var = cur;
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
		trace!(target: "diff_logic", changes = ?self.lower_bound_changes, "running inc_lb");
		self.reset_visit();
		let pi0 = self
			.lower_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].min(ctx) + self.pi[n])
			.max()
			.expect("inc_lb called without any lower bound change");

		let mut queue = mem::take(&mut self.queue);
		queue.clear();
		for &n in &self.lower_bound_changes {
			queue.push(n, pi0 - self.int_vars[n].min(ctx) - self.pi[n]);
		}
		let mut result = Ok(());
		while let Some((s, gamma_s)) = queue.pop() {
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			let min = self.int_vars[s].min(ctx);
			if bound <= self.lower_bound[s].unwrap_or(min) && !self.lower_bound_changes.contains(&s)
			{
				continue;
			}
			self.update_lb(s, bound);
			if bound > min {
				trace!(target: "diff_logic", n = ?s, bound = ?bound, "updating lower bound");
				let (prev, b) = self.backtrace[s].expect("propagated node has no predecessor");
				let lb = self.get_cur_lower_bound(ctx, prev);
				result = self.set_int_lower_bound(ctx, s, bound, b, prev, lb);
				if result.is_err() {
					break;
				}
				let _ = self.lower_bound_changes.insert(s);
			}
			for &e in self.active_out[s].iter(ctx) {
				let edge = &self.edges[e];
				let (to, val, gate) = (edge.to, edge.val, edge.bool_var);
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

	/// Whether adding the edge keeps the graph satisfiable, updating the
	/// potential function when it does.
	///
	/// A negative cycle falsifies the edge's gate, or raises a conflict when
	/// the edge is globally active.
	pub(super) fn inc_sat<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
		new_index: usize,
	) -> Result<bool, E::Conflict>
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
				let (to, val, gate) = (edge.to, edge.val, edge.bool_var);
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
			trace!(target: "diff_logic", gate = ?new_edge.bool_var, "cycle of negative length");
			let reason = self.cycle_reason(new_edge.from);
			if let Some(b) = new_edge.bool_var {
				self.bool_vars[b].clone().fix(ctx, false, reason)?;
			} else {
				return Err(ctx.declare_conflict(reason));
			}
			return Ok(false);
		}
		Ok(true)
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
		trace!(target: "diff_logic", changes = ?self.upper_bound_changes, "running inc_ub");
		self.reset_visit();
		let pi0 = self
			.upper_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].max(ctx) + self.pi[n])
			.min()
			.expect("inc_ub called without any upper bound change");

		let mut queue = mem::take(&mut self.queue);
		queue.clear();
		for &n in &self.upper_bound_changes {
			queue.push(n, self.pi[n] + self.int_vars[n].max(ctx) - pi0);
		}
		let mut result = Ok(());
		while let Some((s, gamma_s)) = queue.pop() {
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			let max = self.int_vars[s].max(ctx);
			if bound >= self.upper_bound[s].unwrap_or(max) && !self.upper_bound_changes.contains(&s)
			{
				continue;
			}
			self.update_ub(s, bound);
			if bound < max {
				trace!(target: "diff_logic", n = ?s, bound = ?bound, "updating upper bound");
				let (prev, b) = self.backtrace[s].expect("propagated node has no predecessor");
				let ub = self.get_cur_upper_bound(ctx, prev);
				result = self.set_int_upper_bound(ctx, s, bound, b, prev, ub);
				if result.is_err() {
					break;
				}
				let _ = self.upper_bound_changes.insert(s);
			}
			for &e in self.active_in[s].iter(ctx) {
				let edge = &self.edges[e];
				let (from, val, gate) = (edge.from, edge.val, edge.bool_var);
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
			let val = self.bool_vars[b]
				.val(ctx)
				.expect("Boolean reported as fixed is unassigned");
			trace!(target: "diff_logic", b = ?b, val = ?val, "Boolean fixed");
			// Closing the edge at `j` only swaps in an edge from before `j`, so
			// every later position still holds an edge not yet visited.
			for j in self.bool_implications[b].open_indices(ctx) {
				let e = *self.bool_implications[b].index(ctx, j);
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
		if !self.lower_bound_changes.is_empty() {
			self.inc_lb(ctx)?;
		}
		if !self.upper_bound_changes.is_empty() {
			self.inc_ub(ctx)?;
		}

		let mut lower_bound_changes = mem::take(&mut self.lower_bound_changes);
		let result = lower_bound_changes.drain().try_for_each(|n| {
			let lb = self.get_cur_lower_bound(ctx, n);
			for i in self.open_out[n].open_indices(ctx) {
				let e = *self.open_out[n].index(ctx, i);
				let edge = &self.edges[e];
				let (to, val, gate) = (edge.to, edge.val, edge.bool_var);
				if lb - self.get_cur_upper_bound(ctx, to) > val {
					trace!(target: "diff_logic", e = ?e, "edge is falsified by its bounds");
					// The lower bound was the trigger, so lifting relaxes the
					// upper bound of the target.
					self.set_bool_false(ctx, gate, e, false)?;
					self.close_imp_edge(ctx, e);
				}
			}
			for i in self.open_in[n].open_indices(ctx) {
				let e = *self.open_in[n].index(ctx, i);
				let edge = &self.edges[e];
				let (from, val) = (edge.from, edge.val);
				if self.get_cur_upper_bound(ctx, from) - lb <= val {
					trace!(target: "diff_logic", e = ?e, "edge is entailed by its bounds");
					self.close_imp_edge(ctx, e);
				}
			}
			Ok(())
		});
		debug_assert!(self.lower_bound_changes.is_empty());
		self.lower_bound_changes = lower_bound_changes;
		result?;

		let mut upper_bound_changes = mem::take(&mut self.upper_bound_changes);
		let result = upper_bound_changes.drain().try_for_each(|n| {
			let ub = self.get_cur_upper_bound(ctx, n);
			for i in self.open_out[n].open_indices(ctx) {
				let e = *self.open_out[n].index(ctx, i);
				let edge = &self.edges[e];
				let (to, val) = (edge.to, edge.val);
				if ub - self.get_cur_lower_bound(ctx, to) <= val {
					trace!(target: "diff_logic", e = ?e, "edge is entailed by its bounds");
					self.close_imp_edge(ctx, e);
				}
			}
			for i in self.open_in[n].open_indices(ctx) {
				let e = *self.open_in[n].index(ctx, i);
				let edge = &self.edges[e];
				let (from, val, gate) = (edge.from, edge.val, edge.bool_var);
				if self.get_cur_lower_bound(ctx, from) - ub > val {
					trace!(target: "diff_logic", e = ?e, "edge is falsified by its bounds");
					// The upper bound was the trigger, so lifting relaxes the
					// lower bound of the source.
					self.set_bool_false(ctx, gate, e, true)?;
					self.close_imp_edge(ctx, e);
				}
			}
			Ok(())
		});
		debug_assert!(self.upper_bound_changes.is_empty());
		self.upper_bound_changes = upper_bound_changes;
		result
	}

	/// Check the consequences of an edge becoming active: the graph may become
	/// unsatisfiable, other implied edges may be resolved, and the bounds of
	/// its endpoints may move.
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
		let added = self.inc_sat(ctx, e)?;
		debug_assert!(added, "an active edge must be addable or raise a conflict");

		let (from, to, val, gate) = {
			let edge = &self.edges[e];
			(edge.from, edge.to, edge.val, edge.bool_var)
		};
		let source_lb = self.get_cur_lower_bound(ctx, from);
		let target_lb = source_lb - val;
		if target_lb > self.get_cur_lower_bound(ctx, to) {
			self.set_int_lower_bound(ctx, to, target_lb, gate, from, source_lb)?;
			if UPDATE_LOCAL_BOUNDS {
				let _ = self.notify_lb_change(ctx, to);
				self.update_lb(to, target_lb);
			}
		}
		let target_ub = self.get_cur_upper_bound(ctx, to);
		let source_ub = target_ub + val;
		if source_ub < self.get_cur_upper_bound(ctx, from) {
			self.set_int_upper_bound(ctx, from, source_ub, gate, to, target_ub)?;
			if UPDATE_LOCAL_BOUNDS {
				let _ = self.notify_ub_change(ctx, from);
				self.update_ub(from, source_ub);
			}
		}
		Ok(())
	}

	/// Falsify the gate of an edge the bounds have ruled out, or raise a
	/// conflict when the edge is globally active.
	///
	/// `lb_fixed` records whether the source's lower bound was the trigger, so
	/// that the other bound can be lifted to the weakest value that still
	/// falsifies the edge.
	pub(super) fn set_bool_false<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
		bool_var: Option<usize>,
		e: usize,
		lb_fixed: bool,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let edge = &self.edges[e];
		let mut lb = self.get_cur_lower_bound(ctx, edge.from);
		let mut ub = self.get_cur_upper_bound(ctx, edge.to);
		// Only the triggering bound is needed as it stands; relaxing the other
		// to the weakest value that still falsifies gives a wider reason.
		if lb_fixed {
			ub = lb - edge.val - 1;
		} else {
			lb = ub + edge.val + 1;
		}
		let (from, to) = (
			self.int_vars[edge.from].clone(),
			self.int_vars[edge.to].clone(),
		);
		let reason = reason_ty::<E::PropagationContext<'_>, _>(move |ctx, reason| {
			let lb_lit = from.lit(ctx, IntLitMeaning::GreaterEq(lb));
			let ub_lit = to.lit(ctx, IntLitMeaning::Less(ub + 1));
			ReasonActions::push(reason, lb_lit);
			ReasonActions::push(reason, ub_lit);
		});
		if let Some(b) = bool_var {
			self.bool_vars[b].clone().fix(ctx, false, reason)
		} else {
			Err(ctx.declare_conflict(reason))
		}
	}

	/// Tighten `int_vars[n]` to at least `value`, because `int_vars[lb_var]` is
	/// at least `lb_val` and the gate holds.
	pub(super) fn set_int_lower_bound<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		n: usize,
		value: IntVal,
		bool_var: Option<usize>,
		lb_var: usize,
		lb_val: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let cause = self.int_vars[lb_var].clone();
		let gate = bool_var.map(|b| self.bool_vars[b].clone());
		self.int_vars[n].tighten_min(ctx, value, move |ctx, reason| {
			let lit = cause.lit(ctx, IntLitMeaning::GreaterEq(lb_val));
			ReasonActions::push(reason, lit);
			if let Some(gate) = gate {
				ReasonActions::push(reason, gate.into());
			}
		})
	}

	/// Tighten `int_vars[n]` to at most `value`, because `int_vars[ub_var]` is
	/// at most `ub_val` and the gate holds.
	pub(super) fn set_int_upper_bound<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		n: usize,
		value: IntVal,
		bool_var: Option<usize>,
		ub_var: usize,
		ub_val: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let cause = self.int_vars[ub_var].clone();
		let gate = bool_var.map(|b| self.bool_vars[b].clone());
		self.int_vars[n].tighten_max(ctx, value, move |ctx, reason| {
			let lit = cause.lit(ctx, IntLitMeaning::Less(ub_val + 1));
			ReasonActions::push(reason, lit);
			if let Some(gate) = gate {
				ReasonActions::push(reason, gate.into());
			}
		})
	}
}
