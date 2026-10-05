//! The difference logic component that owns the graph while the model is
//! simplified.
//!
//! Besides propagating, it runs the expensive one-off analysis — Bellman-Ford
//! for a potential function, then Johnson's algorithm for all-pairs shortest
//! paths — to prune redundant edges, unify variables a zero-length cycle forces
//! equal, falsify gates that cannot hold, and detect root-level infeasibility.
//! Whatever survives is handed to the solver.

use std::{cell::RefCell, mem, num::NonZero, ops::Not, rc::Rc};

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::{debug, trace};

use crate::{
	DeepClone, IntVal,
	actions::{
		BoolAnalyzeActions, BoolInitActions, BoolInspectionActions, BoolPropagationActions,
		InitActions, IntAnalyzeActions, IntDecisionActions, IntEvent, IntInitActions,
		IntInspectionActions, IntPropCond, IntPropagationActions, IntSimplificationActions,
		PostingActions, PropagationActions, ReasoningContext, ReasoningEngine,
		SimplificationActions, TrailingActions,
	},
	constraints::{
		Constraint, NO_REASON, Propagator, SimplificationStatus,
		difference_logic::{
			DifferenceLogicBooleans, DifferenceLogicBounds, DifferenceLogicConstraint,
			MAX_ALL_PAIRS_WORK, ModelNode,
			graph::{DiffEdge, DifferenceLogicGraph},
		},
		int_linear::{IntLinear, LinComparator, Reification},
	},
	helpers::{
		matrix::Matrix,
		overflow::{OverflowImpossible, OverflowPossible},
		trailed_open_list::TrailedOpenList,
	},
	lower::{LoweringContext, LoweringError},
	model::{
		self, Model,
		expressions::{IntLinearExp, Proposition, PropositionConstraint},
		initilization_context::ModelInitContext,
		view::integer::IntView,
	},
	solver::{self, IntLitMeaning, Polarity, queue::PriorityLevel},
	views::ScaledView,
};

/// The [`Constraint`] that owns the difference logic graph while the model is
/// being simplified.
///
/// The model creates one lazily, on first recognising a difference constraint,
/// and keeps its identifier so later ones join the same graph.
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct DifferenceLogicModel {
	/// The graph over model views.
	graph: DifferenceLogicGraph<ModelNode, model::View<bool>>,
	/// Node index of each integer view in the graph.
	int_var_index: FxHashMap<(model::Decision<IntVal>, NonZero<IntVal>), usize>,
	/// Gate index of each Boolean view in the graph.
	bool_var_index: FxHashMap<model::View<bool>, usize>,
	/// Whether the one-off initialisation has run.
	initialized: bool,
	/// How much work the all-pairs pass may cost.
	all_pairs_budget: usize,
	/// Edges added since the last simplification, which must still be
	/// propagated. Only used once [`Self::initialized`] is set; before that
	/// they are part of the initial graph.
	new_edges: Vec<usize>,
	/// All-pairs shortest path distances in the active graph, as computed by
	/// the last run of Johnson's algorithm. `IntVal::MAX` means "no path
	/// known", which is the conservative answer everywhere it is consulted.
	distances: Matrix<2, IntVal>,
	/// For each node, the nodes it already reaches by a direct edge of minimum
	/// weight, so that duplicate shortest edges can be dropped.
	direct_edge: Vec<FxHashSet<usize>>,
	/// Whether each node is still part of the graph.
	node_active: Vec<bool>,
	/// The number of nodes that have been subscribed to, so that
	/// [`Propagator::update_initialization`] only subscribes to the ones added
	/// since it last ran.
	subscribed_nodes: usize,
	/// The number of gates that have been subscribed to; see
	/// [`Self::subscribed_nodes`].
	subscribed_gates: usize,
}

impl DifferenceLogicModel {
	/// Add a difference constraint to the graph, reducing it to global and
	/// implied edges.
	pub(crate) fn add(&mut self, prb: &mut Model, constraint: DifferenceLogicConstraint) {
		use LinComparator::*;
		use Reification::*;

		let DifferenceLogicConstraint {
			x,
			y,
			d,
			comparator,
			reif,
		} = constraint;
		match (comparator, reif) {
			(LessEq, None) => self.add_edge(prb, None, x, y, d),
			(LessEq, Some(ImpliedBy(b))) => self.add_edge(prb, Some(b), x, y, d),
			// `b ↔ x - y ≤ d` is `b → x - y ≤ d` together with the negation
			// `¬b → y - x ≤ -d - 1`.
			(LessEq, Some(ReifiedBy(b))) => {
				self.add_edge(prb, Some(b), x, y, d);
				self.add_edge(prb, Some(!b), y, x, -d - 1);
			}
			// `b → x - y = d` is the conjunction of the two inequalities.
			(Equal, Some(ImpliedBy(b))) => {
				self.add_edge(prb, Some(b), x, y, d);
				self.add_edge(prb, Some(b), y, x, -d);
			}
			// `b ↔ x - y = d` is `b → x - y = d` together with
			// `¬b → x - y ≠ d`.
			(Equal, Some(ReifiedBy(b))) => {
				self.add_edge(prb, Some(b), x, y, d);
				self.add_edge(prb, Some(b), y, x, -d);
				self.add_not_equals(prb, !b, x, y, d);
			}
			// `x - y ≠ d` is `x - y < d` or `x - y > d`, decided by a fresh
			// Boolean.
			(NotEqual, None) => {
				let choice = prb.new_bool_decision();
				self.add_edge(prb, Some(choice), x, y, d - 1);
				self.add_edge(prb, Some(!choice), y, x, -d - 1);
			}
			(NotEqual, Some(ImpliedBy(b))) => self.add_not_equals(prb, b, x, y, d),
			(NotEqual, Some(ReifiedBy(_))) => {
				unreachable!(
					"`DifferenceLogicConstraint::recognise` rewrites a reified disequality"
				)
			}
			(Equal, None) => {
				unreachable!("an unreified two-term equality is not accepted at any level")
			}
		}
	}

	/// Add a single edge `x - y ≤ d`, gated by `b`, creating its nodes if
	/// needed.
	fn add_edge(
		&mut self,
		prb: &mut Model,
		b: Option<model::View<bool>>,
		x: (model::Decision<IntVal>, NonZero<IntVal>),
		y: (model::Decision<IntVal>, NonZero<IntVal>),
		d: IntVal,
	) {
		// A gate that is already decided either makes the edge global or drops
		// it entirely.
		let b = match b {
			Some(b) => match b.val(prb) {
				Some(true) => None,
				Some(false) => return,
				None => Some(self.gate_index(prb, b)),
			},
			None => None,
		};
		let from = self.node_index(prb, x);
		let to = self.node_index(prb, y);
		let index = self.graph.new_edge(prb, DiffEdge::new(from, to, d, b));
		if self.initialized {
			self.new_edges.push(index);
		}
	}

	/// Post `b → int_vars[int_var] ≥ value`, or `≤ value` when `lt`, back to
	/// the model.
	fn add_implied_bound(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
		bool_var: usize,
		int_var: usize,
		lt: bool,
		value: IntVal,
	) {
		let var = model::View::from(self.graph.int_vars[int_var]);
		let bound = if lt { var.leq(value) } else { var.geq(value) };
		ctx.post_constraint(PropositionConstraint(Proposition::Implies(
			Box::new(Proposition::Atom(self.graph.bool_vars[bool_var])),
			Box::new(Proposition::Atom(bound)),
		)));
	}

	/// Rewrite `b → x - y ≠ d` into implied edges, using two fresh Booleans for
	/// the two ways the disequality can hold.
	fn add_not_equals(
		&mut self,
		prb: &mut Model,
		b: model::View<bool>,
		x: (model::Decision<IntVal>, NonZero<IntVal>),
		y: (model::Decision<IntVal>, NonZero<IntVal>),
		d: IntVal,
	) {
		let below = prb.new_bool_decision();
		let above = prb.new_bool_decision();
		let _ = prb.post_constraint_internal(PropositionConstraint(Proposition::Or(vec![
			Proposition::Atom(!b),
			Proposition::Atom(below),
			Proposition::Atom(above),
		])));
		let _ = prb.post_constraint_internal(PropositionConstraint(Proposition::Or(vec![
			Proposition::Atom(!below),
			Proposition::Atom(!above),
		])));
		self.add_edge(prb, Some(below), x, y, d - 1);
		self.add_edge(prb, Some(above), y, x, -d - 1);
	}

	/// Compute an initial potential function with Bellman-Ford, treating every
	/// node as reachable at zero cost from an imaginary source. Fails if the
	/// graph has a cycle of negative length.
	fn bellman_ford_init_pi(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		trace!(target: "diff_logic", "calculating initial pi values");
		let mut changed = false;
		for _ in 0..self.graph.num_nodes() {
			changed = false;
			for n in 0..self.graph.num_nodes() {
				for &e in self.graph.active_out[n].iter(ctx) {
					let edge = &self.graph.edges[e];
					if self.graph.pi[edge.from] + edge.val < self.graph.pi[edge.to] {
						self.graph.pi[edge.to] = self.graph.pi[edge.from] + edge.val;
						changed = true;
					}
				}
			}
			if !changed {
				break;
			}
		}
		// A shortest path from the imaginary source settles within `|V|`
		// rounds, so a change in the last round means a negative cycle.
		if changed {
			trace!(target: "diff_logic", "found negative cycle");
			return Err(ctx.declare_conflict(NO_REASON));
		}
		Ok(())
	}

	/// Drop nodes whose value is already fixed, re-emitting the implied edges
	/// they carried as implied bounds on their neighbours.
	fn check_remove_fixed_nodes(&mut self, ctx: &mut model::SimplificationContext<'_>) {
		for n in 0..self.graph.num_nodes() {
			if !self.node_active[n] {
				continue;
			}
			let Some(val) = self.graph.int_vars[n].val(ctx) else {
				continue;
			};
			// A node with a pending bound change still has work to do.
			if self.graph.lower_bound_changes.contains(&n)
				|| self.graph.upper_bound_changes.contains(&n)
			{
				continue;
			}
			trace!(target: "diff_logic", n = ?n, "removing node with a fixed value");
			self.node_active[n] = false;
			for i in 0..self.graph.active_out[n].len(ctx) {
				let e = *self.graph.active_out[n].index(ctx, i);
				self.graph.remove_active_in(ctx, e);
			}
			for i in 0..self.graph.active_in[n].len(ctx) {
				let e = *self.graph.active_in[n].index(ctx, i);
				self.graph.remove_active_out(ctx, e);
			}
			// Cleared so that a later edge can bring the node back cleanly.
			self.graph.active_out[n].clear(ctx);
			self.graph.active_in[n].clear(ctx);
			// `x` fixed turns `b → x - y ≤ d` into the bound `b → y ≥ x - d`,
			// which the model can enforce directly.
			for i in self.graph.open_out[n].open_indices(ctx) {
				let e = *self.graph.open_out[n].index(ctx, i);
				let edge = self.graph.edges[e].clone();
				trace!(target: "diff_logic", edge = ?edge, "re-emitting implied outgoing edge as a bound");
				self.add_implied_bound(ctx, edge.gate(), edge.to, false, val - edge.val);
				self.graph.close_imp_edge(ctx, e);
			}
			for i in self.graph.open_in[n].open_indices(ctx) {
				let e = *self.graph.open_in[n].index(ctx, i);
				let edge = self.graph.edges[e].clone();
				trace!(target: "diff_logic", edge = ?edge, "re-emitting implied incoming edge as a bound");
				self.add_implied_bound(ctx, edge.gate(), edge.from, true, val + edge.val);
				self.graph.close_imp_edge(ctx, e);
			}
		}
	}

	/// Drop nodes that no longer have any edge.
	fn check_remove_isolated_nodes(&mut self, ctx: &model::SimplificationContext<'_>) {
		for n in 0..self.graph.num_nodes() {
			if self.node_active[n]
				&& self.graph.active_out[n].is_empty(ctx)
				&& self.graph.active_in[n].is_empty(ctx)
				&& self.graph.open_out[n].is_empty(ctx)
				&& self.graph.open_in[n].is_empty(ctx)
			{
				trace!(target: "diff_logic", n = ?n, "removing node with no edges");
				self.node_active[n] = false;
			}
		}
	}

	/// Dijkstra over the active graph from `source`, recording the distance to
	/// every node in row `source` of [`Self::distances`] and its predecessor in
	/// `pred`.
	fn dijkstra_from(
		&mut self,
		ctx: &model::SimplificationContext<'_>,
		source: usize,
		pred: &mut [usize],
	) {
		self.graph.reset_visit();
		self.graph.queue.clear();
		// Only a cycle found by this run may set the origin's predecessor.
		self.distances[[source, source]] = IntVal::MAX;
		self.graph.queue.push(source, 0);
		while let Some((s, dist)) = self.graph.queue.pop() {
			self.graph.visit(s);
			for &e in self.graph.active_out[s].iter(ctx) {
				let edge = &self.graph.edges[e];
				let (to, val) = (edge.to, edge.val);
				let new_dist = dist + val + self.graph.pi[s] - self.graph.pi[to];
				if !self.graph.visited[to] {
					if self.graph.queue.push_decrease(to, new_dist) {
						self.distances[[source, to]] =
							new_dist - self.graph.pi[source] + self.graph.pi[to];
						pred[to] = s;
					}
				} else if to == source && new_dist < self.distances[[source, source]] {
					// A path back to the origin closes a cycle; record it, but
					// do not settle the origin a second time.
					self.distances[[source, source]] = new_dist;
					pred[source] = s;
				}
			}
		}
	}

	/// The shortest path from `from` to `to` that the last all-pairs pass
	/// found, or `IntVal::MAX` when it has none on record.
	///
	/// The matrix only covers the nodes of the last pass, which is skipped
	/// entirely above [`MAX_ALL_PAIRS_WORK`]. "No path on record" is the
	/// conservative answer everywhere this is consulted: it keeps an edge the
	/// pass might have shown redundant.
	fn distance(&self, from: usize, to: usize) -> IntVal {
		if from < self.distances.len(0) && to < self.distances.len(1) {
			self.distances[[from, to]]
		} else {
			IntVal::MAX
		}
	}

	/// Re-emit the given edges of a node the graph cannot name, as clauses.
	///
	/// A node is a scaled decision, so one that turns out to be a literal or a
	/// constant has no node to be. It then takes at most two values, and each
	/// of its edges becomes one bound on the other endpoint per value, under
	/// the literal selecting it and the edge's own gate. `name` names a node of
	/// the model's graph, and a gate, in the context, and `post` takes a
	/// clause.
	fn encode_dissolved_node<Ctx, Node, Err>(
		&self,
		ctx: &mut Ctx,
		n: usize,
		view: &impl IntDecisionActions<Ctx>,
		edges: &[usize],
		name: impl Fn(&mut Ctx, ModelNode, Option<model::View<bool>>) -> (Node, Option<Ctx::Atom>),
		post: impl Fn(&mut Ctx, Vec<Ctx::Atom>) -> Result<(), Err>,
	) -> Result<(), Err>
	where
		Ctx: ReasoningContext + ?Sized,
		Ctx::Atom: Clone + Not<Output = Ctx::Atom>,
		Node: IntDecisionActions<Ctx>,
	{
		let (lb, ub) = view.bounds(ctx);
		let cases = if lb == ub {
			vec![(lb, None)]
		} else {
			let selects_ub = view.lit(ctx, IntLitMeaning::GreaterEq(ub));
			vec![(ub, Some(selects_ub.clone())), (lb, Some(!selects_ub))]
		};

		for &e in edges {
			let edge = self.graph.edges[e].clone();
			let far = if edge.from == n { edge.to } else { edge.from };
			let (far, gate) = name(
				ctx,
				self.graph.int_vars[far],
				edge.bool_var.map(|b| self.graph.bool_vars[b]),
			);
			for (val, selects) in &cases {
				// `x - y ≤ d` with `x` at `v` is `y ≥ v - d`; with `y` at `v`
				// it is `x ≤ v + d`.
				let bound = if edge.from == n {
					far.lit(ctx, IntLitMeaning::GreaterEq(val - edge.val))
				} else {
					far.lit(ctx, IntLitMeaning::Less(val + edge.val + 1))
				};
				let clause = gate
					.clone()
					.map(|g| !g)
					.into_iter()
					.chain(selects.clone().map(|s| !s))
					.chain([bound])
					.collect_vec();
				post(ctx, clause)?;
			}
		}
		Ok(())
	}

	/// The gate index of a Boolean view, creating it if needed.
	fn gate_index(&mut self, prb: &mut Model, b: model::View<bool>) -> usize {
		if let Some(&index) = self.bool_var_index.get(&b) {
			return index;
		}
		let index = self.graph.bool_vars.len();
		let _ = self.bool_var_index.insert(b, index);
		self.graph.bool_vars.push(b);
		self.graph.bool_implications.push(TrailedOpenList::new(prb));
		index
	}

	/// Run the one-off initialisation: a potential function, a first round of
	/// propagation, and Johnson's algorithm to prune the graph.
	fn initialize(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		let (nodes, gates, active, implied) = self.size(ctx);
		debug!(
			target: "diff_logic",
			nodes, gates, active_edges = active, implied_edges = implied,
			"initialising the difference logic graph"
		);
		self.bellman_ford_init_pi(ctx)?;
		<Self as Propagator<Model>>::propagate(self, ctx)?;
		// Removing nodes first keeps the all-pairs computation smaller.
		self.reduce(ctx);
		self.johnson_full(ctx)?;
		self.initialized = true;
		let (nodes, gates, active, implied) = self.size(ctx);
		debug!(
			target: "diff_logic",
			nodes, gates, active_edges = active, implied_edges = implied,
			"difference logic graph simplified"
		);
		Ok(())
	}

	/// Compute all-pairs shortest paths with Johnson's algorithm, then use them
	/// to drop redundant edges, close or falsify implied edges, and unify the
	/// nodes of any zero-length cycle.
	fn johnson_full(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		let num_nodes = self.graph.num_nodes();
		let num_edges = self.graph.edges.len();
		let work = num_nodes.saturating_mul(num_nodes.saturating_add(num_edges));
		if work > self.all_pairs_budget {
			debug!(
				target: "diff_logic",
				nodes = num_nodes, edges = num_edges, work, budget = self.all_pairs_budget,
				"skipping the all-pairs pass: the graph is too large to reduce"
			);
			return Ok(());
		}
		trace!(target: "diff_logic", "starting Johnson's");
		self.distances = Matrix::with_dimensions_and_value([num_nodes, num_nodes], IntVal::MAX);
		// Per-pass state: a stale entry would read as evidence against the very
		// edge this pass means to keep.
		for kept in &mut self.direct_edge {
			kept.clear();
		}
		// Only zero-cycle sources need predecessors, and those are rare, so one
		// reusable row beats a second `num_nodes²` matrix.
		let mut pred = vec![usize::MAX; num_nodes];
		let mut zero_cycles = Vec::new();

		for n in 0..num_nodes {
			if !self.node_active[n] {
				continue;
			}
			self.dijkstra_from(ctx, n, &mut pred);
			if self.distances[[n, n]] == 0 {
				zero_cycles.push(n);
			}
		}

		trace!(target: "diff_logic", "checking the impact on edges");
		for n in 0..num_nodes {
			if !self.node_active[n] {
				continue;
			}
			let mut i = 0;
			while i < self.graph.active_out[n].len(ctx) {
				let e = *self.graph.active_out[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				let (to, val) = (edge.to, edge.val);
				// A shorter path already implies this edge, as does an equal
				// one when a direct edge of that weight has been kept already.
				if self.distances[[n, to]] < val
					|| (self.distances[[n, to]] == val && self.direct_edge[n].contains(&to))
				{
					trace!(target: "diff_logic", e = ?e, distance = self.distances[[n, to]], "global edge is redundant");
					self.graph.remove_active_edge(ctx, e);
				} else {
					let _ = self.direct_edge[n].insert(to);
					i += 1;
				}
			}

			// Each open edge is in exactly one outgoing list, so this sees each
			// once.
			for i in self.graph.open_out[n].open_indices(ctx) {
				let e = *self.graph.open_out[n].index(ctx, i);
				self.resolve_implied_edge(ctx, e)?;
			}
		}

		// The pass above kept predecessors only for its last source, so the few
		// zero-cycle sources that need them are recomputed here.
		for n in zero_cycles {
			if self.distances[[n, n]] != 0 {
				// An earlier cycle already absorbed this node.
				continue;
			}
			trace!(target: "diff_logic", n = ?n, "cycle of length zero");
			self.dijkstra_from(ctx, n, &mut pred);
			let mut offset = 0;
			let mut cur = n;
			loop {
				let prev = pred[cur];
				if prev == n {
					break;
				}
				offset += self.distances[[prev, cur]];
				trace!(target: "diff_logic", prev = ?prev, origin = ?n, offset = ?offset, "unifying nodes");
				let target = model::View::from(self.graph.int_vars[n]) + offset;
				model::View::from(self.graph.int_vars[prev]).unify(ctx, target)?;
				cur = prev;
				self.distances[[cur, cur]] = IntVal::MAX;
			}
		}

		Ok(())
	}

	/// Create an empty component.
	pub(crate) fn new(prb: &mut Model) -> Self {
		let all_pairs_budget = prb
			.diff_logic_all_pairs_budget
			.unwrap_or(MAX_ALL_PAIRS_WORK);
		Self {
			graph: DifferenceLogicGraph::new(prb, Vec::new(), Vec::new()),
			all_pairs_budget,
			int_var_index: FxHashMap::default(),
			bool_var_index: FxHashMap::default(),
			initialized: false,
			new_edges: Vec::new(),
			distances: Matrix::with_dimensions_and_value([0, 0], IntVal::MAX),
			direct_edge: Vec::new(),
			node_active: Vec::new(),
			subscribed_nodes: 0,
			subscribed_gates: 0,
		}
	}

	/// The node index of a decision and the scale applied to it, creating the
	/// node if needed.
	///
	/// `x` is taken as given rather than resolved; [`Self::resolve_aliases`]
	/// corrects a decision that has since become an alias.
	fn node_index(
		&mut self,
		prb: &mut Model,
		x: (model::Decision<IntVal>, NonZero<IntVal>),
	) -> usize {
		if let Some(&index) = self.int_var_index.get(&x) {
			// A node removed as fixed or isolated comes back with the new edge.
			// An aliased or dissolved node is never looked up here, since the
			// constraint was recognised on resolved decisions.
			self.node_active[index] = true;
			return index;
		}
		let index = self.graph.int_vars.len();
		let _ = self.int_var_index.insert(x, index);
		self.graph.int_vars.push(ScaledView::new(x.1, x.0));
		self.graph.add_node(prb);
		self.direct_edge.push(FxHashSet::default());
		self.node_active.push(true);
		index
	}

	/// Remove the nodes that no longer carry information.
	fn reduce(&mut self, ctx: &mut model::SimplificationContext<'_>) {
		self.check_remove_fixed_nodes(ctx);
		self.check_remove_isolated_nodes(ctx);
	}

	/// Follow the aliases the rest of the model has introduced, merging nodes
	/// that have become views of one another.
	///
	/// [`Self::int_var_index`] only keys integer decisions, so a node aliased
	/// onto a Boolean-backed view is updated but not re-interned: two such
	/// nodes are not recognised as one.
	fn resolve_aliases(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		for n in 0..self.graph.num_nodes() {
			if !self.node_active[n] {
				continue;
			}
			let node: model::View<IntVal> = self.graph.int_vars[n].into();
			let alias = node.resolve_alias(ctx.0);
			if node == alias.0 {
				continue;
			}
			trace!(target: "diff_logic", n = ?n, alias = ?alias.0, "node has been aliased");
			let (stripped, offset) = alias.strip_offset();
			let key = stripped
				.integer_decision()
				.map(|d| (d.into_inner(), stripped.scale()));
			if let Some(new) = key.and_then(|k| self.int_var_index.get(&k).copied()) {
				self.unify_nodes(ctx, n, new, offset)?;
				let _ = self.graph.lower_bound_changes.insert(new);
				let _ = self.graph.upper_bound_changes.insert(new);
			} else if let Some((decision, scale)) = key {
				self.update_node_offset(ctx, n, offset)?;
				self.graph.int_vars[n] = ScaledView::new(scale, decision);
				let _ = self.int_var_index.insert((decision, scale), n);
			} else if !matches!(stripped.0.0, IntView::Const(_)) {
				// No longer a decision, so it has no node; its edges become
				// clauses instead.
				trace!(target: "diff_logic", n = ?n, "dissolving a node that is no longer a decision");
				// Every edge is taken, since each is removed right after.
				let edges = self.graph.edges_at(n, |slot| ctx.trailed(slot));
				self.encode_dissolved_node(
					ctx,
					n,
					&stripped.0,
					&edges,
					|_, node, gate| -> (model::View<IntVal>, _) { (node.into(), gate) },
					|ctx, clause| {
						let _ = ctx.post_constraint(PropositionConstraint(Proposition::Or(
							clause.into_iter().map(Proposition::Atom).collect_vec(),
						)));
						Ok::<(), <Model as ReasoningEngine>::Conflict>(())
					},
				)?;
				for e in edges {
					if self.graph.edges[e].bool_var.is_some() {
						self.graph.close_imp_edge(ctx, e);
					} else if self.graph.edges[e].from == n {
						self.graph.remove_active_in(ctx, e);
					} else {
						self.graph.remove_active_out(ctx, e);
					}
				}
				self.graph.active_out[n].clear(ctx);
				self.graph.active_in[n].clear(ctx);
				self.node_active[n] = false;
			}
			// A node that aliased onto a constant is left for
			// `check_remove_fixed_nodes`, which re-emits its edges as bounds.
		}
		Ok(())
	}

	/// Close an implied edge that the last all-pairs pass shows is entailed, or
	/// falsify its gate when the pass shows the edge would close a negative
	/// cycle.
	fn resolve_implied_edge(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
		e: usize,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		let (from, to, val) = {
			let edge = &self.graph.edges[e];
			(edge.from, edge.to, edge.val)
		};
		if self.distance(from, to) <= val {
			trace!(target: "diff_logic", e = ?e, "implied edge is already entailed");
			self.graph.close_imp_edge(ctx, e);
		} else if self.distance(to, from) < -val {
			trace!(target: "diff_logic", e = ?e, "implied edge is falsified");
			let gate = self.graph.edges[e].gate();
			self.graph.bool_vars[gate].fix(ctx, false, NO_REASON)?;
			self.graph.close_imp_edge(ctx, e);
		}
		Ok(())
	}

	/// Keep an edge only while its endpoints are still distinct decisions,
	/// otherwise fold it back into the model and report that it was dropped.
	///
	/// Unification, or an alias resolving onto another node, can collapse the
	/// endpoints long after the edge was made. Rebuilding through the model's
	/// linear arithmetic reduces it to whatever it has become, usually a domain
	/// restriction rather than a transient [`IntLinear`]. It cannot bounce
	/// back: [`DifferenceLogicConstraint::recognise`] only takes *distinct*
	/// decisions.
	fn retain_edge(
		ctx: &mut model::SimplificationContext<'_>,
		x: ModelNode,
		y: ModelNode,
		d: IntVal,
		b: Option<model::View<bool>>,
	) -> Result<bool, <Model as ReasoningEngine>::Conflict> {
		if x == y && d >= 0 {
			trace!(target: "diff_logic", b = ?b, x = ?x, y = ?y, d = ?d, "dropping redundant edge");
			return Ok(false);
		}
		// A node is decision-backed, but its decision may since have become an
		// alias, which is what this is called to discover.
		let (x, y) = (model::View::from(x), model::View::from(y));
		let x_var = x.resolve_alias(ctx.0).integer_decision().map(|d| d.idx());
		let y_var = y.resolve_alias(ctx.0).integer_decision().map(|d| d.idx());
		if x_var != y_var && x_var.is_some() && y_var.is_some() {
			return Ok(true);
		}
		trace!(target: "diff_logic", b = ?b, x = ?x, y = ?y, d = ?d, "re-emitting edge over a single decision or a constant");

		let mut expr: IntLinearExp = x - y;
		expr -= d;
		let rhs = -expr.offset;
		let entries = expr.terms.iter().map(|(&v, &k)| (v, k)).collect_vec();
		match entries[..] {
			// No decision left: `x - y ≤ d` has become a fixed fact.
			[] => match b {
				None => (rhs >= 0).require(ctx, NO_REASON)?,
				Some(_) if rhs >= 0 => {}
				Some(b) => b.fix(ctx, false, NO_REASON)?,
			},
			// One decision left: a direct bound, conditional on `b` if given.
			[(v, k)] => {
				let term = v.bounding_mul(ctx, k)?;
				match b {
					None => term.tighten_max(ctx, rhs, NO_REASON)?,
					Some(b) => {
						let _ = ctx.post_constraint(PropositionConstraint(Proposition::Implies(
							Box::new(Proposition::Atom(b)),
							Box::new(Proposition::Atom(term.leq(rhs))),
						)));
					}
				}
			}
			// Still two distinct decisions — e.g. both Boolean-backed — just
			// not a shape the graph can take as an edge.
			_ => {
				let terms = entries
					.iter()
					.map(|&(v, k)| v.bounding_mul(ctx, k))
					.collect::<Result<Vec<_>, _>>()?;
				let reif = b.map(Reification::ImpliedBy);
				if IntLinear::can_overflow(ctx, &terms) {
					ctx.post_constraint(IntLinear::<OverflowPossible> {
						terms,
						rhs: rhs.into(),
						reif,
						comparator: LinComparator::LessEq,
					});
				} else {
					ctx.post_constraint(IntLinear::<OverflowImpossible> {
						terms,
						rhs,
						reif,
						comparator: LinComparator::LessEq,
					});
				}
			}
		}
		Ok(false)
	}

	/// The size of the graph as `(nodes, gates, active edges, implied edges)`.
	fn size(&self, ctx: &(impl TrailingActions + ?Sized)) -> (usize, usize, usize, usize) {
		(
			self.node_active.iter().filter(|&&active| active).count(),
			(0..self.graph.bool_vars.len())
				.filter(|&b| !self.graph.bool_implications[b].is_empty(ctx))
				.count(),
			(0..self.graph.num_nodes())
				.map(|n| self.graph.active_out[n].len(ctx))
				.sum(),
			(0..self.graph.num_nodes())
				.map(|n| self.graph.open_out[n].num_open(ctx))
				.sum(),
		)
	}

	/// Move every edge of `old` onto `new`, shifted by `offset`, after the two
	/// nodes turned out to denote the same decision.
	fn unify_nodes(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
		old: usize,
		new: usize,
		offset: IntVal,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		trace!(target: "diff_logic", old = ?old, new = ?new, offset = ?offset, "moving all edges");
		let mut moved = Vec::new();
		for i in 0..self.graph.active_out[old].len(ctx) {
			let e = *self.graph.active_out[old].index(ctx, i);
			let (to, val) = (self.graph.edges[e].to, self.graph.edges[e].val);
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[new],
				self.graph.int_vars[to],
				val - offset,
				None,
			)? && (self.distance(new, to) > val - offset
				|| (self.distance(new, to) == val - offset && !self.direct_edge[new].contains(&to)))
			{
				let edge = &mut self.graph.edges[e];
				edge.from = new;
				edge.val -= offset;
				self.graph.push_active_out(ctx, e);
				let _ = self.direct_edge[new].insert(to);
				moved.push(e);
			} else {
				self.graph.remove_active_in(ctx, e);
			}
		}
		self.graph.active_out[old].clear(ctx);
		for i in 0..self.graph.active_in[old].len(ctx) {
			let e = *self.graph.active_in[old].index(ctx, i);
			let (from, val) = (self.graph.edges[e].from, self.graph.edges[e].val);
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[from],
				self.graph.int_vars[new],
				val + offset,
				None,
			)? && (self.distance(from, new) > val + offset
				|| (self.distance(from, new) == val + offset
					&& !self.direct_edge[from].contains(&new)))
			{
				let edge = &mut self.graph.edges[e];
				edge.to = new;
				edge.val += offset;
				self.graph.push_active_in(ctx, e);
				let _ = self.direct_edge[from].insert(new);
				moved.push(e);
			} else {
				self.graph.remove_active_out(ctx, e);
			}
		}
		self.graph.active_in[old].clear(ctx);

		// Implied edges: close the ones that have become degenerate first, then
		// move whatever is left.
		for i in self.graph.open_out[old].open_indices(ctx) {
			let e = *self.graph.open_out[old].index(ctx, i);
			let edge = self.graph.edges[e].clone();
			if !Self::retain_edge(
				ctx,
				self.graph.int_vars[new],
				self.graph.int_vars[edge.to],
				edge.val - offset,
				edge.bool_var.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_out[old].open_indices(ctx) {
			let e = *self.graph.open_out[old].index(ctx, i);
			let out_index = self.graph.open_out[new].total_len();
			let edge = &mut self.graph.edges[e];
			edge.from = new;
			edge.val -= offset;
			edge.out_index = out_index;
			self.graph.open_out[new].push(e);
		}
		self.graph.open_out[old].clear(ctx);
		for i in self.graph.open_in[old].open_indices(ctx) {
			let e = *self.graph.open_in[old].index(ctx, i);
			let edge = self.graph.edges[e].clone();
			if !Self::retain_edge(
				ctx,
				self.graph.int_vars[edge.from],
				self.graph.int_vars[new],
				edge.val + offset,
				edge.bool_var.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_in[old].open_indices(ctx) {
			let e = *self.graph.open_in[old].index(ctx, i);
			let in_index = self.graph.open_in[new].total_len();
			let edge = &mut self.graph.edges[e];
			edge.to = new;
			edge.val += offset;
			edge.in_index = in_index;
			self.graph.open_in[new].push(e);
		}
		self.graph.open_in[old].clear(ctx);

		for e in moved {
			self.graph.propagate_edge_addition::<Model, true>(ctx, e)?;
		}
		self.node_active[old] = false;
		Ok(())
	}

	/// Shift a node by `offset`, adjusting its potential, derived bounds, and
	/// distances, and the weight of every edge that touches it, and dropping
	/// the edges that become degenerate.
	fn update_node_offset(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
		n: usize,
		offset: IntVal,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		trace!(target: "diff_logic", n = ?n, offset = ?offset, "updating node offset");
		self.graph.pi[n] += offset;
		if let Some(lb) = self.graph.lower_bound[n].as_mut() {
			*lb -= offset;
		}
		if let Some(ub) = self.graph.upper_bound[n].as_mut() {
			*ub -= offset;
		}
		// Shift the node's distances as its edges are shifted below, so that
		// the matrix keeps describing the graph for later unifications.
		if n < self.distances.len(0) {
			for m in 0..self.distances.len(0) {
				if m == n {
					continue;
				}
				if self.distances[[n, m]] != IntVal::MAX {
					self.distances[[n, m]] -= offset;
				}
				if self.distances[[m, n]] != IntVal::MAX {
					self.distances[[m, n]] += offset;
				}
			}
		}
		let mut i = 0;
		while i < self.graph.active_out[n].len(ctx) {
			let e = *self.graph.active_out[n].index(ctx, i);
			let to = self.graph.edges[e].to;
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[n],
				self.graph.int_vars[to],
				self.graph.edges[e].val,
				None,
			)? {
				self.graph.edges[e].val -= offset;
				i += 1;
			} else {
				self.graph.remove_active_edge(ctx, e);
			}
		}
		i = 0;
		while i < self.graph.active_in[n].len(ctx) {
			let e = *self.graph.active_in[n].index(ctx, i);
			let from = self.graph.edges[e].from;
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[from],
				self.graph.int_vars[n],
				self.graph.edges[e].val,
				None,
			)? {
				self.graph.edges[e].val += offset;
				i += 1;
			} else {
				self.graph.remove_active_edge(ctx, e);
			}
		}
		for i in self.graph.open_out[n].open_indices(ctx) {
			let e = *self.graph.open_out[n].index(ctx, i);
			let edge = self.graph.edges[e].clone();
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[n],
				self.graph.int_vars[edge.to],
				edge.val,
				edge.bool_var.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.edges[e].val -= offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_in[n].open_indices(ctx) {
			let e = *self.graph.open_in[n].index(ctx, i);
			let edge = self.graph.edges[e].clone();
			if Self::retain_edge(
				ctx,
				self.graph.int_vars[edge.from],
				self.graph.int_vars[n],
				edge.val,
				edge.bool_var.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.edges[e].val += offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		Ok(())
	}
}

impl Constraint<Model> for DifferenceLogicModel {
	fn analyze(&self, ctx: &mut ModelInitContext<'_>) {
		// Dropped edges are analysed too: polarity is only a hint, and one from
		// a redundant constraint is still valid.
		for edge in &self.graph.edges {
			match edge.bool_var {
				// A gate that is false satisfies its edge vacuously.
				Some(b) => self.graph.bool_vars[b].polarity(ctx, Polarity::Negative),
				// `x - y ≤ d` is easier to satisfy the smaller `x` and the
				// larger `y` are.
				None => {
					self.graph.int_vars[edge.from].polarity(ctx, Polarity::Negative);
					self.graph.int_vars[edge.to].polarity(ctx, Polarity::Positive);
				}
			}
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<SimplificationStatus, <Model as ReasoningEngine>::Conflict> {
		// Edges added since the last analysis, so that a repeated
		// [`Model::propagate`] over an unchanged graph does not pay for
		// [`Self::johnson_full`] again.
		let new_edges = mem::take(&mut self.new_edges);
		if !self.initialized {
			self.initialize(ctx)?;
		} else {
			for &e in &new_edges {
				if self.graph.edges[e].bool_var.is_none() {
					self.graph.propagate_edge_addition::<Model, true>(ctx, e)?;
				}
			}
		}

		self.resolve_aliases(ctx)?;
		<Self as Propagator<Model>>::propagate(self, ctx)?;

		// At the lowest priority the cheaper constraints have settled, so every
		// edge they fold into is here; what this changes wakes them again.
		let new_active = new_edges
			.iter()
			.any(|&e| self.graph.edges[e].bool_var.is_none());
		if new_active {
			// Removing nodes first keeps the all-pairs computation smaller, as
			// in [`Self::initialize`].
			self.reduce(ctx);
			self.johnson_full(ctx)?;
		} else if self.initialized {
			// Implied edges leave the active graph, and so the distances,
			// unchanged, so the last pass still answers for them.
			for e in new_edges {
				if self.graph.is_open(ctx, e) {
					self.resolve_implied_edge(ctx, e)?;
				}
			}
		}

		self.reduce(ctx);
		// Every derived bound is now on the decisions themselves, and the model
		// never backtracks to reset them, so a kept one would only go stale.
		self.graph.forget_derived_bounds();
		debug_assert!(
			self.graph.potential_is_feasible(
				(0..self.graph.num_nodes())
					.flat_map(|n| self.graph.active_out[n].iter(ctx).copied())
			),
			"simplifying left an active edge with a negative reduced cost"
		);
		// Never subsumed, even when no node is left: the model keeps adding
		// later difference constraints to this component.
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, ctx: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		// A decision of two values lowers to a literal, which the graph cannot
		// name, so its edges are encoded instead.
		let mut keep = vec![false; self.graph.num_nodes()];
		// What lowering added to each node, moved into the weights of its edges
		// so that a node stays a bare scaled decision.
		let mut offsets = vec![0; self.graph.num_nodes()];
		let mut int_vars = Vec::new();
		let mut dissolved = Vec::new();
		for (n, &active) in self.node_active.iter().enumerate() {
			if !active {
				continue;
			}
			let view = ctx.solver_view(model::View::from(self.graph.int_vars[n]));
			match view.0 {
				solver::IntView::Linear(lin) => {
					keep[n] = true;
					offsets[n] = lin.offset;
					int_vars.push(ScaledView::new(lin.scale, lin.var));
				}
				solver::IntView::Bool(_) | solver::IntView::Const(_) => dissolved.push((n, view)),
			}
		}
		for (n, view) in dissolved {
			// Nothing is removed here, so an edge between two dissolved nodes
			// is left to the later of the two, to encode each edge
			// once.
			let edges = self
				.graph
				.edges_at(n, |slot| ctx.model_trailed(slot))
				.into_iter()
				.filter(|&e| {
					let edge = &self.graph.edges[e];
					let far = if edge.from == n { edge.to } else { edge.from };
					keep[far] || far >= n
				})
				.collect_vec();
			self.encode_dissolved_node(
				ctx,
				n,
				&view,
				&edges,
				|ctx: &mut LoweringContext<'_>, node: ModelNode, gate| {
					(
						ctx.solver_view(node.into()),
						gate.map(|g| ctx.solver_view(g)),
					)
				},
				|ctx, clause| ctx.add_clause(clause),
			)?;
		}
		// A gate is still needed while it guards an open edge.
		let gate_active = self
			.graph
			.bool_implications
			.iter()
			.map(|list| {
				!list
					.open_indices_from(ctx.model_trailed(list.closed_slot()))
					.is_empty()
			})
			.collect_vec();
		// `add_edge` drops or globalises the edges of a decided gate, so one
		// still active is unfixed.
		let bool_vars = self
			.graph
			.bool_vars
			.iter()
			.zip(&gate_active)
			.filter(|&(_, &active)| active)
			.map(|(&v, _)| match ctx.solver_view(v).0 {
				solver::view::boolean::BoolView::Lit(lit) => lit,
				solver::view::boolean::BoolView::Const(_) => {
					unreachable!("an active gate is not fixed")
				}
			})
			.collect_vec();
		trace!(
			target: "diff_logic",
			nodes = int_vars.len(),
			gates = bool_vars.len(),
			"lowering difference logic to the solver"
		);
		// Renumber the positions that `keep` marks, so that position `i` maps
		// to its index among the kept positions, or `None` if it is dropped.
		let remap_vec = |keep: &[bool]| -> Vec<Option<usize>> {
			keep.iter()
				.scan(0_usize, |count, &keep| {
					Some(keep.then(|| {
						*count += 1;
						*count - 1
					}))
				})
				.collect_vec()
		};

		let graph = Rc::new(RefCell::new(DifferenceLogicGraph::from_model(
			&self.graph,
			ctx,
			int_vars,
			bool_vars,
			&remap_vec(&keep),
			&remap_vec(&gate_active),
			&offsets,
		)));
		// The two propagators hold the graph jointly, so both are given the
		// same reference; deep cloning the solver keeps them sharing one copy.
		// The lowerer records the two propagators posted here, in this order,
		// as the solver's reference to the component, so they are posted even
		// when the graph is empty.
		let _ = ctx.add_propagator(Box::new(DifferenceLogicBounds {
			graph: Rc::clone(&graph),
		}));
		let _ = ctx.add_propagator(Box::new(DifferenceLogicBooleans { graph }));
		Ok(())
	}
}

impl Propagator<Model> for DifferenceLogicModel {
	fn advise_of_bool_change(&mut self, _: &mut Model, data: u64) -> bool {
		self.graph.fixed_bools.insert(data as usize)
	}

	fn advise_of_int_change(&mut self, ctx: &mut Model, data: u64, event: IntEvent) -> bool {
		self.graph.notify_int_change(ctx, data as usize, event)
	}

	fn initialize(&mut self, ctx: &mut ModelInitContext<'_>) {
		// The most expensive step, so it waits for the cheaper constraints.
		ctx.set_priority(PriorityLevel::Lowest);
		// Created before its first edge, so there is nothing to subscribe to
		// yet; `Model::post_difference` asks again once there is.
		self.update_initialization(ctx);
		ctx.enqueue_now(true);
	}

	fn propagate(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		self.graph.propagate_bounds::<Model>(ctx)?;
		self.graph.propagate_booleans::<Model, true>(ctx)
	}

	fn update_initialization(&mut self, ctx: &mut ModelInitContext<'_>) {
		// Nodes and gates are only appended, so a watermark suffices; a second
		// subscription would advise the component twice.
		for (i, &n) in self
			.graph
			.int_vars
			.iter()
			.enumerate()
			.skip(self.subscribed_nodes)
		{
			n.advise_when(ctx, IntPropCond::Bounds, i as u64);
		}
		self.subscribed_nodes = self.graph.int_vars.len();
		for (i, &b) in self
			.graph
			.bool_vars
			.iter()
			.enumerate()
			.skip(self.subscribed_gates)
		{
			b.advise_when_fixed(ctx, i as u64);
		}
		self.subscribed_gates = self.graph.bool_vars.len();
	}
}
