//! The difference logic component that owns the graph while the model is
//! simplified.
//!
//! Besides propagating, it computes a potential function with Bellman-Ford
//! once, and runs Johnson's all-pairs shortest paths whenever active edges were
//! added, to prune redundant edges, unify decisions that a zero-length cycle
//! forces equal, falsify gates that cannot hold, and detect root-level
//! infeasibility. Whatever survives is handed to the solver.

use std::{cell::RefCell, mem, ops::Not, rc::Rc};

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
	int_dcn_index: FxHashMap<ModelNode, usize>,
	/// Gate index of each Boolean view in the graph.
	bool_dcn_index: FxHashMap<model::View<bool>, usize>,
	/// Whether the one-off initialisation has run.
	initialized: bool,
	/// How much work a repeated all-pairs pass may cost; see
	/// [`MAX_ALL_PAIRS_WORK`].
	all_pairs_budget: usize,
	/// The number of active edges the graph had when the all-pairs pass last
	/// started; see [`Self::johnson_full`].
	analysed_edges: usize,
	/// Edges added since the last simplification, which must still be
	/// propagated. Only used once [`Self::initialized`] is set; before that
	/// they are part of the initial graph.
	new_edges: Vec<usize>,
	/// All-pairs shortest path distances in the active graph from the last run
	/// of Johnson's algorithm, read through [`Self::distance`].
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
		x: ModelNode,
		y: ModelNode,
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

	/// Post `b → int_dcns[int_dcn] ≥ value`, or `≤ value` when `lt`, back to
	/// the model.
	fn add_implied_bound(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
		bool_dcn: usize,
		int_dcn: usize,
		lt: bool,
		value: IntVal,
	) {
		let view = model::View::from(self.graph.int_dcns[int_dcn]);
		let bound = if lt { view.leq(value) } else { view.geq(value) };
		ctx.post_constraint(PropositionConstraint(Proposition::Implies(
			Box::new(Proposition::Atom(self.graph.bool_dcns[bool_dcn])),
			Box::new(Proposition::Atom(bound)),
		)));
	}

	/// Rewrite `b → x - y ≠ d` into implied edges, using two fresh Booleans for
	/// the two ways the disequality can hold.
	fn add_not_equals(
		&mut self,
		prb: &mut Model,
		b: model::View<bool>,
		x: ModelNode,
		y: ModelNode,
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

	/// Drop nodes whose value is already fixed, re-emitting the edges they
	/// carried as bounds on their neighbours: direct bounds for the active
	/// edges, and implied bounds for the implied ones.
	///
	/// The bounds use the fixed value itself, which a hole in the domain can
	/// put beyond the bound that the graph derived.
	fn check_remove_fixed_nodes(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		for n in 0..self.graph.num_nodes() {
			if !self.node_active[n] {
				continue;
			}
			let Some(val) = self.graph.int_dcns[n].val(ctx) else {
				continue;
			};
			trace!(target: "diff_logic", n = ?n, "removing node with a fixed value");
			self.node_active[n] = false;
			// `x` fixed turns `x - y ≤ d` into the bound `y ≥ x - d`.
			for i in 0..self.graph.active_out[n].len(ctx) {
				let e = *self.graph.active_out[n].index(ctx, i);
				let (to, weight) = (self.graph.edges[e].to, self.graph.edges[e].val);
				self.graph.int_dcns[to].tighten_min(ctx, val - weight, NO_REASON)?;
				self.graph.remove_active_in(ctx, e);
			}
			// `y` fixed turns `x - y ≤ d` into the bound `x ≤ y + d`.
			for i in 0..self.graph.active_in[n].len(ctx) {
				let e = *self.graph.active_in[n].index(ctx, i);
				let (from, weight) = (self.graph.edges[e].from, self.graph.edges[e].val);
				self.graph.int_dcns[from].tighten_max(ctx, val + weight, NO_REASON)?;
				self.graph.remove_active_out(ctx, e);
			}
			// Cleared so that a later edge can bring the node back cleanly.
			self.graph.active_out[n].clear(ctx);
			self.graph.active_in[n].clear(ctx);
			// The same for the implied edges, under their gates, which the
			// model can enforce directly.
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
		Ok(())
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
		// Reset, so that the cycle branch below records only a cycle found by
		// this run, and its predecessor.
		self.distances[[source, source]] = IntVal::MAX;
		self.graph.queue.push(source, 0);
		while let Some((s, dist)) = self.graph.queue.pop() {
			self.graph.visit(s);
			// The origin's own entry is the length of its shortest cycle,
			// which the branch below records.
			if s != source {
				self.distances[[source, s]] = dist - self.graph.pi[source] + self.graph.pi[s];
			}
			for &e in self.graph.active_out[s].iter(ctx) {
				let edge = &self.graph.edges[e];
				let (to, val) = (edge.to, edge.val);
				let new_dist = dist + val + self.graph.pi[s] - self.graph.pi[to];
				if !self.graph.visited[to] {
					if self.graph.queue.push_decrease(to, new_dist) {
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
	/// The matrix only covers the nodes of the last pass, and a later pass can
	/// be skipped above [`MAX_ALL_PAIRS_WORK`]. "No path on record" is always
	/// the conservative answer: it keeps an edge that the pass might have shown
	/// redundant.
	fn distance(&self, from: usize, to: usize) -> IntVal {
		if from < self.distances.len(0) && to < self.distances.len(1) {
			self.distances[[from, to]]
		} else {
			IntVal::MAX
		}
	}

	/// Re-emit the given edges of a node the graph cannot name, as clauses.
	///
	/// A node is a scaled decision, so a view that is a literal or a constant
	/// cannot be one. Such a view takes at most two values, and each edge
	/// becomes one bound on its other endpoint per value, under the literal
	/// selecting the value and the edge's gate. `name` translates a node and a
	/// gate into the context, and `post` posts a clause.
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
				self.graph.int_dcns[far],
				edge.bool_dcn.map(|b| self.graph.bool_dcns[b]),
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
		if let Some(&index) = self.bool_dcn_index.get(&b) {
			return index;
		}
		let index = self.graph.bool_dcns.len();
		let _ = self.bool_dcn_index.insert(b, index);
		self.graph.bool_dcns.push(b);
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
		self.reduce(ctx)?;
		let _ = self.johnson_full(ctx)?;
		self.initialized = true;
		let (nodes, gates, active, implied) = self.size(ctx);
		debug!(
			target: "diff_logic",
			nodes, gates, active_edges = active, implied_edges = implied,
			"difference logic graph simplified"
		);
		Ok(())
	}

	/// Whether the distances on record already imply an edge `from - to ≤
	/// val`: by a shorter path, or by an equal one when a direct edge of that
	/// weight has been kept already.
	fn is_redundant(&self, from: usize, to: usize, val: IntVal) -> bool {
		let distance = self.distance(from, to);
		distance < val || (distance == val && self.direct_edge[from].contains(&to))
	}

	/// Compute all-pairs shortest paths with Johnson's algorithm, then use them
	/// to drop redundant edges, close or falsify implied edges, and unify the
	/// nodes of any zero-length cycle. Returns whether the pass ran, rather
	/// than being skipped as too costly.
	fn johnson_full(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<bool, <Model as ReasoningEngine>::Conflict> {
		let num_nodes = self.graph.num_nodes();
		let num_edges = self.graph.edges.len();
		let work = num_nodes.saturating_mul(num_nodes.saturating_add(num_edges));
		// The budget only guards against repeating the pass for small
		// additions: a graph whose active edges have at least doubled is
		// analysed regardless, which costs about as much in total as the last
		// such pass. The comparison is against the edges that the last pass
		// started with, so that redundant edges, which a pass removes, cannot
		// trigger one each time they arrive.
		let active_edges = self.num_active_edges(ctx);
		let doubled = active_edges >= 2 * self.analysed_edges;
		if !doubled && work > self.all_pairs_budget {
			debug!(
				target: "diff_logic",
				nodes = num_nodes, edges = num_edges, work, budget = self.all_pairs_budget,
				active_edges, analysed_edges = self.analysed_edges,
				"skipping the all-pairs pass: too costly for the edges added since the last one"
			);
			return Ok(false);
		}
		self.analysed_edges = active_edges;
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
			// Dropping a redundant edge changes no distance, so it is done
			// right away, to spare the later sources from relaxing it.
			let mut i = 0;
			while i < self.graph.active_out[n].len(ctx) {
				let e = *self.graph.active_out[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				let (to, val) = (edge.to, edge.val);
				if self.is_redundant(n, to, val) {
					trace!(target: "diff_logic", e = ?e, distance = self.distances[[n, to]], "global edge is redundant");
					self.graph.remove_active_edge(ctx, e);
				} else {
					let _ = self.direct_edge[n].insert(to);
					i += 1;
				}
			}
		}

		trace!(target: "diff_logic", "checking the impact on implied edges");
		for n in 0..num_nodes {
			if !self.node_active[n] {
				continue;
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
				let target = model::View::from(self.graph.int_dcns[n]) + offset;
				model::View::from(self.graph.int_dcns[prev]).unify(ctx, target)?;
				cur = prev;
				self.distances[[cur, cur]] = IntVal::MAX;
			}
		}

		Ok(true)
	}

	/// Create an empty component.
	pub(crate) fn new(prb: &mut Model) -> Self {
		let all_pairs_budget = prb
			.diff_logic_all_pairs_budget
			.unwrap_or(MAX_ALL_PAIRS_WORK);
		Self {
			graph: DifferenceLogicGraph::default(),
			all_pairs_budget,
			analysed_edges: 0,
			int_dcn_index: FxHashMap::default(),
			bool_dcn_index: FxHashMap::default(),
			initialized: false,
			new_edges: Vec::new(),
			distances: Matrix::with_dimensions_and_value([0, 0], IntVal::MAX),
			direct_edge: Vec::new(),
			node_active: Vec::new(),
			subscribed_nodes: 0,
			subscribed_gates: 0,
		}
	}

	/// The index of a node, creating it if needed.
	fn node_index(&mut self, prb: &mut Model, x: ModelNode) -> usize {
		if let Some(&index) = self.int_dcn_index.get(&x) {
			// A node removed as fixed or isolated comes back with the new edge.
			// An aliased or dissolved node is never looked up here, since the
			// constraint was recognised on resolved decisions.
			self.node_active[index] = true;
			return index;
		}
		let index = self.graph.int_dcns.len();
		let _ = self.int_dcn_index.insert(x, index);
		self.graph.int_dcns.push(x);
		self.graph.add_node(prb);
		self.direct_edge.push(FxHashSet::default());
		self.node_active.push(true);
		index
	}

	/// The number of active edges.
	fn num_active_edges(&self, ctx: &(impl TrailingActions + ?Sized)) -> usize {
		self.graph.active_out.iter().map(|l| l.len(ctx)).sum()
	}

	/// Remove the nodes that no longer carry information.
	fn reduce(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		self.check_remove_fixed_nodes(ctx)?;
		self.check_remove_isolated_nodes(ctx);
		Ok(())
	}

	/// Follow the aliases the rest of the model has introduced, merging nodes
	/// that have become views of one another.
	///
	/// A node aliased onto a Boolean-backed view cannot stay a node, so its
	/// edges are re-emitted as clauses; see [`Self::encode_dissolved_node`]. A
	/// node aliased onto a constant is left for
	/// [`Self::check_remove_fixed_nodes`].
	fn resolve_aliases(
		&mut self,
		ctx: &mut model::SimplificationContext<'_>,
	) -> Result<(), <Model as ReasoningEngine>::Conflict> {
		for n in 0..self.graph.num_nodes() {
			if !self.node_active[n] {
				continue;
			}
			let node: model::View<IntVal> = self.graph.int_dcns[n].into();
			let alias = node.resolve_alias(ctx.0);
			if node == alias.0 {
				continue;
			}
			trace!(target: "diff_logic", n = ?n, alias = ?alias.0, "node has been aliased");
			let offset = alias.offset();
			let key = alias
				.integer_decision()
				.map(|d| ScaledView::new(alias.scale(), d.into_inner()));
			if let Some(new) = key.and_then(|k| self.int_dcn_index.get(&k).copied()) {
				self.unify_nodes(ctx, n, new, offset)?;
				let _ = self.graph.min_changes.insert(new);
				let _ = self.graph.max_changes.insert(new);
			} else if let Some(key) = key {
				self.update_node_offset(ctx, n, offset)?;
				self.graph.int_dcns[n] = key;
				let _ = self.int_dcn_index.insert(key, n);
			} else if !matches!(alias.0.0, IntView::Const(_)) {
				trace!(target: "diff_logic", n = ?n, "dissolving a node that is no longer a decision");
				let edges = self.graph.edges_at(n, |slot| ctx.trailed(slot));
				self.encode_dissolved_node(
					ctx,
					n,
					&alias.0,
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
					if self.graph.edges[e].bool_dcn.is_some() {
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
			self.graph.bool_dcns[gate].fix(ctx, false, NO_REASON)?;
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
		let x_dcn = x.resolve_alias(ctx.0).integer_decision().map(|d| d.idx());
		let y_dcn = y.resolve_alias(ctx.0).integer_decision().map(|d| d.idx());
		if x_dcn != y_dcn && x_dcn.is_some() && y_dcn.is_some() {
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
			(0..self.graph.bool_dcns.len())
				.filter(|&b| !self.graph.bool_implications[b].is_empty(ctx))
				.count(),
			self.num_active_edges(ctx),
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
				self.graph.int_dcns[new],
				self.graph.int_dcns[to],
				val - offset,
				None,
			)? && !self.is_redundant(new, to, val - offset)
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
				self.graph.int_dcns[from],
				self.graph.int_dcns[new],
				val + offset,
				None,
			)? && !self.is_redundant(from, new, val + offset)
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
				self.graph.int_dcns[new],
				self.graph.int_dcns[edge.to],
				edge.val - offset,
				edge.bool_dcn.map(|b| self.graph.bool_dcns[b]),
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
				self.graph.int_dcns[edge.from],
				self.graph.int_dcns[new],
				edge.val + offset,
				edge.bool_dcn.map(|b| self.graph.bool_dcns[b]),
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
		// The target may have been removed as isolated before; it carries the
		// moved edges now.
		self.node_active[new] = true;
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
		if let Some(lb) = self.graph.derived_min[n].as_mut() {
			*lb -= offset;
		}
		if let Some(ub) = self.graph.derived_max[n].as_mut() {
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
				self.graph.int_dcns[n],
				self.graph.int_dcns[to],
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
				self.graph.int_dcns[from],
				self.graph.int_dcns[n],
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
				self.graph.int_dcns[n],
				self.graph.int_dcns[edge.to],
				edge.val,
				edge.bool_dcn.map(|b| self.graph.bool_dcns[b]),
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
				self.graph.int_dcns[edge.from],
				self.graph.int_dcns[n],
				edge.val,
				edge.bool_dcn.map(|b| self.graph.bool_dcns[b]),
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
			match edge.bool_dcn {
				// A gate that is false satisfies its edge vacuously.
				Some(b) => self.graph.bool_dcns[b].polarity(ctx, Polarity::Negative),
				// `x - y ≤ d` is easier to satisfy the smaller `x` and the
				// larger `y` are.
				None => {
					self.graph.int_dcns[edge.from].polarity(ctx, Polarity::Negative);
					self.graph.int_dcns[edge.to].polarity(ctx, Polarity::Positive);
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
		let mut new_active = false;
		if !self.initialized {
			self.initialize(ctx)?;
		} else {
			for &e in &new_edges {
				if self.graph.edges[e].bool_dcn.is_none() {
					self.graph.propagate_edge_addition::<Model, true>(ctx, e)?;
					new_active = true;
				}
			}
		}

		self.resolve_aliases(ctx)?;
		<Self as Propagator<Model>>::propagate(self, ctx)?;

		// At the lowest priority the cheaper constraints have reached their
		// fixpoint, so the edges they fold into have all arrived; any change
		// made here wakes them again.
		let mut analysed = false;
		if new_active {
			self.reduce(ctx)?;
			analysed = self.johnson_full(ctx)?;
		}
		if !analysed {
			// Without a new pass, the new implied edges are checked against the
			// distances on record. Those are exact when no active edge was
			// added, and otherwise only too long, which is conservative.
			for e in new_edges {
				if self.graph.is_open(ctx, e) {
					self.resolve_implied_edge(ctx, e)?;
				}
			}
		}

		self.reduce(ctx)?;
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
		let mut int_dcns = Vec::new();
		let mut dissolved = Vec::new();
		for (n, &active) in self.node_active.iter().enumerate() {
			if !active {
				continue;
			}
			let view = ctx.solver_view(model::View::from(self.graph.int_dcns[n]));
			match view.0 {
				solver::IntView::Linear(lin) => {
					keep[n] = true;
					offsets[n] = lin.offset;
					int_dcns.push(ScaledView::new(lin.scale, lin.var));
				}
				solver::IntView::Bool(_) | solver::IntView::Const(_) => dissolved.push((n, view)),
			}
		}
		for (n, view) in dissolved {
			// Nothing is removed here, so an edge between two dissolved nodes
			// is encoded by the earlier of the two only.
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
		// An open edge implies an unfixed gate: edges are closed or activated
		// when their gate is fixed, and `add_edge` never opens one on a
		// decided gate.
		let bool_dcns = self
			.graph
			.bool_dcns
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
			nodes = int_dcns.len(),
			gates = bool_dcns.len(),
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
			int_dcns,
			bool_dcns,
			&remap_vec(&keep),
			&remap_vec(&gate_active),
			&offsets,
		)));
		// The lowerer records the last two propagators posted, in this order,
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
		debug_assert_ne!(
			event,
			IntEvent::Domain,
			"the component only subscribes to bound changes"
		);
		self.graph.notify_int_change(ctx, data as usize, event)
	}

	fn initialize(&mut self, ctx: &mut ModelInitContext<'_>) {
		// The most expensive step, so it waits for the cheaper constraints.
		ctx.set_priority(PriorityLevel::Lowest);
		// Usually a no-op: the component is created before its first edge, and
		// `Model::post_difference` subscribes as nodes and gates appear.
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
			.int_dcns
			.iter()
			.enumerate()
			.skip(self.subscribed_nodes)
		{
			n.advise_when(ctx, IntPropCond::Bounds, i as u64);
		}
		self.subscribed_nodes = self.graph.int_dcns.len();
		for (i, &b) in self
			.graph
			.bool_dcns
			.iter()
			.enumerate()
			.skip(self.subscribed_gates)
		{
			b.advise_when_fixed(ctx, i as u64);
		}
		self.subscribed_gates = self.graph.bool_dcns.len();
	}
}
