//! Structure and algorithms for a global difference logic propagator.

use std::{
	cell::RefCell,
	cmp::{Reverse, max, min},
	fmt::Debug,
	hash::Hash,
	mem,
	rc::Rc,
};

use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::trace;

use crate::{
	Conjunction, IntVal, Model,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, ConstructionActions,
		InitActions, IntDecisionActions, IntExplanationActions, IntInitActions,
		IntInspectionActions, IntSimplificationActions, PostingActions, PropagationActions,
		ReasoningContext, ReasoningEngine, SimplificationActions, TrailAccessActions, Trailed,
		TrailingActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, IntModelActions, IntSolverActions,
		Propagator, ReasonBuilder, SimplificationStatus,
		int_linear::{IntLinear, LinComparator, Reification},
	},
	helpers::{
		matrix::Matrix,
		overflow::{OverflowImpossible, OverflowPossible},
		priority_queue::LazyPriorityQueue,
		trailed_list::TrailedList,
		trailed_open_list::TrailedOpenList,
	},
	lower::{LoweringContext, LoweringError},
	model,
	model::{
		expressions::BoolFormula,
		view::{boolean::BoolView, integer::IntView},
	},
	solver,
	solver::{
		IntLitMeaning,
		activation_list::{IntEvent, IntPropCond},
		engine::Engine,
		queue::PriorityLevel,
	},
	views::{LinearBoolView, LinearView},
};
/*-----------------------------------------------------
- Collection and processing of difference constraints -
-----------------------------------------------------*/

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Different types of (potential) difference logic constraints.
pub enum DifferenceLogicConstraint {
	/// A globally active difference constraint: x - y <= d
	Global(model::View<IntVal>, model::View<IntVal>, IntVal),
	/// An implied difference constraint: b -> x - y <= d
	Implied(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	),
	/// A reified difference constraint: b <-> x - y <= d
	Reified(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	),
	/// An implied equality constraint: b -> x - y == d (without implication is
	/// covered by views)
	ImpliedEquals(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	),
	/// A not equals constraint: x - y != d
	NotEquals(model::View<IntVal>, model::View<IntVal>, IntVal),
	/// An implied not equals constraint: b -> x - y != d
	ImpliedNotEquals(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	),
	/// A reified equality constraint: b <-> x - y == d
	ReifiedEquals(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	),
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// User-defined parameters for difference logic.
pub struct DifferenceLogicParameters {
	/// Priority of difference logic bound propagation.
	priority_level_bounds: PriorityLevel,
	/// Priority of difference logic bool propagation.
	priority_level_bools: PriorityLevel,
	/// Whether to use inc_imp for checking implied constraints.
	use_inc_imp: bool,
	/// Mode for explaining boolean changes.
	bool_reasons: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Representation of set of raw difference constraints within a model.
pub struct DifferenceLogicCollection {
	/// Level of difference logic to add.
	level: u8,
	/// User-defined parameters for difference logic.
	parameters: DifferenceLogicParameters,
	/// List of raw difference constraints.
	raw_constraints: Vec<DifferenceLogicConstraint>,
}

/// Parse a priority level from the given integer.
fn parse_priority_level(level: u8) -> PriorityLevel {
	match level {
		0 => PriorityLevel::Lowest,
		1 => PriorityLevel::Low,
		2 => PriorityLevel::Medium,
		3 => PriorityLevel::High,
		4 => PriorityLevel::Highest,
		5 => PriorityLevel::Immediate,
		_ => panic!("Priority level needs to be within [0,...,5], given level {level} is invalid"),
	}
}

/// Transform an implied not equals constraint to implied difference constraints
/// by introducing 2 new boolean decision variables.
fn add_implied_not_equals(
	model: &mut Model,
	imp_constraints: &mut Vec<(
		model::View<bool>,
		model::View<IntVal>,
		model::View<IntVal>,
		IntVal,
	)>,
	b: model::View<bool>,
	x: model::View<IntVal>,
	y: model::View<IntVal>,
	d: IntVal,
) {
	let decision1 = model.new_bool_decision();
	let decision2 = model.new_bool_decision();
	model.post_constraint(Formula::Or(vec![
		Formula::from(!b),
		Formula::from(decision1),
		Formula::from(decision2),
	]));
	model.post_constraint(Formula::Or(vec![
		Formula::from(!decision1),
		Formula::from(!decision2),
	]));
	imp_constraints.push((decision1, x, y, d - 1));
	imp_constraints.push((decision2, y, x, -d - 1));
}

impl DifferenceLogicCollection {
	/// Create a new collection of difference constraints with the given
	/// parameters.
	pub(crate) fn new(
		level: u8,
		priority_level_bounds: u8,
		priority_level_bools: u8,
		use_inc_imp: bool,
		bool_reasons: u8,
	) -> Self {
		Self {
			level,
			parameters: DifferenceLogicParameters {
				priority_level_bounds: parse_priority_level(priority_level_bounds),
				priority_level_bools: parse_priority_level(priority_level_bools),
				use_inc_imp,
				bool_reasons,
			},
			raw_constraints: Vec::new(),
		}
	}

	/// Add a raw difference constraint if accepted, return acceptance status.
	pub(crate) fn add(&mut self, constraint: DifferenceLogicConstraint) -> bool {
		let accept = match constraint {
			// Level 3: Include not equals constraints which require additional boolean variables.
			DifferenceLogicConstraint::NotEquals(_, _, _)
			| DifferenceLogicConstraint::ImpliedNotEquals(_, _, _, _)
			| DifferenceLogicConstraint::ReifiedEquals(_, _, _, _) => self.level > 2,
			// Level 2+: Accept implied equals constraints.
			DifferenceLogicConstraint::ImpliedEquals(_, _, _, _) => self.level > 1,
			// Always accept global constraints and implied / reified constraints.
			_ => true,
		};
		if accept {
			self.raw_constraints.push(constraint);
		}
		accept
	}

	/// Process the raw difference constraints and transform them to global and
	/// implied difference constraints.
	pub(crate) fn process(
		&mut self,
		model: &mut Model,
	) -> Result<Option<DifferenceLogicModel>, LoweringError> {
		let mut global_constraints = Vec::new();
		let mut imp_constraints = Vec::new();
		for raw in self.raw_constraints.iter() {
			match raw {
				DifferenceLogicConstraint::Global(x, y, d) => global_constraints.push((*x, *y, *d)),
				DifferenceLogicConstraint::Implied(b, x, y, d) => {
					imp_constraints.push((*b, *x, *y, *d));
				}
				DifferenceLogicConstraint::Reified(b, x, y, d) => {
					imp_constraints.push((*b, *x, *y, *d));
					imp_constraints.push((!*b, *y, *x, -*d - 1));
				}
				// b -> x - y == d is transformed to b -> x - y <= d and b -> x - y >= d.
				DifferenceLogicConstraint::ImpliedEquals(b, x, y, d) => {
					imp_constraints.push((*b, *x, *y, *d));
					imp_constraints.push((*b, *y, *x, -*d));
				}
				// x - y != d is transformed to b -> x - y < d and !b -> x - y > d for a new boolean
				// variable b.
				DifferenceLogicConstraint::NotEquals(x, y, d) => {
					let decision = model.new_bool_decision();
					imp_constraints.push((decision, *x, *y, *d - 1));
					imp_constraints.push((!decision, *y, *x, -*d - 1));
				}
				// b -> x - y != d is transformed to b -> c \/ e; !c \/ !e; c -> x - y < d;
				// e -> x - y > d for new boolean variables c and e.
				DifferenceLogicConstraint::ImpliedNotEquals(b, x, y, d) => {
					add_implied_not_equals(model, &mut imp_constraints, *b, *x, *y, *d);
				}
				// b <-> x - y == d is transformed to b -> x - y == d and !b -> x - y != d
				DifferenceLogicConstraint::ReifiedEquals(b, x, y, d) => {
					imp_constraints.push((*b, *x, *y, *d));
					imp_constraints.push((*b, *y, *x, -*d));
					add_implied_not_equals(model, &mut imp_constraints, !*b, *x, *y, *d);
				}
			}
		}
		if global_constraints.is_empty() && imp_constraints.is_empty() {
			return Ok(None);
		}
		Ok(Some(DifferenceLogicModel::new(
			model,
			self.parameters.clone(),
			global_constraints,
			imp_constraints,
		)?))
	}
}

/*--------------------------------------------------------
- Model of difference logic for the simplification stage -
--------------------------------------------------------*/

/// Check if the underlying variables are different, if not reemit the
/// potentially implied difference constraint.
fn check_vars_different<E>(
	ctx: &mut E::PropagationCtx<'_>,
	x: model::View<IntVal>,
	y: model::View<IntVal>,
	d: IntVal,
	b: Option<model::View<bool>>,
) -> Result<bool, E::Conflict>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
	model::View<IntVal>: IntModelActions<E>,
{
	if x == y && d >= 0 {
		trace!(b = ?b, x = ?x, y = ?y, d = ?d, "removing redundant edge");
		return Ok(false);
	}
	let x_var = get_int_var_index(ctx.resolve_alias(x));
	let y_var = get_int_var_index(ctx.resolve_alias(y));
	if x_var == y_var || x_var.is_none() || y_var.is_none() {
		trace!(b = ?b, x = ?x, y = ?y, d = ?d, "reemitting edge with same underlying variable or constant");
		let terms = vec![x, y.bounding_neg(ctx)?];
		if IntLinear::can_overflow(ctx, &terms) {
			ctx.post_constraint(IntLinear::<OverflowPossible> {
				terms,
				rhs: d.into(),
				reif: b.map(Reification::ImpliedBy),
				comparator: LinComparator::LessEq,
			});
		} else {
			ctx.post_constraint(IntLinear::<OverflowImpossible> {
				terms,
				rhs: d,
				reif: b.map(Reification::ImpliedBy),
				comparator: LinComparator::LessEq,
			});
		}
		return Ok(false);
	}
	Ok(true)
}

/// Get the underlying variable index for a boolean decision (None if constant).
fn get_bool_var_index(b: model::View<bool>) -> Option<usize> {
	match b.0 {
		BoolView::Decision(d) => Some(d.idx()),
		BoolView::Const(_) => None,
		BoolView::IntEq(d, _) => Some(d.idx()),
		BoolView::IntGreaterEq(d, _) => Some(d.idx()),
		BoolView::IntLess(d, _) => Some(d.idx()),
		BoolView::IntNotEq(d, _) => Some(d.idx()),
	}
}

/// Get the underlying variable index for an integer decision (None if
/// constant).
fn get_int_var_index(x: model::View<IntVal>) -> Option<usize> {
	match x.0 {
		IntView::Const(_) => None,
		IntView::Linear(view) => Some(view.var.idx()),
		IntView::Bool(view) => get_bool_var_index(view.var),
	}
}

/// Get a transformation of the integer decision that has an offset of 0.
fn update_transform(x: model::View<IntVal>) -> (model::View<IntVal>, IntVal) {
	match x.0 {
		IntView::Linear(view) => (
			model::View(IntView::Linear(LinearView::new(view.scale, 0, view.var))),
			view.offset,
		),
		IntView::Bool(view) => (
			model::View(IntView::Bool(LinearBoolView::new(view.scale, 0, view.var))),
			view.offset,
		),
		_ => (x, 0),
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// The initial difference logic structure for model simplification.
pub(crate) struct DifferenceLogicModel {
	/// User-defined parameters for difference logic.
	parameters: DifferenceLogicParameters,
	/// Whether initial simplification has been performed.
	initialized: bool,
	/// Constraint graph.
	graph: DifferenceLogicGraph<model::View<IntVal>, model::View<bool>>,
	/// Mapping of integer decision variables to their index.
	int_var_index: FxHashMap<model::View<IntVal>, usize>,
	/// Minimum distances in the global graph.
	distances: Matrix<2, IntVal>,
	/// Set of nodes reachable with a direct edge of minimum distance for each
	/// node.
	direct_edge: Vec<FxHashSet<usize>>,
	/// Whether a node is active.
	node_active: Vec<bool>,
	/// Number of nodes that are active.
	num_active_nodes: usize,
	/// Whether a boolean is active.
	bool_active: Vec<bool>,
}

/// Return the index associated to the key if existing, or add the key to the
/// list and return the new index.
fn key_to_index<T>(map: &mut FxHashMap<T, usize>, list: &mut Vec<T>, key: T) -> usize
where
	T: Eq + Hash + Clone,
{
	let len = list.len();
	let index = *map.entry(key.clone()).or_insert(len);
	if index == len {
		list.push(key);
	}
	index
}

impl DifferenceLogicModel {
	/// Create a new difference logic model from the given parameters and
	/// collections of difference constraints.
	fn new(
		prb: &mut Model,
		parameters: DifferenceLogicParameters,
		global_constraints: Vec<(model::View<IntVal>, model::View<IntVal>, IntVal)>,
		imp_constraints: Vec<(
			model::View<bool>,
			model::View<IntVal>,
			model::View<IntVal>,
			IntVal,
		)>,
	) -> Result<Self, LoweringError> {
		let mut int_vars = Vec::new();
		let mut int_var_index = FxHashMap::default();
		let mut bool_vars = Vec::new();
		let mut bool_var_index = FxHashMap::default();
		let mut trimmed_constraints = Vec::new();
		let mut trimmed_imp_constraints = Vec::new();

		for (x, y, d) in global_constraints.into_iter() {
			if check_vars_different::<Model>(prb, x, y, d, None)? {
				let (x_trans, xd) = update_transform(x);
				let (y_trans, yd) = update_transform(y);
				trimmed_constraints.push((
					key_to_index(&mut int_var_index, &mut int_vars, x_trans),
					key_to_index(&mut int_var_index, &mut int_vars, y_trans),
					d - xd + yd,
				));
			}
		}

		for (b, x, y, d) in imp_constraints.into_iter() {
			if check_vars_different::<Model>(prb, x, y, d, Some(b))? {
				let (x_trans, xd) = update_transform(x);
				let (y_trans, yd) = update_transform(y);
				if let Some(val) = b.val(prb) {
					// Boolean is already fixed: Global constraint if true, skipped if false.
					trace!(b = ?b, x = ?x, y = ?y, d = ?d, "boolean already fixed");
					if val {
						trimmed_constraints.push((
							key_to_index(&mut int_var_index, &mut int_vars, x_trans),
							key_to_index(&mut int_var_index, &mut int_vars, y_trans),
							d - xd + yd,
						));
					}
				} else {
					trimmed_imp_constraints.push((
						key_to_index(&mut bool_var_index, &mut bool_vars, b),
						key_to_index(&mut int_var_index, &mut int_vars, x_trans),
						key_to_index(&mut int_var_index, &mut int_vars, y_trans),
						d - xd + yd,
					));
				}
			}
		}

		trace!(
			int_vars = int_vars.len(),
			bool_vars = bool_vars.len(),
			global_edges = trimmed_constraints.len(),
			implied_edges = trimmed_imp_constraints.len(),
			"creating graph"
		);
		let num_int = int_vars.len();
		let num_bool = bool_vars.len();
		let mut graph =
			DifferenceLogicGraph::new(prb, int_vars, bool_vars, parameters.bool_reasons);

		// Add global constraints
		for (x, y, d) in trimmed_constraints.into_iter() {
			let _ = graph.new_edge(prb, DiffEdge::new(x, y, d, None));
		}

		// Add implied constraints
		for (b, x, y, d) in trimmed_imp_constraints.into_iter() {
			let _ = graph.new_edge(prb, DiffEdge::new(x, y, d, Some(b)));
		}

		Ok(Self {
			parameters,
			initialized: false,
			graph,
			int_var_index,
			distances: Matrix::with_dimensions_and_value([num_int, num_int], IntVal::MAX),
			direct_edge: vec![FxHashSet::default(); num_int],
			node_active: vec![true; num_int],
			num_active_nodes: num_int,
			bool_active: vec![true; num_bool],
		})
	}

	/// Remove unused nodes and booleans, return whether the graph still has
	/// active nodes.
	fn reduce_and_check<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> bool
	where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		model::View<IntVal>: IntModelActions<E>,
		model::View<bool>: BoolModelActions<E>,
	{
		self.check_remove_fixed_nodes(ctx);
		self.check_remove_isolated_nodes(ctx);
		if self.num_active_nodes == 0 {
			// If no nodes are left, there is nothing more to do
			trace!("no more nodes left, return subsumed");
			return false;
		}
		self.check_remove_isolated_booleans(ctx);
		true
	}

	/// Compute initial pi values by assuming an additional vertex with a 0-cost
	/// path to every other vertex and applying Bellman-Ford. Fail if a
	/// negative cycle is detected.
	fn bellman_ford_init_pi<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		model::View<IntVal>: IntModelActions<E>,
	{
		trace!("calculating initial pi values");
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
		if changed {
			for n in 0..self.graph.num_nodes() {
				for &e in self.graph.active_out[n].iter(ctx) {
					let edge = &self.graph.edges[e];
					if self.graph.pi[edge.from] + edge.val < self.graph.pi[edge.to] {
						trace!(e = ?e, "found negative cycle");
						return Err(ctx.declare_conflict([]));
					}
				}
			}
		}
		Ok(())
	}

	/// Use Johnson's algorithm to get all pairs of shortest paths. Remove edges
	/// not used in any shortest path, close implied edges if possible.
	fn johnson_full<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		model::View<IntVal>: IntModelActions<E>,
		model::View<bool>: BoolModelActions<E>,
	{
		trace!("starting Johnson's");
		let mut pred = vec![vec![usize::MAX; self.graph.num_nodes()]; self.graph.num_nodes()];
		let mut queue = LazyPriorityQueue::new();

		for (n, p) in pred.iter_mut().enumerate() {
			if !self.node_active[n] {
				continue;
			}
			self.graph.reset_visit();
			let _ = queue.push(n, Reverse(0));
			while !queue.is_empty() {
				let (s, Reverse(dist)) = queue.pop().unwrap();
				self.graph.visit(s);
				for &index in self.graph.active_out[s].iter(ctx) {
					let edge = &self.graph.edges[index];
					let new_dist = dist + edge.val + self.graph.pi[s] - self.graph.pi[edge.to];
					if !self.graph.visited[edge.to] {
						let prev = queue.push_increase(edge.to, Reverse(new_dist));
						if prev.is_none_or(|Reverse(old_dist)| new_dist < old_dist) {
							self.distances[[n, edge.to]] =
								new_dist - self.graph.pi[n] + self.graph.pi[edge.to];
							p[edge.to] = s;
						}
					} else if edge.to == n && new_dist < self.distances[[n, n]] {
						// Loop back to origin - store distance, but don't enqueue again
						self.distances[[n, n]] = new_dist;
						p[n] = s;
					}
				}
			}
		}

		trace!("checking impact on edges");
		for n in 0..self.graph.num_nodes() {
			if !self.node_active[n] {
				continue;
			}
			let reached = &mut self.direct_edge[n];
			let mut i = 0;
			while i < self.graph.active_out[n].len(ctx) {
				let &e = self.graph.active_out[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				if self.distances[[n, edge.to]] < edge.val
					|| (self.distances[[n, edge.to]] == edge.val && reached.contains(&edge.to))
				{
					trace!(edge = ?edge, distance = self.distances[[n, edge.to]], "global edge is redundant");
					let _ = self.graph.active_out[n].swap_remove(ctx, i);
					let _ = self.graph.active_in[edge.to].swap_remove_element(ctx, &e);
				} else {
					let _ = reached.insert(edge.to);
					i += 1;
				}
			}

			for i in self.graph.open_out[n].open_iter(ctx) {
				let &e = self.graph.open_out[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				if self.distances[[n, edge.to]] <= edge.val {
					trace!(edge = ?edge, distance = self.distances[[n, edge.to]], "implied edge is redundant");
					self.graph.close_imp_edge(ctx, e);
				}
			}

			for i in self.graph.open_in[n].open_iter(ctx) {
				let &e = self.graph.open_in[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				if self.distances[[n, edge.from]] < -edge.val {
					trace!(edge = ?edge, opposite_distance = self.distances[[n, edge.to]], "implied edge is falsified");
					self.graph.bool_vars[edge.bool_var.unwrap()].fix(ctx, false, [])?;
					self.graph.close_imp_edge(ctx, e);
				}
			}
		}

		for n in (0..self.graph.num_nodes()).filter(|&n| self.node_active[n]) {
			if self.distances[[n, n]] == 0 {
				trace!(n = ?n, "cycle of length 0");
				let origin = n;
				let mut offset = 0;
				let mut cur = n;
				loop {
					let prev = pred[n][cur];
					if prev == n {
						break;
					}
					offset += self.distances[[prev, cur]];
					trace!(prev = ?prev, origin = ?origin, offset = ?offset, "unifying nodes");
					self.graph.int_vars[prev].unify(ctx, self.graph.int_vars[origin] + offset)?;
					cur = prev;
					self.distances[[cur, cur]] = IntVal::MAX;
				}
			}
		}

		Ok(())
	}

	/// Update the offset of a node, including the value of all edges.
	fn update_node_offset<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		n: usize,
		offset: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		model::View<IntVal>: IntModelActions<E>,
		model::View<bool>: BoolModelActions<E>,
	{
		trace!(n = ?n, offset = ?offset, "updating node offset");
		self.graph.pi[n] += offset;
		let mut i = 0;
		while i < self.graph.active_out[n].len(ctx) {
			let &e = self.graph.active_out[n].index(ctx, i);
			let to = self.graph.edges[e].to;
			if check_vars_different(
				ctx,
				self.graph.int_vars[n],
				self.graph.int_vars[to],
				self.graph.edges[e].val,
				None,
			)? {
				self.graph.edges[e].val -= offset;
				i += 1;
			} else {
				let _ = self.graph.active_out[n].swap_remove(ctx, i);
				let _ = self.graph.active_in[to].swap_remove_element(ctx, &e);
			}
		}
		i = 0;
		while i < self.graph.active_in[n].len(ctx) {
			let &e = self.graph.active_in[n].index(ctx, i);
			let from = self.graph.edges[e].from;
			if check_vars_different(
				ctx,
				self.graph.int_vars[from],
				self.graph.int_vars[n],
				self.graph.edges[e].val,
				None,
			)? {
				self.graph.edges[e].val += offset;
				i += 1;
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(ctx, &e);
				let _ = self.graph.active_in[n].swap_remove(ctx, i);
			}
		}
		for i in self.graph.open_out[n].open_iter(ctx) {
			let &e = self.graph.open_out[n].index(ctx, i);
			if check_vars_different(
				ctx,
				self.graph.int_vars[n],
				self.graph.int_vars[self.graph.edges[e].to],
				self.graph.edges[e].val,
				self.graph.edges[e]
					.bool_var
					.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.edges[e].val -= offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_in[n].open_iter(ctx) {
			let &e = self.graph.open_in[n].index(ctx, i);
			if check_vars_different(
				ctx,
				self.graph.int_vars[self.graph.edges[e].from],
				self.graph.int_vars[n],
				self.graph.edges[e].val,
				self.graph.edges[e]
					.bool_var
					.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.edges[e].val += offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		Ok(())
	}

	/// Moves all edges from the old node to the new node, adapted by the given
	/// offset.
	fn unify_nodes<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		old: usize,
		new: usize,
		offset: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		model::View<IntVal>: IntModelActions<E>,
		model::View<bool>: BoolModelActions<E>,
	{
		trace!(old = ?old, new = ?new, offset = ?offset, "moving all edges");
		// Move active edges, remove them if redundant, or fail if conflicting.
		let mut mod_edges = Vec::new();
		for i in 0..self.graph.active_out[old].len(ctx) {
			let &e = self.graph.active_out[old].index(ctx, i);
			let to = self.graph.edges[e].to;
			let val = self.graph.edges[e].val;
			if check_vars_different(
				ctx,
				self.graph.int_vars[new],
				self.graph.int_vars[to],
				val - offset,
				None,
			)? && (self.distances[[new, to]] > val - offset
				|| (self.distances[[new, to]] == val - offset
					&& !self.direct_edge[new].contains(&to)))
			{
				let edge = &mut self.graph.edges[e];
				edge.from = new;
				edge.val -= offset;
				self.graph.active_out[new].push(ctx, e);
				let _ = self.direct_edge[new].insert(edge.to);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_in[to].swap_remove_element(ctx, &e);
			}
		}
		self.graph.active_out[old].clear(ctx);
		for i in 0..self.graph.active_in[old].len(ctx) {
			let &e = self.graph.active_in[old].index(ctx, i);
			let from = self.graph.edges[e].from;
			let val = self.graph.edges[e].val;
			if check_vars_different(
				ctx,
				self.graph.int_vars[from],
				self.graph.int_vars[new],
				val + offset,
				None,
			)? && (self.distances[[from, new]] > val + offset
				|| (self.distances[[from, new]] == val + offset
					&& !self.direct_edge[from].contains(&new)))
			{
				let edge = &mut self.graph.edges[e];
				edge.to = new;
				edge.val += offset;
				self.graph.active_in[new].push(ctx, e);
				let _ = self.direct_edge[from].insert(new);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(ctx, &e);
			}
		}
		self.graph.active_in[old].clear(ctx);
		// Outgoing implied arcs: First check if they should be closed, then move
		// remaining.
		for i in self.graph.open_out[old].open_iter(ctx) {
			let &e = self.graph.open_out[old].index(ctx, i);
			if !check_vars_different(
				ctx,
				self.graph.int_vars[new],
				self.graph.int_vars[self.graph.edges[e].to],
				self.graph.edges[e].val - offset,
				self.graph.edges[e]
					.bool_var
					.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_out[old].open_iter(ctx) {
			let &e = self.graph.open_out[old].index(ctx, i);
			let edge = &mut self.graph.edges[e];
			edge.from = new;
			edge.val -= offset;
			edge.out_index = self.graph.open_out[new].len();
			self.graph.open_out[new].push(e);
		}
		self.graph.open_out[old].clear(ctx);
		// Incoming implied arcs: First check if they should be closed, then move
		// remaining.
		for i in self.graph.open_in[old].open_iter(ctx) {
			let &e = self.graph.open_in[old].index(ctx, i);
			if !check_vars_different(
				ctx,
				self.graph.int_vars[self.graph.edges[e].from],
				self.graph.int_vars[new],
				self.graph.edges[e].val + offset,
				self.graph.edges[e]
					.bool_var
					.map(|b| self.graph.bool_vars[b]),
			)? {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_in[old].open_iter(ctx) {
			let &e = self.graph.open_in[old].index(ctx, i);
			let edge = &mut self.graph.edges[e];
			edge.to = new;
			edge.val += offset;
			edge.in_index = self.graph.open_in[new].len();
			self.graph.open_in[new].push(e);
		}
		self.graph.open_in[old].clear(ctx);
		// Check consequences of all modified active edges
		for e in mod_edges {
			self.graph.propagate_edge_addition(ctx, e, true, true)?;
		}
		self.node_active[old] = false;
		self.num_active_nodes -= 1;
		Ok(())
	}

	/// Add an implied bound to the model.
	fn add_implied_bound<A: SimplificationActions<Target = Model>>(
		&mut self,
		actions: &mut A,
		bool_var: usize,
		int_var: usize,
		lt: bool,
		value: IntVal,
	) {
		let bound = if lt {
			Box::new(BoolFormula::Atom(self.graph.int_vars[int_var].leq(value)))
		} else {
			Box::new(BoolFormula::Atom(self.graph.int_vars[int_var].geq(value)))
		};
		actions.post_constraint(BoolFormula::Implies(
			Box::new(BoolFormula::Atom(self.graph.bool_vars[bool_var])),
			bound,
		));
	}

	/// Check if nodes with fixed domain exist, if yes remove them from the
	/// graph.
	fn check_remove_fixed_nodes<E>(&mut self, ctx: &mut E::PropagationCtx<'_>)
	where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		model::View<IntVal>: IntModelActions<E>,
		model::View<bool>: BoolModelActions<E>,
	{
		for n in 0..self.graph.num_nodes() {
			// Remove node if it is still active, fixed, and does not have bound changes to
			// propagate.
			if self.node_active[n]
				&& let Some(val) = self.graph.int_vars[n].val(ctx)
				&& !self.graph.lower_bound_changes.contains(&n)
				&& !self.graph.upper_bound_changes.contains(&n)
			{
				trace!(n = ?n, "removing variable with fixed value");
				self.node_active[n] = false;
				self.num_active_nodes -= 1;
				for &e in self.graph.active_out[n].iter(ctx) {
					let edge = &self.graph.edges[e];
					let _ = self.graph.active_in[edge.to].swap_remove_element(ctx, &e);
				}
				for &e in self.graph.active_in[n].iter(ctx) {
					let edge = &self.graph.edges[e];
					let _ = self.graph.active_out[edge.from].swap_remove_element(ctx, &e);
				}
				for i in self.graph.open_out[n].open_iter(ctx) {
					let &e = self.graph.open_out[n].index(ctx, i);
					let edge = &self.graph.edges[e];
					trace!(edge = ?edge, "reemitting implied outgoing edge");
					self.add_implied_bound(
						ctx,
						edge.bool_var.unwrap(),
						edge.to,
						false,
						val - edge.val,
					);
					self.graph.close_imp_edge(ctx, e);
				}
				for i in self.graph.open_in[n].open_iter(ctx) {
					let &e = self.graph.open_in[n].index(ctx, i);
					let edge = &self.graph.edges[e];
					trace!(edge = ?edge, "reemitting implied incoming edge");
					self.add_implied_bound(
						ctx,
						edge.bool_var.unwrap(),
						edge.from,
						true,
						val + edge.val,
					);
					self.graph.close_imp_edge(ctx, e);
				}
			}
		}
	}

	/// Check if nodes with no edges exist, if yes remove them from the graph.
	fn check_remove_isolated_nodes<A: TrailAccessActions>(&mut self, actions: &A) {
		for n in 0..self.graph.num_nodes() {
			if self.node_active[n]
				&& self.graph.active_out[n].is_empty(actions)
				&& self.graph.active_in[n].is_empty(actions)
				&& self.graph.open_out[n].is_empty(actions)
				&& self.graph.open_in[n].is_empty(actions)
			{
				trace!(n = ?n, "removing variable with no edges");
				self.node_active[n] = false;
				self.num_active_nodes -= 1;
			}
		}
	}

	/// Check if isolated booleans exist, if yes mark them as inactive.
	fn check_remove_isolated_booleans<A: TrailAccessActions>(&mut self, actions: &A) {
		for b in 0..self.graph.bool_implications.len() {
			if self.bool_active[b] && self.graph.bool_implications[b].num_open(actions) == 0 {
				trace!(b = ?b, "removing boolean with no edges");
				self.bool_active[b] = false;
			}
		}
	}

	/// Return statistics about the size of the graph.
	pub(crate) fn output_statistics<A: TrailAccessActions>(
		&self,
		actions: &A,
	) -> (usize, usize, usize, usize) {
		(
			self.graph.int_vars.len(),
			self.graph.bool_vars.len(),
			(0..self.graph.num_nodes())
				.map(|n| self.graph.active_out[n].len(actions))
				.sum(),
			(0..self.graph.num_nodes())
				.map(|n| self.graph.open_out[n].num_open(actions))
				.sum(),
		)
	}
}

impl<E> Constraint<E> for DifferenceLogicModel
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
{
	#[tracing::instrument(name = "diff_logic_simplify", level = "trace", skip(self, ctx))]
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		if !self.initialized {
			trace!(
				"starting initial propagation with graph: {}",
				self.graph.to_dot(ctx, self.node_active.clone())
			);
			self.bellman_ford_init_pi(ctx)?;
			self.graph.propagate_bounds(ctx)?;
			self.graph.propagate_booleans(ctx, false, true)?;
			// Already do removals before Johnson's to reduce complexity of the graph
			self.check_remove_fixed_nodes(ctx);
			self.check_remove_isolated_nodes(ctx);
			self.johnson_full(ctx)?;
			self.initialized = true;
		} else {
			for n in 0..self.graph.int_vars.len() {
				if self.node_active[n] {
					// Check if variables have been unified
					let alias = ctx.resolve_alias(self.graph.int_vars[n]);
					if self.graph.int_vars[n] != alias {
						trace!(n = ?n, alias = ?alias, "var alias is different");
						let (v_trans, vd) = update_transform(alias);
						if let Some(&new) = self.int_var_index.get(&v_trans) {
							self.unify_nodes(ctx, n, new, vd)?;
							self.graph.lower_bound_changes.insert(new);
							self.graph.upper_bound_changes.insert(new);
						} else if !matches!(alias.0, IntView::Const(_)) {
							*self.graph.lower_bound[n].as_mut().unwrap() -= vd;
							*self.graph.upper_bound[n].as_mut().unwrap() -= vd;
							self.update_node_offset(ctx, n, vd)?;
							self.graph.int_vars[n] = v_trans;
						}
					}
				}
			}

			self.propagate(ctx)?;
		}

		if !self.reduce_and_check(ctx) {
			trace!("diff logic subsumed");
			return Ok(SimplificationStatus::Subsumed);
		}

		debug_assert!((0..self.graph.num_nodes()).all(|n| {
			self.graph.open_out[n]
				.open_iter(ctx)
				.all(|i| self.graph.edges[*self.graph.open_out[n].index(ctx, i)].out_index == i)
		}));
		debug_assert!((0..self.graph.num_nodes()).all(|n| {
			self.graph.open_in[n]
				.open_iter(ctx)
				.all(|i| self.graph.edges[*self.graph.open_in[n].index(ctx, i)].in_index == i)
		}));

		trace!(
			"graph after simplify: {}",
			self.graph.to_dot(ctx, self.node_active.clone())
		);
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, ctx: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		trace!("transforming diff logic to solver");
		let int_vars = self
			.graph
			.int_vars
			.iter()
			.enumerate()
			.filter(|(i, _)| self.node_active[*i])
			.map(|(_, &v)| ctx.solver_view(v))
			.collect_vec();
		let bool_vars = self
			.graph
			.bool_vars
			.iter()
			.enumerate()
			.filter(|(i, _)| self.bool_active[*i])
			.map(|(_, &v)| ctx.solver_view(v))
			.collect_vec();
		let node_map = remap_vec(&self.node_active);
		let bool_map = remap_vec(&self.bool_active);
		let graph_cell = Rc::new(RefCell::new(DifferenceLogicGraph::from(
			&self.graph,
			ctx,
			int_vars,
			bool_vars,
			node_map,
			bool_map,
		)));
		DifferenceLogicBounds::post(
			ctx,
			self.parameters.priority_level_bounds,
			Rc::clone(&graph_cell),
		);
		DifferenceLogicBooleans::post(
			ctx,
			self.parameters.priority_level_bools,
			self.parameters.use_inc_imp,
			Rc::clone(&graph_cell),
		);
		Ok(())
	}
}

impl<E> Propagator<E> for DifferenceLogicModel
where
	E: ReasoningEngine,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
{
	fn advise_of_bool_change(&mut self, _ctx: &mut E::NotificationCtx<'_>, data: u64) -> bool {
		self.graph.fixed_bools.insert(data as usize)
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationCtx<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		let data = data as usize;
		let mut enqueue = false;
		if event == IntEvent::LowerBound || event == IntEvent::Fixed {
			enqueue = self.graph.notify_lb_change(ctx, data);
		}
		if event == IntEvent::UpperBound || event == IntEvent::Fixed {
			enqueue |= self.graph.notify_ub_change(ctx, data);
		}
		enqueue
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		for (i, &n) in self.graph.int_vars.iter().enumerate() {
			n.advise_when(ctx, IntPropCond::Bounds, i as u64);
		}
		for (i, &b) in self.graph.bool_vars.iter().enumerate() {
			b.advise_when_fixed(ctx, i as u64);
		}
		ctx.enqueue_now(true);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.graph.propagate_bounds(ctx)?;
		self.graph.propagate_booleans(ctx, true, true)?;
		Ok(())
	}
}

/*------------------------------------------------------------
- Common graph structure used for simplification and solving -
------------------------------------------------------------*/

#[derive(Debug, Clone, PartialEq, Eq)]
/// An edge in the difference logic graph (bool_var -> from - to <= val).
pub struct DiffEdge {
	/// Source node index.
	from: usize,
	/// Target node index.
	to: usize,
	/// Difference value.
	val: IntVal,
	/// Index of the Boolean for the difference constraints (None for globally
	/// active constraints).
	bool_var: Option<usize>,
	/// Index of this edge in the list of edges implied by the boolean
	bool_index: usize,
	/// Index of this edge in the list of open outgoing edges
	out_index: usize,
	/// Index of this edge in the list of open incoming edges
	in_index: usize,
}

impl DiffEdge {
	/// Create a new difference edge.
	fn new(from: usize, to: usize, val: IntVal, bool_var: Option<usize>) -> Self {
		Self {
			from,
			to,
			val,
			bool_var,
			bool_index: 0,
			out_index: 0,
			in_index: 0,
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A graph of difference constraints.
pub struct DifferenceLogicGraph<I, B> {
	/// Integer variables.
	int_vars: Vec<I>,
	/// Boolean variables.
	bool_vars: Vec<B>,
	/// List of active outgoing edges for each node.
	active_out: Vec<TrailedList<usize>>,
	/// List of active incoming edges for each node.
	active_in: Vec<TrailedList<usize>>,
	/// List of open outgoing edges for each node.
	open_out: Vec<TrailedOpenList<usize>>,
	/// List of open incoming edges for each node.
	open_in: Vec<TrailedOpenList<usize>>,
	/// Updated lower bound for each node.
	lower_bound: Vec<Option<IntVal>>,
	/// Updated upper bound for each node.
	upper_bound: Vec<Option<IntVal>>,
	/// Potential function value for each node.
	pi: Vec<IntVal>,
	/// Backtrace for shortest path calculations for each node.
	backtrace: Vec<Option<(usize, Option<usize>)>>,
	/// Visited state for each node.
	visited: Vec<bool>,
	/// Number of open implication edges.
	num_open_edges: Trailed<usize>,
	/// List of all edges in the graph.
	edges: Vec<DiffEdge>,
	/// Map from boolean indices to their implied edges.
	bool_implications: Vec<TrailedOpenList<usize>>,
	/// List of updated visited states.
	visited_updates: Vec<usize>,
	/// List of integer variable indices with reported lower bound changes.
	lower_bound_changes: FxHashSet<usize>,
	/// List of integer variable indices with reported upper bound changes.
	upper_bound_changes: FxHashSet<usize>,
	/// Current lower bound updates.
	lb_updates: Vec<usize>,
	/// Current upper bound updates.
	ub_updates: Vec<usize>,
	/// List of boolean variable indices that have recently been reported as
	/// fixed to true.
	fixed_bools: FxHashSet<usize>,
	/// Mode to produce reasons for booleans set to false.
	bool_reasons: u8,
}

/// Return a vector where each element is either None if the position in the
/// input is False, or the current count of the occurrences of True in the
/// input. E.g., [false, true, true, false, true] results in [None, Some(0),
/// Some(1), None, Some(2)].
fn remap_vec(vec: &[bool]) -> Vec<Option<usize>> {
	vec.iter()
		.scan(0_usize, |count, &a| {
			if a {
				*count += 1;
				Some(Some(*count - 1))
			} else {
				Some(None)
			}
		})
		.collect_vec()
}

impl<I, B> DifferenceLogicGraph<I, B> {
	/// Create a new difference logic graph from the given variables without
	/// edges.
	fn new<E: ConstructionActions + ?Sized>(
		solver: &mut E,
		int_vars: Vec<I>,
		bool_vars: Vec<B>,
		bool_reasons: u8,
	) -> Self {
		let num_int = int_vars.len();
		let num_bool = bool_vars.len();
		Self {
			int_vars,
			bool_vars,
			active_out: (0..num_int)
				.map(|_| TrailedList::new(solver, true))
				.collect_vec(),
			active_in: (0..num_int)
				.map(|_| TrailedList::new(solver, true))
				.collect_vec(),
			open_out: (0..num_int)
				.map(|_| TrailedOpenList::new(solver))
				.collect_vec(),
			open_in: (0..num_int)
				.map(|_| TrailedOpenList::new(solver))
				.collect_vec(),
			lower_bound: vec![None; num_int],
			upper_bound: vec![None; num_int],
			pi: vec![0; num_int],
			backtrace: vec![None; num_int],
			visited: vec![false; num_int],
			num_open_edges: solver.new_trailed(0),
			edges: Vec::new(),
			bool_implications: (0..num_bool)
				.map(|_| TrailedOpenList::new(solver))
				.collect_vec(),
			visited_updates: Vec::new(),
			lower_bound_changes: (0..num_int).collect(),
			upper_bound_changes: (0..num_int).collect(),
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			fixed_bools: FxHashSet::default(),
			bool_reasons,
		}
	}

	/// Create a new difference logic graph from the given existing graph. The
	/// old trail is used to access trailed information for the existing graph.
	/// Old nodes are mapped (if present) or dropped (if None) according to
	/// node_map, booleans are mapped according to bool_map.
	fn from<I1, B1>(
		from: &DifferenceLogicGraph<I1, B1>,
		ctx: &mut LoweringContext,
		int_vars: Vec<I>,
		bool_vars: Vec<B>,
		node_map: Vec<Option<usize>>,
		bool_map: Vec<Option<usize>>,
	) -> Self {
		let mut new_graph = DifferenceLogicGraph::new(ctx, int_vars, bool_vars, from.bool_reasons);
		new_graph.lower_bound_changes.clear();
		new_graph.upper_bound_changes.clear();
		new_graph.pi = from
			.pi
			.iter()
			.enumerate()
			.filter(|(i, _)| node_map[*i].is_some())
			.map(|(_, &pi)| pi)
			.collect_vec();

		// Identify edges in use
		let mut edge_map = vec![0; from.edges.len()];
		for n in (0..from.num_nodes()).filter(|i| node_map[*i].is_some()) {
			for &e in from.active_out[n].iter(ctx.model_trail()) {
				edge_map[e] = 1;
			}
			for i in from.open_out[n].open_iter(ctx.model_trail()) {
				edge_map[*from.open_out[n].index(ctx.model_trail(), i)] = 2;
			}
		}

		// Remap used edges
		for (e, edge) in from.edges.iter().enumerate() {
			if edge_map[e] > 0 {
				new_graph.new_edge(
					ctx,
					DiffEdge::new(
						node_map[edge.from].unwrap(),
						node_map[edge.to].unwrap(),
						edge.val,
						if edge_map[e] == 1 {
							None
						} else {
							Some(bool_map[edge.bool_var.unwrap()].unwrap())
						},
					),
				);
			}
		}

		new_graph
	}

	/// Return the total number of nodes.
	fn num_nodes(&self) -> usize {
		self.int_vars.len()
	}

	/// Add a new edge to the graph, return the index. Depending on the boolean,
	/// the edge is added globally (boolean is None) or as an implied edge.
	fn new_edge<T: TrailingActions + ?Sized>(
		&mut self,
		actions: &mut T,
		mut edge: DiffEdge,
	) -> usize {
		let index = self.edges.len();
		if let Some(b) = edge.bool_var {
			edge.bool_index = self.bool_implications[b].len();
			self.bool_implications[b].push(index);
			edge.out_index = self.open_out[edge.from].len();
			self.open_out[edge.from].push(index);
			edge.in_index = self.open_in[edge.to].len();
			self.open_in[edge.to].push(index);
			let _ = actions.set_trailed(
				self.num_open_edges,
				actions.trailed(self.num_open_edges) + 1,
			);
		} else {
			self.active_out[edge.from].push(actions, index);
			self.active_in[edge.to].push(actions, index);
		}
		self.edges.push(edge);
		index
	}

	/// Activate the implied edge given by the index.
	fn activate_imp_edge<T: TrailingActions>(&mut self, actions: &mut T, index: usize) {
		let edge = &self.edges[index];
		self.active_out[edge.from].push(actions, index);
		self.active_in[edge.to].push(actions, index);
	}

	/// Close the implied edge given by the index.
	fn close_imp_edge<T: TrailingActions>(&mut self, actions: &mut T, e: usize) {
		let edge = &self.edges[e];
		let b = edge.bool_var.unwrap();
		let to = edge.to;
		let from = edge.from;
		let bool_index = edge.bool_index;
		let out_index = edge.out_index;
		let in_index = edge.in_index;
		let was_open = self.bool_implications[b]
			.close(actions, bool_index, |&e, i| self.edges[e].bool_index = i)
			& self.open_out[from].close(actions, out_index, |&e, i| self.edges[e].out_index = i)
			& self.open_in[to].close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert!(was_open);
		let _ = actions.set_trailed(
			self.num_open_edges,
			actions.trailed(self.num_open_edges) - 1,
		);
	}

	/// Mark the given node as visited.
	fn visit(&mut self, n: usize) {
		if !self.visited[n] {
			self.visited_updates.push(n);
		}
		self.visited[n] = true;
	}

	/// Reset the visited state of all nodes.
	fn reset_visit(&mut self) {
		for &n in self.visited_updates.iter() {
			self.visited[n] = false;
		}
		self.visited_updates.clear();
	}

	/// Get the current lower bound for the node, either stored or from the
	/// context.
	fn get_cur_lower_bound<Ctx>(&self, ctx: &mut Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext,
		I: IntInspectionActions<Ctx>,
	{
		match self.lower_bound[n] {
			Some(lb) => lb,
			None => self.int_vars[n].min(ctx),
		}
	}

	/// Update the stored lower bound for the node.
	fn update_lb(&mut self, n: usize, val: IntVal) {
		if self.lower_bound[n].is_none() {
			self.lb_updates.push(n);
		}
		self.lower_bound[n] = Some(val);
	}

	/// Get the current upper bound for the node, either stored or from the
	/// context.
	fn get_cur_upper_bound<Ctx>(&self, ctx: &mut Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext,
		I: IntInspectionActions<Ctx>,
	{
		match self.upper_bound[n] {
			Some(ub) => ub,
			None => self.int_vars[n].max(ctx),
		}
	}

	/// Update the stored upper bound for the node.
	fn update_ub(&mut self, n: usize, val: IntVal) {
		if self.upper_bound[n].is_none() {
			self.ub_updates.push(n);
		}
		self.upper_bound[n] = Some(val);
	}

	/// Get the reason for a cycle of negative lengths (all booleans along the
	/// cycle).
	fn get_cycle_reason<Ctx>(&self, node: usize) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext,
		B: BoolPropagationActions<Ctx> + Into<Ctx::Atom>,
	{
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = self.backtrace[var] {
			if let Some(b) = b {
				reason.push(self.bool_vars[b].clone().into());
			}
			var = cur;
		}
		reason
	}

	/// Check incremental addition of the edge given by index to the active
	/// graph. Returns true if addition is possible. Otherwise, false is
	/// returned for implied edges, and a conflict is caused by global edges.
	fn inc_sat<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		new_index: usize,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		B: BoolSolverActions<E>,
	{
		let new_edge = &self.edges[new_index];
		trace!(
			x = new_edge.from,
			y = new_edge.to,
			d = new_edge.val,
			"inc_sat"
		);
		let mut queue = LazyPriorityQueue::new();
		let mut pi_new = FxHashMap::default();
		self.backtrace[new_edge.to] = None;
		let gamma_v = self.pi[new_edge.from] + new_edge.val - self.pi[new_edge.to];
		if gamma_v < 0 {
			let _ = queue.push(new_edge.to, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&new_edge.from).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = pi_new.insert(s, self.pi[s] + gamma_s);
			for &e in self.active_out[s].iter(ctx) {
				let edge = &self.edges[e];
				if !pi_new.contains_key(&edge.to) {
					let gamma_t = pi_new[&s] + edge.val - self.pi[edge.to];
					if gamma_t < 0 {
						let old = queue.push_increase(edge.to, Reverse(gamma_t));
						if old.is_none_or(|Reverse(old_gamma)| gamma_t < old_gamma) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		// If the origin is in the queue, we have a cycle of negative length.
		if queue.get_priority(&new_edge.from).is_some() {
			trace!(b = ?new_edge.bool_var, "cycle with negative length");
			if let Some(b) = new_edge.bool_var {
				self.bool_vars[b].fix(ctx, false, self.get_cycle_reason(new_edge.from))?;
			} else {
				return Err(ctx.declare_conflict(self.get_cycle_reason(new_edge.from)));
			}
			return Ok(false);
		}
		for (var, val) in pi_new {
			self.pi[var] = val;
		}
		Ok(true)
	}

	/// Perform dijkstra from the given node to all relevant nodes in the graph,
	/// return a map of distances. Can be performed in forward or backward
	/// direction.
	fn dijkstra_relevant<A: TrailAccessActions>(
		&mut self,
		actions: &A,
		new_edge: usize,
		reverse: bool,
	) -> FxHashMap<usize, IntVal> {
		self.reset_visit();
		let new_edge = &self.edges[new_edge];
		let origin = if reverse { new_edge.to } else { new_edge.from };
		let relevant_target = if reverse { new_edge.from } else { new_edge.to };
		let mut distances = FxHashMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = LazyPriorityQueue::new();
		let _ = queue.push(origin, Reverse((0, false)));
		let _ = queue.push(
			relevant_target,
			Reverse((
				new_edge.val
					+ if reverse {
						self.pi[relevant_target] - self.pi[origin]
					} else {
						self.pi[origin] - self.pi[relevant_target]
					},
				true,
			)),
		);
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse((dist, relevant))) = queue.pop().unwrap();
			self.visit(s);
			for &e in if reverse {
				self.active_in[s].iter(actions)
			} else {
				self.active_out[s].iter(actions)
			} {
				let edge = &self.edges[e];
				let target = if reverse { edge.from } else { edge.to };
				let new_dist = dist
					+ edge.val + if reverse {
					self.pi[target] - self.pi[s]
				} else {
					self.pi[s] - self.pi[target]
				};
				if !self.visited[target] {
					// Cases where we want to propagate the relevancy of s to t (equals
					// lexicographic order of (new_dist, relevant)):
					// - Path to t with lower distance than before
					// - Path to t with same distance as before and s is not relevant (prefer
					//   irrelevancy in ties)
					let new_relevant = relevant || (s == origin && target == relevant_target);
					let new_prio = Reverse((new_dist, new_relevant));
					let prev = queue.push_increase(target, new_prio);
					if prev != Some(new_prio) {
						if new_relevant {
							// A new shortest distance has been found, add new distance to the map,
							// if key was not present before increase relevant count.
							if distances
								.insert(
									target,
									new_dist
										+ if reverse {
											self.pi[origin] - self.pi[target]
										} else {
											self.pi[target] - self.pi[origin]
										},
								)
								.is_none()
							{
								relevant_count += 1;
							}
						} else {
							// Remove old distance from the map, if key was present before decrease
							// relevant count.
							if distances.remove(&target).is_some() {
								relevant_count -= 1;
							}
						}
					}
				}
			}
			if relevant {
				relevant_count -= 1;
			}
		}
		distances
	}

	/// Check if the new edge given by the index implies or falsifies any of the
	/// open edges.
	fn inc_imp<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		new_index: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		B: BoolSolverActions<E>,
	{
		if ctx.trailed(self.num_open_edges) == 0 {
			trace!("No open implications");
			return Ok(());
		}

		// Incoming paths to relevant nodes starting from u via uv.
		let incoming_u = self.dijkstra_relevant(ctx, new_index, false);
		// Outgoing paths from relevant nodes ending at v via uv.
		let outgoing_v = self.dijkstra_relevant(ctx, new_index, true);
		let indegree_u: usize = incoming_u
			.iter()
			.map(|(&n, _)| self.open_in[n].num_open(ctx))
			.sum();
		let outdegree_v: usize = outgoing_v
			.iter()
			.map(|(&n, _)| self.open_out[n].num_open(ctx))
			.sum();

		let new_edge_val = self.edges[new_index].val;

		if indegree_u < outdegree_v {
			for &n in incoming_u.keys() {
				for i in self.open_in[n].open_iter(ctx) {
					let &e = self.open_in[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, implied)");
					if outgoing_v.contains_key(&edge.from)
						&& outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val
					{
						trace!(edge = ?edge, "constraint is implied");
						self.close_imp_edge(ctx, e);
					}
				}
				for i in self.open_out[n].open_iter(ctx) {
					let &e = self.open_out[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, reverse)");
					if outgoing_v.contains_key(&edge.to)
						&& outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val < -edge.val
					{
						trace!(edge = ?edge, "constraint is falsified since inverse is implied");
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		} else {
			for &n in outgoing_v.keys() {
				for i in self.open_out[n].open_iter(ctx) {
					let &e = self.open_out[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, implied)");
					if incoming_u.contains_key(&edge.to)
						&& outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val
					{
						trace!(edge = ?edge, "constraint is implied");
						self.close_imp_edge(ctx, e);
					}
				}
				for i in self.open_in[n].open_iter(ctx) {
					let &e = self.open_in[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, reverse)");
					if incoming_u.contains_key(&edge.from)
						&& outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val < -edge.val
					{
						trace!(edge = ?edge, "constraint is falsified since inverse is implied");
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		}

		Ok(())
	}

	/// Evaluate and enqueue the lower bound change, return true if the change
	/// is new.
	fn notify_lb_change<Ctx>(&mut self, ctx: &mut Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext,
		I: IntInspectionActions<Ctx>,
	{
		if self.lower_bound[n].is_none_or(|v| v < self.int_vars[n].min(ctx)) {
			return self.lower_bound_changes.insert(n);
		}
		false
	}

	/// Evaluate and enqueue the upper bound change, return true if the change
	/// is new.
	fn notify_ub_change<Ctx>(&mut self, ctx: &mut Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext,
		I: IntInspectionActions<Ctx>,
	{
		if self.upper_bound[n].is_none_or(|v| v > self.int_vars[n].max(ctx)) {
			return self.upper_bound_changes.insert(n);
		}
		false
	}

	/// Set the lower bound int(n) >= value, with the reason bool(bool_var) /\
	/// int(lb_var) >= lb_val.
	fn set_int_lower_bound<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
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
		self.int_vars[n].tighten_min(ctx, value, |ctx: &mut E::PropagationCtx<'_>| {
			let mut reason = vec![self.int_vars[lb_var].lit(ctx, IntLitMeaning::GreaterEq(lb_val))];
			if let Some(b) = bool_var {
				reason.push(self.bool_vars[b].clone().into());
			}
			reason
		})?;
		Ok(())
	}

	/// Set the upper bound int(n) <= value, with the reason bool(bool_var) /\
	/// int(ub_var) <= ub_val.
	fn set_int_upper_bound<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
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
		self.int_vars[n].tighten_max(ctx, value, |ctx: &mut E::PropagationCtx<'_>| {
			let mut reason = vec![self.int_vars[ub_var].lit(ctx, IntLitMeaning::Less(ub_val + 1))];
			if let Some(b) = bool_var {
				reason.push(self.bool_vars[b].clone().into());
			}
			reason
		})?;
		Ok(())
	}

	/// Perform incremental updates of lower bounds.
	fn inc_lb<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		trace!(lb_changes = ?self.lower_bound_changes, "running inc_lb");
		self.reset_visit();
		let pi0 = self
			.lower_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].min(ctx) + self.pi[n])
			.max()
			.unwrap();
		let mut queue = LazyPriorityQueue::new();
		for &n in self.lower_bound_changes.iter() {
			let _ = queue.push(n, Reverse(pi0 - self.int_vars[n].min(ctx) - self.pi[n]));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			if bound > self.get_cur_lower_bound(ctx, s) || self.lower_bound_changes.contains(&s) {
				self.update_lb(s, bound);
				if bound > self.int_vars[s].min(ctx) {
					trace!(n = ?s, bound = ?bound, "updating lower bound");
					let (prev, b) = self.backtrace[s].unwrap();
					let lb = self.get_cur_lower_bound(ctx, prev);
					self.set_int_lower_bound(ctx, s, bound, b, prev, lb)?;
					let _ = self.lower_bound_changes.insert(s);
				}
				for &e in self.active_out[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.to] {
						let path = gamma_s + self.pi[s] + edge.val - self.pi[edge.to];
						let old = queue.push_increase(edge.to, Reverse(path));
						if old.is_none_or(|Reverse(old_path)| path < old_path) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Perform incremental updates of upper bounds.
	fn inc_ub<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		trace!(ub_changes = ?self.upper_bound_changes, "running inc_ub");
		self.reset_visit();
		let pi0 = self
			.upper_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].max(ctx) + self.pi[n])
			.min()
			.unwrap();
		let mut queue = LazyPriorityQueue::new();
		for &n in self.upper_bound_changes.iter() {
			let _ = queue.push(n, Reverse(self.pi[n] + self.int_vars[n].max(ctx) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			if bound < self.get_cur_upper_bound(ctx, s) || self.upper_bound_changes.contains(&s) {
				self.update_ub(s, bound);
				if bound < self.int_vars[s].max(ctx) {
					trace!(n = ?s, bound = ?bound, "updating upper bound");
					let (prev, b) = self.backtrace[s].unwrap();
					let ub = self.get_cur_upper_bound(ctx, prev);
					self.set_int_upper_bound(ctx, s, bound, b, prev, ub)?;
					let _ = self.upper_bound_changes.insert(s);
				}
				for &e in self.active_in[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.from] {
						let path = gamma_s + self.pi[edge.from] + edge.val - self.pi[s];
						let old = queue.push_increase(edge.from, Reverse(path));
						if old.is_none_or(|Reverse(old_path)| path < old_path) {
							self.backtrace[edge.from] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Reset the stored upper and lower bounds as well as queued bound changes.
	fn reset_bounds(&mut self) {
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		for &n in self.lb_updates.iter() {
			self.lower_bound[n] = None;
		}
		for &n in self.ub_updates.iter() {
			self.upper_bound[n] = None;
		}
		self.lb_updates.clear();
		self.ub_updates.clear();
	}

	/// Given an eager reason for setting the boolean variable associated to the
	/// given edge to false, with lifting depending on the parameters setting.
	fn get_bool_reason<Ctx>(&self, edge: usize, lb_fixed: bool) -> impl ReasonBuilder<Ctx>
	where
		Ctx: ReasoningContext,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let e = &self.edges[edge];
			let mut lb = self.get_cur_lower_bound(ctx, e.from);
			let mut ub = self.get_cur_upper_bound(ctx, e.to);
			if self.bool_reasons == 1 {
				if lb_fixed {
					ub = lb - e.val - 1;
				} else {
					lb = ub + e.val + 1;
				}
			}
			let reason = vec![
				self.int_vars[e.from].lit(ctx, IntLitMeaning::GreaterEq(lb)),
				self.int_vars[e.to].lit(ctx, IntLitMeaning::Less(ub + 1)),
			];
			reason
		}
	}

	/// Set the given boolean variable to false (or create a conflict if None)
	/// with a reason depending on the parameters setting (lazy or eager).
	fn set_bool_false<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		bool_var: Option<usize>,
		edge: usize,
		lb_fixed: bool,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		B: BoolSolverActions<E>,
		I: IntSolverActions<E>,
	{
		if self.bool_reasons == 0 {
			let data = if lb_fixed {
				edge as u64
			} else {
				-(edge as i64) as u64
			};
			if let Some(b) = bool_var {
				self.bool_vars[b].fix(ctx, false, ctx.deferred_reason(data))?;
			} else {
				return Err(ctx.declare_conflict(ctx.deferred_reason(data)));
			}
		} else if let Some(b) = bool_var {
			self.bool_vars[b].fix(ctx, false, self.get_bool_reason(edge, lb_fixed))?;
		} else {
			return Err(ctx.declare_conflict(self.get_bool_reason(edge, lb_fixed)));
		};
		Ok(())
	}

	/// Propagate new bounds.
	fn propagate_bounds<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		// Lower bound updates
		if !self.lower_bound_changes.is_empty() {
			self.inc_lb(ctx)?;
		}

		// Upper bound updates
		if !self.upper_bound_changes.is_empty() {
			self.inc_ub(ctx)?;
		}

		// Consequences of lower bound updates on open implied constraints
		let lb_changes = mem::take(&mut self.lower_bound_changes);
		for n in lb_changes {
			let lb = self.lower_bound[n].unwrap();

			for i in self.open_out[n].open_iter(ctx) {
				let &e = self.open_out[n].index(ctx, i);
				let edge = &self.edges[e];
				let target_ub = self.get_cur_upper_bound(ctx, edge.to);
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!(edge = ?edge, "constraint is falsified by bounds");
					// Lower bound is lifted
					self.set_bool_false(ctx, edge.bool_var, e, false)?;
					self.close_imp_edge(ctx, e);
				}
			}

			for i in self.open_in[n].open_iter(ctx) {
				let &e = self.open_in[n].index(ctx, i);
				let edge = &self.edges[e];
				if self.get_cur_upper_bound(ctx, edge.from) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!(edge = ?edge, "constraint is implied by bounds");
					self.close_imp_edge(ctx, e);
				}
			}
		}

		// Consequences of upper bound updates on open implied constraints
		let ub_changes = mem::take(&mut self.upper_bound_changes);
		for n in ub_changes {
			let ub = self.upper_bound[n].unwrap();

			for j in self.open_out[n].open_iter(ctx) {
				let &e = self.open_out[n].index(ctx, j);
				let edge = &self.edges[e];
				if ub - self.get_cur_lower_bound(ctx, edge.to) <= edge.val {
					// Constraint is implied by bounds.
					trace!(edge = ?edge, "constraint is implied by bounds");
					self.close_imp_edge(ctx, e);
				}
			}

			for j in self.open_in[n].open_iter(ctx) {
				let &e = self.open_in[n].index(ctx, j);
				let edge = &self.edges[e];
				let source_lb = self.get_cur_lower_bound(ctx, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!(edge = ?edge, "constraint is falsified by bounds");
					// Upper bound is lifted
					self.set_bool_false(ctx, edge.bool_var, e, true)?;
					self.close_imp_edge(ctx, e);
				}
			}
		}

		Ok(())
	}

	/// Propagate the addition of an edge, checking for conflicts and
	/// implications.
	fn propagate_edge_addition<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		e: usize,
		check_implied: bool,
		update_local_bounds: bool,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		// If the edge can't be added, a conflict will be generated
		let result = self.inc_sat(ctx, e)?;
		debug_assert!(result, "Adding {e} should be possible or cause a conflict!");
		if check_implied {
			// If the edge was added, check the status of open edges.
			self.inc_imp(ctx, e)?;
		}
		let source_lb = self.get_cur_lower_bound(ctx, self.edges[e].from);
		let lb_y = source_lb - self.edges[e].val;
		if lb_y > self.get_cur_lower_bound(ctx, self.edges[e].to) {
			// New edge caused lower bound change.
			self.set_int_lower_bound(
				ctx,
				self.edges[e].to,
				lb_y,
				self.edges[e].bool_var,
				self.edges[e].from,
				source_lb,
			)?;
			if update_local_bounds {
				self.notify_lb_change(ctx, self.edges[e].to);
				self.update_lb(self.edges[e].to, lb_y);
			}
		}
		let target_ub = self.get_cur_upper_bound(ctx, self.edges[e].to);
		let ub_x = target_ub + self.edges[e].val;
		if ub_x < self.get_cur_upper_bound(ctx, self.edges[e].from) {
			// New edge caused upper bound change.
			self.set_int_upper_bound(
				ctx,
				self.edges[e].from,
				ub_x,
				self.edges[e].bool_var,
				self.edges[e].to,
				target_ub,
			)?;
			if update_local_bounds {
				self.notify_ub_change(ctx, self.edges[e].from);
				self.update_ub(self.edges[e].from, ub_x);
			}
		}
		Ok(())
	}

	/// Propagate fixed booleans.
	fn propagate_booleans<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		check_implied: bool,
		update_local_bounds: bool,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
		B: BoolSolverActions<E>,
	{
		let fixed_bools = mem::take(&mut self.fixed_bools);
		for b in fixed_bools {
			let val = self.bool_vars[b].val(ctx).unwrap();
			trace!(b = ?b, val = ?val, "boolean fixed");
			if val {
				// Consequences of setting the boolean to true -> add all implied edges.
				for j in self.bool_implications[b].open_iter(ctx) {
					if let Some(&e) = self.bool_implications[b].index_opt(ctx, j) {
						trace!(edge = ?self.edges[e], "adding edge");
						self.close_imp_edge(ctx, e);
						self.activate_imp_edge(ctx, e);
						self.propagate_edge_addition(ctx, e, check_implied, update_local_bounds)?;
					}
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				for j in self.bool_implications[b].open_iter(ctx) {
					let &e = self.bool_implications[b].index(ctx, j);
					self.close_imp_edge(ctx, e);
				}
			}
		}

		Ok(())
	}

	/// Generate a dot presentation of the active graph.
	fn to_dot<E>(&self, ctx: &mut E::PropagationCtx<'_>, filter: Vec<bool>) -> String
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut out = "digraph {\n".to_owned();
		for n in (0..self.num_nodes()).filter(|&n| filter[n]) {
			out.push_str(
				format!(
					"\"{:?}\" [label=\"{:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
					n,
					n,
					self.get_cur_lower_bound(ctx, n),
					self.get_cur_upper_bound(ctx, n),
					self.pi[n]
				)
				.as_str(),
			);
			for &e in self.active_out[n].iter(ctx) {
				let edge = &self.edges[e];
				out.push_str(
					format!(
						"\"{:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n",
						n, edge.to, edge.val, edge.bool_var
					)
					.as_str(),
				);
			}
		}
		out += "}";
		out
	}
}

/*-------------------------------
- Propagators for solving phase -
--------------------------------*/

#[derive(Debug, Clone, PartialEq, Eq)]
/// Bounds consistent global difference constraint propagator.
pub struct DifferenceLogicBounds {
	/// Priority level for bounds propagation.
	priority_level: PriorityLevel,
	/// Shared reference to the difference logic graph.
	graph: Rc<RefCell<DifferenceLogicGraph<solver::View<IntVal>, solver::View<bool>>>>,
}

impl DifferenceLogicBounds {
	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		priority_level: PriorityLevel,
		graph: Rc<RefCell<DifferenceLogicGraph<solver::View<IntVal>, solver::View<bool>>>>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntSolverActions<Engine>,
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self {
			priority_level,
			graph: Rc::clone(&graph),
		}));
	}
}

impl<E> Propagator<E> for DifferenceLogicBounds
where
	E: ReasoningEngine,
	solver::View<IntVal>: IntSolverActions<E>,
	solver::View<bool>: BoolSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _ctx: &mut E::NotificationCtx<'_>) {
		trace!("Backtrack advise");
		self.graph.borrow_mut().reset_bounds();
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationCtx<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		let mut graph = self.graph.borrow_mut();
		let data = data as usize;
		let mut enqueue = false;
		if event == IntEvent::LowerBound || event == IntEvent::Fixed {
			enqueue = graph.notify_lb_change(ctx, data);
		}
		if event == IntEvent::UpperBound || event == IntEvent::Fixed {
			enqueue |= graph.notify_ub_change(ctx, data);
		}
		enqueue
	}

	fn explain(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		_lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let signed_data = data as i64;
		let graph = self.graph.borrow();
		let views = if signed_data < 0 {
			let edge = &graph.edges[-signed_data as usize];
			let target_ub = graph.int_vars[edge.to].max(ctx);
			let (lit_lb, IntLitMeaning::GreaterEq(meaning_lb)) = graph.int_vars[edge.from]
				.lit_relaxed(ctx, IntLitMeaning::GreaterEq(target_ub + edge.val + 1))
			else {
				unreachable!("IntLitMeaning should always be GreaterEq");
			};
			vec![
				lit_lb,
				graph.int_vars[edge.to]
					.lit_relaxed(
						ctx,
						IntLitMeaning::Less(max(target_ub + 1, meaning_lb - edge.val)),
					)
					.0,
			]
		} else {
			let edge = &self.graph.borrow().edges[signed_data as usize];
			let source_lb = graph.int_vars[edge.from].min(ctx);
			let (lit_ub, IntLitMeaning::Less(meaning_ub)) =
				graph.int_vars[edge.to].lit_relaxed(ctx, IntLitMeaning::Less(source_lb - edge.val))
			else {
				unreachable!("IntLitMeaning should always be Less");
			};
			vec![
				graph.int_vars[edge.from]
					.lit_relaxed(
						ctx,
						IntLitMeaning::GreaterEq(min(source_lb, meaning_ub + edge.val)),
					)
					.0,
				lit_ub,
			]
		};
		trace!(data = ?data, views = ?views, "lazy explanation");
		views
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(self.priority_level);
		for (i, n) in self.graph.borrow().int_vars.iter().enumerate() {
			n.advise_when(ctx, IntPropCond::Bounds, i as u64);
		}
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(name = "difference_logic_bounds", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.graph.borrow_mut().propagate_bounds(ctx)?;
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Difference constraint boolean propagator.
pub struct DifferenceLogicBooleans {
	/// Priority level for bounds propagation.
	priority_level: PriorityLevel,
	/// Shared reference to the difference logic graph.
	graph: Rc<RefCell<DifferenceLogicGraph<solver::View<IntVal>, solver::View<bool>>>>,
	/// Whether to proactively check implied constraints.
	use_inc_imp: bool,
}

impl DifferenceLogicBooleans {
	/// Create a new [`DifferenceLogicBooleans`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		priority_level: PriorityLevel,
		use_inc_imp: bool,
		graph: Rc<RefCell<DifferenceLogicGraph<solver::View<IntVal>, solver::View<bool>>>>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntSolverActions<Engine>,
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self {
			priority_level,
			graph: Rc::clone(&graph),
			use_inc_imp,
		}));
	}
}

impl<E> Propagator<E> for DifferenceLogicBooleans
where
	E: ReasoningEngine,
	solver::View<IntVal>: IntSolverActions<E>,
	solver::View<bool>: BoolSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _ctx: &mut E::NotificationCtx<'_>) {
		trace!("Backtrack advise");
		self.graph.borrow_mut().fixed_bools.clear();
	}

	fn advise_of_bool_change(&mut self, _ctx: &mut E::NotificationCtx<'_>, data: u64) -> bool {
		self.graph.borrow_mut().fixed_bools.insert(data as usize)
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(self.priority_level);
		for (i, b) in self.graph.borrow().bool_vars.iter().enumerate() {
			b.advise_when_fixed(ctx, i as u64);
		}
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(name = "difference_logic_booleans", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.graph
			.borrow_mut()
			.propagate_booleans(ctx, self.use_inc_imp, false)?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use itertools::Itertools;
	use pindakaas::{Lit as RawLit, Var as RawVar, solver::propagation::SolvingActions};
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::{
		IntVal, Model,
		actions::{
			BoolInspectionActions, IntInspectionActions, IntPropagationActions,
			IntSimplificationActions,
		},
		constraints::{
			BoolSolverActions, Constraint, IntSolverActions,
			difference_logic::{
				DiffEdge, DifferenceLogicCollection, DifferenceLogicConstraint,
				DifferenceLogicGraph, DifferenceLogicModel,
			},
		},
		lower::InitConfig,
		model,
		model::{ConRef, view::integer::IntView},
		solver,
		solver::{
			Solver,
			Value::Int,
			decision::integer::{EncodingType, IntDecision},
			engine::Engine,
			solving_context::SolvingContext,
		},
		views::LinearView,
	};

	const LEVEL: u8 = 3;
	const PRIO_BOUNDS: u8 = 2;
	const PRIO_BOOLS: u8 = 1;
	const USE_INC_IMP: bool = true;
	const BOOL_REASONS: u8 = 0;

	struct DummyActions;

	// Dummy implementation of [`SolvingActions`] to allow creating a
	// [`SolvingContext`]
	impl SolvingActions for DummyActions {
		fn is_decision(&mut self, _lit: RawLit) -> bool {
			panic!("not implemented")
		}

		fn new_observed_var(&mut self) -> RawVar {
			panic!("not implemented")
		}

		fn phase(&mut self, _lit: RawLit) {
			panic!("not implemented")
		}

		fn unphase(&mut self, _lit: RawLit) {
			panic!("not implemented")
		}
	}

	/// Get a fixed number of integer variables in the given range
	fn get_int_vars_range(
		slv: &mut Solver,
		num_vars: usize,
		from: IntVal,
		to: IntVal,
	) -> Vec<solver::View<IntVal>> {
		(0..num_vars)
			.map(|_| {
				IntDecision::new_in(
					slv,
					RangeList::from_iter([from..=to]),
					EncodingType::Eager,
					EncodingType::Eager,
				)
			})
			.collect_vec()
	}

	#[test]
	#[traced_test]
	fn test_relevant_dijkstra() {
		let mut prb = Model::default();
		let b = prb.new_bool_decision();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 10, 1, 10);
		let bool_vars = vec![map.get(&mut slv, b)];
		let mut graph = DifferenceLogicGraph::new(&mut slv, int_vars, bool_vars, BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		for (x, y, d) in vec![
			(0, 1, 1),
			(0, 2, 1),
			(0, 4, 1),
			(1, 4, 1),
			(1, 5, 1),
			(2, 4, 1),
			(3, 4, 1),
			(3, 5, 1),
			(4, 6, 1),
			(4, 8, 1),
			(5, 6, 1),
			(5, 7, 1),
			(5, 8, 1),
			(5, 9, 1),
			(7, 9, 1),
			(8, 9, 1),
		] {
			let _ = graph.new_edge(&mut ctx, DiffEdge::new(x, y, d, None));
		}
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(4, 5, 1, Some(0)));

		let outgoing_x = graph.dijkstra_relevant(&ctx, new_index, false);
		trace!("{:?}", outgoing_x);
		assert_eq!(outgoing_x.len(), 2);
		assert!(outgoing_x.contains_key(&5));
		assert!(outgoing_x.contains_key(&7));
		let incoming_y = graph.dijkstra_relevant(&ctx, new_index, true);
		trace!("{:?}", incoming_y);
		assert_eq!(incoming_y.len(), 2);
		assert!(incoming_y.contains_key(&2));
		assert!(incoming_y.contains_key(&4));
	}

	#[test]
	#[traced_test]
	fn test_inc_lb()
	where
		solver::View<IntVal>: IntSolverActions<Engine>,
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		let mut prb = Model::default();
		let (mut slv, _): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 5, 1, 10);
		let mut graph: DifferenceLogicGraph<_, solver::View<bool>> =
			DifferenceLogicGraph::new(&mut slv, int_vars, vec![], BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 3, 3, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 4, 1, None));
		assert!(graph.int_vars[0].tighten_min(&mut ctx, 8, []).is_ok());
		assert!(graph.inc_lb(&mut ctx).is_ok());
		assert_eq!(graph.int_vars[1].min(&ctx), 6);
		assert_eq!(graph.int_vars[2].min(&ctx), 5);
		assert_eq!(graph.int_vars[3].min(&ctx), 3);
		assert_eq!(graph.int_vars[4].min(&ctx), 4);
	}

	#[test]
	#[traced_test]
	fn test_inc_ub()
	where
		solver::View<IntVal>: IntSolverActions<Engine>,
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		let mut prb = Model::default();
		let (mut slv, _): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 5, 1, 10);
		let mut graph: DifferenceLogicGraph<_, solver::View<bool>> =
			DifferenceLogicGraph::new(&mut slv, int_vars, vec![], BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 3, 3, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 4, 1, None));
		assert!(graph.int_vars[4].tighten_max(&mut ctx, 3, []).is_ok());
		assert!(graph.inc_ub(&mut ctx).is_ok());
		assert_eq!(graph.int_vars[0].max(&ctx), 7);
		assert_eq!(graph.int_vars[1].max(&ctx), 5);
		assert_eq!(graph.int_vars[2].max(&ctx), 4);
	}

	#[test]
	#[traced_test]
	fn test_inc_sat()
	where
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		let mut prb = Model::default();
		let b = prb.new_bool_decision();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 3, 1, 10);
		let bool_var = map.get(&mut slv, b);
		let mut graph = DifferenceLogicGraph::new(&mut slv, int_vars, vec![bool_var], BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let second = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, -4, None));
		assert!(graph.inc_sat(&mut ctx, second).unwrap());
		let feasible = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, 3, None));
		assert!(graph.inc_sat(&mut ctx, feasible).unwrap());
		let impossible = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, 1, Some(0)));
		assert!(!graph.inc_sat(&mut ctx, impossible).unwrap());
		let conflict = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, 1, None));
		assert!(graph.inc_sat(&mut ctx, conflict).is_err());
	}

	#[test]
	#[traced_test]
	fn test_inc_imp()
	where
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		let mut prb = Model::default();
		let bools = (0..3).map(|_| prb.new_bool_decision()).collect_vec();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 3, 1, 10);
		let bool_vars = bools
			.into_iter()
			.map(|b| map.get(&mut slv, b))
			.collect_vec();
		let mut graph =
			DifferenceLogicGraph::new(&mut slv, int_vars, bool_vars.clone(), BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 1, 2, Some(2)));
		let _ = graph.inc_imp(&mut ctx, new_index);
		assert_eq!(
			ctx.state.propagation_queue.pop_front().unwrap().lit,
			RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap())
		);
		assert!(bool_vars[1].val(&ctx).is_none());
		assert!(bool_vars[2].val(&ctx).is_none());
		assert_eq!(graph.open_out[2].num_open(&ctx), 1);
		assert_eq!(graph.open_in[2].num_open(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_inc_imp2()
	where
		solver::View<bool>: BoolSolverActions<Engine>,
	{
		let mut prb = Model::default();
		let bools = (0..4).map(|_| prb.new_bool_decision()).collect_vec();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars = get_int_vars_range(&mut slv, 4, 1, 10);
		let bool_vars = bools
			.into_iter()
			.map(|b| map.get(&mut slv, b))
			.collect_vec();
		let mut graph =
			DifferenceLogicGraph::new(&mut slv, int_vars, bool_vars.clone(), BOOL_REASONS);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 3, 2, Some(3)));
		let _ = graph.inc_imp(&mut ctx, new_index);
		assert_eq!(
			ctx.state.propagation_queue.pop_front().unwrap().lit,
			RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap())
		);
		assert!(bool_vars[1].val(&ctx).is_none());
		assert!(bool_vars[2].val(&ctx).is_none());
		assert!(bool_vars[3].val(&ctx).is_none());
		assert_eq!(graph.open_out[0].num_open(&ctx), 2);
		assert_eq!(graph.open_in[0].num_open(&ctx), 0);
	}

	fn test_paper_simple(bool_reasons: u8) {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(3, RangeList::from_iter([1..=5]));
		let b = prb.new_bool_decision();
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			bool_reasons,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[1],
			int_vars[2],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[1],
			int_vars[2],
			4,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[0],
			int_vars[2],
			-2,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		let (iv, bv, gc, ic) = diff_logic_model.output_statistics(&prb);
		assert_eq!(iv, 3);
		assert_eq!(bv, 1);
		assert_eq!(gc, 2);
		assert_eq!(ic, 2);
		prb.post_constraint(diff_logic_model);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views = int_vars.iter().map(|&v| map.get(&mut slv, v)).collect_vec();
		let b_view = solver::View::from(map.get(&mut slv, b));
		slv.assert_num_solutions(
			&[int_views[0], int_views[1], int_views[2], b_view],
			41,
			move |sol| {
				let Int(x) = sol[0] else { return false };
				let Int(y) = sol[1] else { return false };
				let Int(z) = sol[2] else { return false };
				let Int(b) = sol[3] else { return false };
				trace!("Checking x = {x}, y = {y}, z = {z}, b = {b}");
				x - y <= -2 && y - z <= 3 && (b < 1 || y - z <= 4) && (b < 1 || x - z <= -2)
			},
		);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple_r0() {
		test_paper_simple(0);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple_r1() {
		test_paper_simple(1);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple_r2() {
		test_paper_simple(2);
	}

	#[test]
	#[traced_test]
	fn test_paper_medium() {
		let mut prb = Model::default();
		let int_vars5 = prb.new_int_decisions(4, RangeList::from_iter([1..=5]));
		let int_vars4 = prb.new_int_decisions(2, RangeList::from_iter([1..=4]));
		let b = prb.new_bool_decision();
		let c = prb.new_bool_decision();
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars5[0],
			int_vars5[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars5[1],
			int_vars5[2],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars5[2],
			int_vars4[0],
			-1,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars4[0],
			int_vars4[1],
			2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars5[0],
			int_vars5[3],
			1,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars5[3],
			int_vars5[2],
			-1,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars5[0],
			int_vars5[2],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars5[1],
			int_vars5[2],
			4,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			c,
			int_vars5[1],
			int_vars4[1],
			1,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			!c,
			int_vars4[1],
			int_vars5[1],
			-2,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		prb.post_constraint(diff_logic_model);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views5 = int_vars5
			.iter()
			.map(|&v| map.get(&mut slv, v))
			.collect_vec();
		let int_views4 = int_vars4
			.iter()
			.map(|&v| map.get(&mut slv, v))
			.collect_vec();
		let b_view = solver::View::from(map.get(&mut slv, b));
		let c_view = solver::View::from(map.get(&mut slv, c));
		slv.assert_num_solutions(
			&[
				int_views5[0],
				int_views5[1],
				int_views5[2],
				int_views4[0],
				int_views4[1],
				int_views5[3],
				b_view,
				c_view,
			],
			86,
			move |sol| {
				let Int(x) = sol[0] else { return false };
				let Int(y) = sol[1] else { return false };
				let Int(z) = sol[2] else { return false };
				let Int(u) = sol[3] else { return false };
				let Int(v) = sol[4] else { return false };
				let Int(t) = sol[5] else { return false };
				let Int(b) = sol[6] else { return false };
				let Int(c) = sol[7] else { return false };
				trace!(
					"Checking x = {x}, y = {y}, z = {z}, u = {u}, v = {v}, t = {t}, b = {b}, c = {c}"
				);
				x - y <= -2
					&& y - z <= 3 && z - u <= -1
					&& u - v <= 2 && x - t <= 1
					&& t - z <= -1 && (b < 1 || x - z <= -2)
					&& (b < 1 || y - z <= 4)
					&& (c < 1 || y - v <= 1)
					&& (c == 1 || y - v > 1)
			},
		);
	}

	#[test]
	#[traced_test]
	fn test_conflict() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[1],
			int_vars[2],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[2],
			int_vars[0],
			-2,
		));
		let mut diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(
			<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb)
				.is_err()
		);
	}

	#[test]
	#[traced_test]
	fn test_equal() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[1],
			int_vars[2],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[2],
			int_vars[0],
			-1,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		prb.post_constraint(diff_logic_model);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views = int_vars.iter().map(|&v| map.get(&mut slv, v)).collect_vec();
		slv.assert_num_solutions(&[int_views[0], int_views[1], int_views[2]], 7, move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}");
			x - y == 3 && y - z == -2 && z - x == -1
		});
	}

	#[test]
	#[traced_test]
	fn test_replacement() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(4, RangeList::from_iter([1..=5]));
		let b = prb.new_bool_decision();
		let c = prb.new_bool_decision();
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[2],
			int_vars[0],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[0],
			int_vars[2],
			2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[0],
			int_vars[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			c,
			int_vars[1],
			int_vars[0],
			2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			c,
			int_vars[2],
			int_vars[0],
			-1,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		prb.post_constraint(diff_logic_model);
		assert!(prb.propagate(ConRef::new(0)).is_ok());
		let IntView::Linear(view) = int_vars[3].0 else {
			unreachable!();
		};
		let var_index = view.var;
		assert!(
			int_vars[0]
				.unify(
					&mut prb,
					model::View::<IntVal>(IntView::Linear(LinearView::new(
						NonZero::new(2).unwrap(),
						1,
						var_index
					)))
				)
				.is_ok()
		);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views = int_vars.iter().map(|&v| map.get(&mut slv, v)).collect_vec();
		let b_view = solver::View::from(map.get(&mut slv, b));
		let c_view = solver::View::from(map.get(&mut slv, c));
		slv.assert_num_solutions(
			&[
				int_views[0],
				int_views[1],
				int_views[2],
				int_views[3],
				b_view,
				c_view,
			],
			14,
			move |sol| {
				let Int(x) = sol[0] else { return false };
				let Int(y) = sol[1] else { return false };
				let Int(z) = sol[2] else { return false };
				let Int(t) = sol[3] else { return false };
				let Int(b) = sol[4] else { return false };
				let Int(c) = sol[5] else { return false };
				trace!("Checking x = {x}, y = {y}, z = {z}, t = {t}, b = {b}, c = {c}");
				!(x - y > -2 || z - x > 3 || b >= 1 && x - z > 2 || c >= 1 && y - x > 2)
			},
		);
	}

	#[test]
	#[traced_test]
	fn test_unification() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(3, RangeList::from_iter([1..=5]));
		let b = prb.new_bool_decision();
		let c = prb.new_bool_decision();
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[2],
			int_vars[0],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[0],
			int_vars[2],
			2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			b,
			int_vars[0],
			int_vars[1],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			c,
			int_vars[1],
			int_vars[0],
			2,
		));
		diff_logic.add(DifferenceLogicConstraint::Implied(
			c,
			int_vars[2],
			int_vars[0],
			-1,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		prb.post_constraint(diff_logic_model);
		assert!(prb.propagate(ConRef::new(0)).is_ok());
		let IntView::Linear(view) = int_vars[2].0 else {
			unreachable!();
		};
		let var_index = view.var;
		assert!(
			int_vars[0]
				.unify(
					&mut prb,
					model::View::<IntVal>(IntView::Linear(LinearView::new(
						NonZero::new(1).unwrap(),
						1,
						var_index
					)))
				)
				.is_ok()
		);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views = int_vars.iter().map(|&v| map.get(&mut slv, v)).collect_vec();
		let b_view = solver::View::from(map.get(&mut slv, b));
		let c_view = solver::View::from(map.get(&mut slv, c));
		slv.assert_num_solutions(
			&[int_views[0], int_views[1], int_views[2], b_view, c_view],
			10,
			move |sol| {
				let Int(x) = sol[0] else { return false };
				let Int(y) = sol[1] else { return false };
				let Int(z) = sol[2] else { return false };
				let Int(b) = sol[3] else { return false };
				let Int(c) = sol[4] else { return false };
				trace!("Checking x = {x}, y = {y}, z = {z}, b = {b}, c = {c}");
				!(x - y > -2 || z - x > 3 || b >= 1 && x - z > 2 || c >= 1 && y - x > 2)
					&& (c < 1 || z - x <= -1)
					&& z + 1 == x
			},
		);
	}

	#[test]
	#[traced_test]
	fn test_constants() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_decisions(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(
			LEVEL,
			PRIO_BOUNDS,
			PRIO_BOOLS,
			USE_INC_IMP,
			BOOL_REASONS,
		);
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[0],
			int_vars[1],
			3,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[1],
			int_vars[2],
			-2,
		));
		diff_logic.add(DifferenceLogicConstraint::Global(
			int_vars[2],
			int_vars[0],
			5,
		));
		let diff_logic_model = diff_logic
			.process(&mut prb)
			.expect("Creating model failed")
			.expect("Model is empty");
		prb.post_constraint(diff_logic_model);
		assert!(prb.propagate(ConRef::new(0)).is_ok());
		assert!(int_vars[0].unify(&mut prb, model::View::from(5)).is_ok());
		assert!(int_vars[2].unify(&mut prb, model::View::from(5)).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_views = int_vars.iter().map(|&v| map.get(&mut slv, v)).collect_vec();
		slv.assert_num_solutions(&[int_views[0], int_views[1], int_views[2]], 2, move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}");
			x - y <= 3 && y - z <= -2 && x == 5 && z == 5
		});
	}
}
