//! Structure and algorithms for a global difference logic propagator.

use std::cell::RefCell;
use std::cmp::{max, min, Reverse};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::AddAssign;
use std::rc::Rc;
use itertools::Itertools;
use pindakaas::Lit as RawLit;
use pindakaas::propositional_logic::Formula;
use rustc_hash::FxBuildHasher;
use tracing::trace;
use crate::solver::activation_list::{IntEvent, IntPropCond};
use crate::solver::{BoolView, BoolViewInner, Goal, IntLitMeaning};
use crate::{actions::{ReformulationActions, SimplificationActions,
}, constraints::{Constraint, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, BoolFormula, Conjunction, IntDecision, IntVal, Model};
use crate::actions::{BoolInitActions, BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions, BrancherInitActions, ConstructionActions, DecisionActions, InitActions, IntDecisionActions, IntExplanationActions, IntInitActions, IntInspectionActions, IntSimplificationActions, PropagationActions, ReasoningEngine, TrailingActions};
use crate::branchers::{Brancher, Decision};
use crate::constraints::{BoxedPropagator, ModelBoolView, ModelIntView, ReasonBuilder, SolverBoolView, SolverIntView};
use crate::helpers::linear_transform::LinearTransform;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::TrailedOpenList;
use crate::reformulate::{BoolDecisionInner, IntDecisionIndex, IntDecisionInner};
use crate::solver::trail::TrailedInt;

// Redefine hash-based types using the fast FxBuildHasher.
/*#[derive(Copy, Clone, Default, Debug)]
/// Custom definition to derive Debug
pub struct FxBuildHasher;

impl BuildHasher for FxBuildHasher {
	type Hasher = FxHasher;
	fn build_hasher(&self) -> FxHasher {
		FxHasher::default()
	}
}*/

type HashSet<T> = std::collections::HashSet<T, FxBuildHasher>;
type IndexSet<T> = indexmap::IndexSet<T, FxBuildHasher>;
type IndexMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;
type PriorityQueue<I, P> = priority_queue::PriorityQueue<I, P, FxBuildHasher>;

/******************************************************
* Collection and processing of difference constraints *
******************************************************/

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Different types of (potential) difference logic constraints.
pub enum DifferenceLogicConstraint {
	/// A globally active difference constraint: x - y <= d
	Global(IntDecision, IntDecision, IntVal),
	/// An implied difference constraint: b -> x - y <= d
	Implied(BoolDecision, IntDecision, IntDecision, IntVal),
	/// A reified difference constraint: b <-> x - y <= d
	Reified(BoolDecision, IntDecision, IntDecision, IntVal),
	/// An implied equality constraint: b -> x - y == d (without implication is covered by views)
	ImpliedEquals(BoolDecision, IntDecision, IntDecision, IntVal),
	/// A not equals constraint: x - y != d
	NotEquals(IntDecision, IntDecision, IntVal),
	/// An implied not equals constraint: b -> x - y != d
	ImpliedNotEquals(BoolDecision, IntDecision, IntDecision, IntVal),
	/// A reified equality constraint: b <-> x - y == d
	ReifiedEquals(BoolDecision, IntDecision, IntDecision, IntVal),
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
	/// Which branching strategy to set for the propagator.
	branching: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Representation of set of raw difference constraints within a model.
pub struct DifferenceLogicCollection {
	/// User-defined parameters for difference logic.
	parameters: DifferenceLogicParameters,
	/// List of raw potential difference constraints.
	raw_constraints: Vec<DifferenceLogicConstraint>,
	/// Collection of boolean OR clauses for detecting conflicting edges.
	boolean_or: IndexSet<(BoolDecision, BoolDecision)>,
	/// Objective (if it exists)
	objective: Option<(IntDecision, Goal)>,
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

/// Transform an implied not equals constraint to implied difference constraints by introducing 2 new boolean decision variables.
fn add_implied_not_equals(model: &mut Model, imp_constraints: &mut Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>, b: BoolDecision, x: IntDecision, y: IntDecision, d: IntVal) {
	let decision1 = model.new_bool_var();
	let decision2 = model.new_bool_var();
	model.add_constraint(Formula::Or(vec![Formula::from(!b), Formula::from(decision1), Formula::from(decision2)]));
	model.add_constraint(Formula::Or(vec![Formula::from(!decision1), Formula::from(!decision2)]));
	imp_constraints.push((decision1, x, y, d - 1));
	imp_constraints.push((decision2, y, x, -d - 1));
}

impl DifferenceLogicCollection {
	
	pub(crate) fn new(priority_level_bounds: u8, priority_level_bools: u8, use_inc_imp: bool, branching: u8, objective: Option<(IntDecision, Goal)>) -> Self {
		Self {
			parameters: DifferenceLogicParameters {
				priority_level_bounds: parse_priority_level(priority_level_bounds),
				priority_level_bools: parse_priority_level(priority_level_bools),
				use_inc_imp,
				branching,
			},
			raw_constraints: Vec::new(),
			boolean_or: IndexSet::default(),
			objective,
		}
	}

	/// Add a raw difference constraint.
	pub(crate) fn add(&mut self, constraint: DifferenceLogicConstraint) {
		self.raw_constraints.push(constraint);
	}

	pub(crate) fn add_bool_or(&mut self, or1: BoolDecision, or2: BoolDecision) {
		// TODO deal with more complicated cases with more than 2 lits?
		let _ = self.boolean_or.insert((or1, or2));
		let _ = self.boolean_or.insert((or2, or1));
	}

	/// Process the raw difference constraints, transform them to global and implied difference
	/// constraints and / or reemit them as standalone constraints depending on the given level
	/// parameter (binary encoding).
	pub(crate) fn process(&mut self, model: &mut Model, level: u32) -> Result<Option<DifferenceLogicModel>, ReformulationError> {
		let mut global_constraints = Vec::new();
		let mut imp_constraints = Vec::new();
		for raw in self.raw_constraints.iter() {
			match raw {
				// Always post global, implied, and reified constraints TODO could check if they are isolated etc?
				DifferenceLogicConstraint::Global(x, y, d) => global_constraints.push((*x, *y, *d)),
				DifferenceLogicConstraint::Implied(b, x, y, d) => imp_constraints.push((*b, *x, *y, *d)),
				DifferenceLogicConstraint::Reified(b, x, y, d) => {
					imp_constraints.push((*b, *x, *y, *d));
					imp_constraints.push((!*b, *y, *x, -*d-1));
				},
				// b -> x - y == d is transformed to b -> x - y <= d and b -> x - y >= d.
				DifferenceLogicConstraint::ImpliedEquals(b, x, y, d) => {
					if level & 0b1 > 0 {
						imp_constraints.push((*b, *x, *y, *d));
						imp_constraints.push((*b, *y, *x, -*d));
					}
					if level & 0b1 == 0 || level & 0b10 > 0 {
						model.add_constraint((*x - *y).eq(*d).implied_by(*b));
					}
				},
				// x - y != d is transformed to b -> x - y < d and !b -> x - y > d for a new boolean variable b.
				DifferenceLogicConstraint::NotEquals(x, y, d) => {
					if level & 0b100 > 0 {
						let decision = model.new_bool_var();
						imp_constraints.push((decision, *x, *y, *d - 1));
						imp_constraints.push((!decision, *y, *x, -*d - 1));
					}
					if level & 0b100 == 0 || level & 0b1000 > 0 {
						model.add_constraint((*x - *y).ne(*d));
					}
				},
				// b -> x - y != d is transformed to b -> c \/ e; !c \/ !e; c -> x - y < d; e -> x - y > d for new boolean variables c and e.
				DifferenceLogicConstraint::ImpliedNotEquals(b, x, y, d) => {
					if level & 0b10_000 > 0 {
						add_implied_not_equals(model, &mut imp_constraints, *b, *x, *y, *d);
					}
					if level & 0b10_000 == 0 || level & 0b100_000 > 0 {
						model.add_constraint((*x - *y).ne(*d).implied_by(*b));
					}
				},
				// b <-> x - y == d is transformed to b -> x - y == d and !b -> x - y != d
				DifferenceLogicConstraint::ReifiedEquals(b, x, y, d) => {
					if level & 0b1000_000 > 0 {
						imp_constraints.push((*b, *x, *y, *d));
						imp_constraints.push((*b, *y, *x, -*d));
						add_implied_not_equals(model, &mut imp_constraints, !*b, *x, *y, *d);
					}
					if level & 0b1000_000 == 0 || level & 0b10_000_000 > 0 {
						model.add_constraint((*x - *y).eq(*d).reified_by(*b));
					}
				},
			}
		}
		if global_constraints.is_empty() && imp_constraints.is_empty() {
			return Ok(None);
		}
		Ok(Some(DifferenceLogicModel::new(model, self.parameters.clone(), global_constraints, imp_constraints, self.boolean_or.clone())?))
	}
	
}

/*********************************************************
* Model of difference logic for the simplification stage *
*********************************************************/

/// Check if the underlying variables are different, if not reemit the potentially implied difference constraint.
fn check_vars_different<A: SimplificationActions<Target=Model>>(actions: &mut A, x: IntDecision, y: IntDecision, d: IntVal, b: Option<BoolDecision>) -> bool {
	if x == y && d >= 0 {
		trace!("Removing redundant {b:?} implies {x:?} - {y:?} <= {d:?}");
		return false;
	}
	let x_var = get_int_var_index(x);
	let y_var = get_int_var_index(y);
	if x_var == y_var || x_var.is_none() || y_var.is_none() {
		trace!("Decisions implied by {b:?} {x:?} and {y:?} (<= {d:?}) have the same underlying variable or include a constant, reemitting");
		let mut reemit = (x - y).leq(d);
		if let Some(b) = b {
			reemit = reemit.implied_by(b);
		}
		actions.add_constraint(reemit);
		return false;
	}
	true
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// The actual underlying variable below all transformations.
enum VarIndex {
	/// An underlying integer decision variable.
	IntIndex(IntDecisionIndex),
	/// An underlying boolean.
	BoolIndex(RawLit),
}

/// Get the underlying variable for a boolean decision (None if constant).
fn get_bool_var_index(b: BoolDecision) -> Option<VarIndex> {
	match b.0 { 
		BoolDecisionInner::Lit(l) => Some(VarIndex::BoolIndex(l)),
		BoolDecisionInner::Const(_) => None,
		BoolDecisionInner::IntEq(i, _) => Some(VarIndex::IntIndex(i)),
		BoolDecisionInner::IntGreaterEq(i, _) => Some(VarIndex::IntIndex(i)),
		BoolDecisionInner::IntLess(i, _) => Some(VarIndex::IntIndex(i)),
		BoolDecisionInner::IntNotEq(i, _) => Some(VarIndex::IntIndex(i)),
	}
}

/// Get the underlying variable for an integer decision (None if constant).
fn get_int_var_index(x: IntDecision) -> Option<VarIndex> {
	match x.0 { 
		IntDecisionInner::Var(i) => Some(VarIndex::IntIndex(i)),
		IntDecisionInner::Const(_) => None,
		IntDecisionInner::Linear(_, i) => Some(VarIndex::IntIndex(i)),
		IntDecisionInner::Bool(_, b) => get_bool_var_index(b),
	}
}

/// Get a transformation of the integer decision that has an offset of 0.
fn update_transform(x: IntDecision) -> (IntDecision, IntVal) {
	match x.0 {
		IntDecisionInner::Linear(transform, i) => {
			if transform.scale.get() == 1 {
				(IntDecision(IntDecisionInner::Var(i)), transform.offset)
			} else {
				(IntDecision(IntDecisionInner::Linear(LinearTransform::scaled(transform.scale), i)), transform.offset)
			}
		},
		IntDecisionInner::Bool(transform, b) => 
			(IntDecision(IntDecisionInner::Bool(LinearTransform::scaled(transform.scale), b)), transform.offset),
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
	graph: DifferenceLogicGraph<IntDecision, BoolDecision>,
	/// Mapping of integer decision variables to their index.
	int_var_index: IndexSet<IntDecision>,
	/// Minimum distances in the global graph.
	distances: Vec<Vec<IntVal>>,
	/// Set of nodes reachable with a direct edge of minimum distance for each node.
	direct_edge: Vec<HashSet<usize>>,

}

impl DifferenceLogicModel {

	fn new(prb: &mut Model,
		   parameters: DifferenceLogicParameters,
		   global_constraints: Vec<(IntDecision, IntDecision, IntVal)>,
		   imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
		   boolean_or: IndexSet<(BoolDecision, BoolDecision)>) -> Result<Self, ReformulationError> {

		let mut int_var_index = IndexSet::default();
		let mut bool_var_index = IndexSet::default();
		let mut trimmed_constraints = Vec::new();
		let mut trimmed_imp_constraints = Vec::new();

		for (x, y, d) in global_constraints.into_iter() {
			if check_vars_different(prb, x, y, d, None) {
				let (x_trans, xd) = update_transform(x);
				let (y_trans, yd) = update_transform(y);
				trimmed_constraints.push((int_var_index.insert_full(x_trans).0,
										  int_var_index.insert_full(y_trans).0,
										  d - xd + yd));
			}
		}

		for (b, x, y, d) in imp_constraints.into_iter() {
			if check_vars_different(prb, x, y, d, Some(b)) {
				let (x_trans, xd) = update_transform(x);
				let (y_trans, yd) = update_transform(y);
				if let Some(val) = b.val(prb) {
					// Boolean is already fixed: Global constraint if true, skipped if false.
					trace!("Fixed boolean {b:?} ({val}) for {x:?} - {y:?} <= {d:?}");
					if val {
						trimmed_constraints.push((int_var_index.insert_full(x_trans).0,
												  int_var_index.insert_full(y_trans).0,
												  d - xd + yd));
					}
				} else {
					trimmed_imp_constraints.push((bool_var_index.insert_full(b).0,
												  int_var_index.insert_full(x_trans).0,
												  int_var_index.insert_full(y_trans).0,
												  d - xd + yd));
				}
			}
		}

		trace!("Creating DifferenceLogicGraph for {} int and {} bool vars, {} global and {} implied edges.", int_var_index.len(), bool_var_index.len(), trimmed_constraints.len(), trimmed_imp_constraints.len());
		let int_vars = int_var_index.iter().map(|&v| v).collect_vec();
		let num_int = int_vars.len();
		trace!("Original int vars:");
		for &v in int_vars.iter() {
			trace!("{v:?}: lb {:?}, ub: {:?}", v.lower_bound(prb), v.upper_bound(prb));
		}
		let bool_vars = bool_var_index.iter().map(|&v| v).collect_vec();
		let mut graph = DifferenceLogicGraph::new(prb, int_vars, bool_vars);

		// Add global constraints
		for (x, y, d) in trimmed_constraints.into_iter() {
			let _ = graph.new_edge(prb, DiffEdge::new(x, y, d, None));
		}

		let mut decision_bool_cache = vec![Vec::new(); num_int]; // TODO only used for collection information about boolean relations
		// Add implied constraints
		for (b, x, y, d) in trimmed_imp_constraints.into_iter() {
			let _ = graph.new_edge(prb, DiffEdge::new(x, y, d, Some(b)));
			for i in graph.open_in[x].open_iter(prb) {
				let e_xor = *graph.open_in[x].index(prb, i);
				let edge = &graph.edges[e_xor];
				if edge.from == y && edge.val + d < 0 && boolean_or.contains(&(graph.bool_vars[b], graph.bool_vars[edge.bool_var.unwrap()])) {
					trace!("Found pair of implied edges in XOR configuration between {x} and {y} (lengths {d}, {})", edge.val);
					graph.bool_vars[b].unify(prb, !graph.bool_vars[edge.bool_var.unwrap()])?;
					decision_bool_cache[x].push((d, b));
					decision_bool_cache[y].push((edge.val, edge.bool_var.unwrap()));
				}
			}
		}
		// TODO investigate to do this collection differently?
		for (i1, &b1) in graph.bool_vars.iter().enumerate() {
			if let Some(i2) = bool_var_index.get_index_of(&!b1) {
				for ei1 in graph.bool_implications[i1].open_iter(prb) {
					let &e1 = graph.bool_implications[i1].index(prb, ei1);
					for ei2 in graph.bool_implications[i2].open_iter(prb) {
						let &e2 = graph.bool_implications[i2].index(prb, ei2);
						if e1 < e2 {
							trace!("Found pair of implied edges (by boolean) in OR configuration ({e1}, {e2})");
							let edge1 = &graph.edges[e1];
							decision_bool_cache[edge1.from].push((edge1.val, i1));
							let edge2 = &graph.edges[e2];
							decision_bool_cache[edge2.from].push((edge2.val, i2));
						}
					}
				}
			}
		}
		for (n, v) in decision_bool_cache.into_iter().enumerate() {
			for (val, b) in v.into_iter().sorted() {
				graph.decision_bools[n].push((b, val));
			}
		}

		Ok(Self {
			parameters,
			initialized: false,
			graph,
			int_var_index,
			distances: vec![vec![IntVal::MAX; num_int]; num_int],
			direct_edge: vec![HashSet::default(); num_int],
		})

	}

	fn reduce_and_check<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> bool where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		IntDecision: ModelIntView<E>,
		BoolDecision: ModelBoolView<E>,
	{
		self.check_remove_fixed_nodes(ctx);
		self.check_remove_isolated_nodes(ctx);
		if self.graph.num_active_nodes == 0 {
			// If no nodes are left, there is nothing more to do
			trace!("No more nodes left, return subsumed");
			return false;
		}
		self.check_remove_isolated_booleans(ctx);
		trace!("Graph at the end of simplify: {}", self.graph.to_dot(ctx));
		true
	}

	/// Compute initial pi values by assuming an additional vertex with a 0-cost path to every other
	/// vertex and applying Bellman-Ford. Fail if a negative cycle is detected.
	fn bellman_ford_init_pi<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		IntDecision: ModelIntView<E>,
	{
		trace!("Calculating initial pi values.");
		let mut distance = vec![0; self.graph.num_nodes() + 1];
		//let mut predecessor = vec![self.nodes.len(); self.nodes.len() + 1];
		let mut changed = false;
		for _ in 0..self.graph.num_nodes() {  // TODO fail faster in case of negative cycle?
			changed = false;
			for n in 0..self.graph.num_nodes() {
				for &e in self.graph.active_out[n].iter(ctx) {
					let edge = &self.graph.edges[e];
					if distance[edge.from] + edge.val < distance[edge.to] {
						distance[edge.to] = distance[edge.from] + edge.val;
						//predecessor[edge.to] = edge.from;
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
					if distance[edge.from] + edge.val < distance[edge.to] {
						trace!("Found negative cycle!");
						return Err(ctx.declare_conflict([]));  // TODO output cycle (not needed at the moment)?
					}
				}
			}
		}
		for n in 0..self.graph.num_nodes() {
			self.graph.pi[n] = distance[n];
		}
		Ok(())
	}

	/// Use Johnson's algorithm to get all pairs of shortest paths. Remove edges not used in any
	/// shortest path, close implied edges if possible.
	fn johnson_full<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		IntDecision: ModelIntView<E>,
		BoolDecision: ModelBoolView<E>,
	{

		trace!("Starting Johnson's");
		let mut pred = vec![vec![usize::MAX; self.graph.num_nodes()]; self.graph.num_nodes()];
		let mut queue = PriorityQueue::default();

		for n in 0..self.graph.num_nodes() {
			if !self.graph.active[n] {
				continue;
			}
			self.graph.reset_visit();
			let _ = queue.push(n, Reverse(0));
			while !queue.is_empty() {
				let (s, Reverse(dist)) = queue.pop().unwrap();
				self.graph.visit(s);
				//trace!("dijkstra on current node {s:?} with dist {dist}");
				for &index in self.graph.active_out[s].iter(ctx) {
					let edge = &self.graph.edges[index];
					let new_dist = dist + edge.val + self.graph.pi[s] - self.graph.pi[edge.to];
					if !self.graph.visited[edge.to] {
						let prev = queue.push_increase(edge.to, Reverse(new_dist));
						if prev.map_or(true, |Reverse(old_dist)| new_dist < old_dist) {
							self.distances[n][edge.to] = new_dist - self.graph.pi[n] + self.graph.pi[edge.to];
							pred[n][edge.to] = s;
						}
						//trace!("dijkstra adding node {:?} with dist {new_dist}", target.var);
					} else if edge.to == n && new_dist < self.distances[n][n] {
						// Loop back to origin - store distance, but don't enqueue again
						self.distances[n][n] = new_dist;
						pred[n][n] = s;
					}
				}
			}
		}

		trace!("Distances:");
		for (i, row) in self.distances.iter().enumerate() {
			trace!("{i}: {:?}", row.iter().enumerate().filter(|(_, &val)| val < IntVal::MAX).collect_vec());
		}
		trace!("Checking impact on edges");
		for n in 0..self.graph.num_nodes() {
			if !self.graph.active[n] {
				continue;
			}
			let reached = self.direct_edge.get_mut(n).unwrap();
			let mut i = 0;
			while i < self.graph.active_out[n].len(ctx) {
				let &e = self.graph.active_out[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				if self.distances[n][edge.to] < edge.val || (self.distances[n][edge.to] == edge.val && reached.contains(&edge.to)) {
					trace!("Global edge {edge:?} is redundant, shortest path of length {} found", self.distances[n][edge.to]);
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
				if self.distances[n][edge.to] <= edge.val {
					trace!("Implied edge {edge:?} is redundant, shortest path of length {} found", self.distances[n][edge.to]);
					self.graph.close_imp_edge(ctx, e);
				}
			}

			for i in self.graph.open_in[n].open_iter(ctx) {
				let &e = self.graph.open_in[n].index(ctx, i);
				let edge = &self.graph.edges[e];
				if self.distances[n][edge.from] < -edge.val {
					trace!("Implied edge {edge:?} is falsified, opposite shortest path of length {} found", self.distances[n][edge.from]);
					self.graph.set_bool_false(ctx, edge.bool_var, e, false)?; // TODO is this correct?
					//adapter.actions.set_bool(!edge.bool_var.map_or(BoolDecision::from(true), |b| adapter.bool_vars[b]))?;  // TODO no reason recorded here (not needed at the moment)
					self.graph.close_imp_edge(ctx, e);
				}
			}
		}

		for n in (0..self.graph.num_nodes()).filter(|&n| self.graph.active[n]) {
			if self.distances[n][n] == 0 {// TODO count offset and always unify with start of loop to prevent long unification chains?
				trace!("Found cycle of length 0");
				let mut cur = n;
				loop {
					let prev = pred[n][cur];
					if prev == n {
						break;
					}
					trace!("Unifying {prev} and {cur} with offset {:?}", self.distances[prev][cur]);
					self.graph.int_vars[prev].unify(ctx, self.graph.int_vars[cur] + self.distances[prev][cur])?;
					cur = prev;
					self.distances[cur][cur] = IntVal::MAX;
				}
			}
		}

		Ok(())

	}

	/// Update the offset of a node, including the value of all edges.
	fn update_node_offset<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, n: usize, offset: IntVal) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		IntDecision: ModelIntView<E>,
		BoolDecision: ModelBoolView<E>,
	{

		trace!("Updating the offset of node {n} by {offset}");
		self.graph.pi[n] += offset;
		let mut i = 0;
		while i < self.graph.active_out[n].len(ctx) {
			let &e = self.graph.active_out[n].index(ctx, i);
			let to = self.graph.edges[e].to;
			if check_vars_different(ctx, self.graph.int_vars[n], self.graph.int_vars[to], self.graph.edges[e].val, None) {
				self.graph.edges.get_mut(e).unwrap().val -= offset;
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
			if check_vars_different(ctx, self.graph.int_vars[from], self.graph.int_vars[n], self.graph.edges[e].val, None) {
				self.graph.edges.get_mut(e).unwrap().val += offset;
				i += 1;
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(ctx, &e);
				let _ = self.graph.active_in[n].swap_remove(ctx, i);
			}
		}
		for i in self.graph.open_out[n].open_iter(ctx) {
			let &e = self.graph.open_out[n].index(ctx, i);
			if check_vars_different(ctx, self.graph.int_vars[n],
									self.graph.int_vars[self.graph.edges[e].to],
									self.graph.edges[e].val,
									self.graph.edges[e].bool_var.map(|b| self.graph.bool_vars[b])) {
				self.graph.edges.get_mut(e).unwrap().val -= offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		for i in self.graph.open_in[n].open_iter(ctx) {
			let &e = self.graph.open_in[n].index(ctx, i);
			if check_vars_different(ctx, self.graph.int_vars[self.graph.edges[e].from],
										 self.graph.int_vars[n],
										 self.graph.edges[e].val,
										 self.graph.edges[e].bool_var.map(|b| self.graph.bool_vars[b])) {
				self.graph.edges.get_mut(e).unwrap().val += offset;
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		Ok(())

	}

	/// Moves all edges from the old node to the new node, adapted by the given offset.
	fn unify_nodes<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, old: usize, new: usize, offset: IntVal) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		IntDecision: ModelIntView<E>,
		BoolDecision: ModelBoolView<E>,
	{

		trace!("Moving all edges from node {old} to node {new} with offset {offset}");
		let mut mod_edges = Vec::new();
		for i in 0..self.graph.active_out[old].len(ctx) {
			let &e = self.graph.active_out[old].index(ctx, i);
			let to = self.graph.edges[e].to;
			let val = self.graph.edges[e].val;
			if check_vars_different(ctx, self.graph.int_vars[new], self.graph.int_vars[to], val - offset, None) &&
				(self.distances[new][to] > val - offset || (self.distances[new][to] == val - offset && !self.direct_edge[new].contains(&to))) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.from = new;
				edge.val -= offset;
				self.graph.active_out[new].push(ctx, e);
				let _ = self.direct_edge.get_mut(new).unwrap().insert(edge.to);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_in[to].swap_remove_element(ctx, &e);
			}
		}
		for i in 0..self.graph.active_in[old].len(ctx) {
			let &e = self.graph.active_in[old].index(ctx, i);
			let from = self.graph.edges[e].from;
			let val = self.graph.edges[e].val;
			if check_vars_different(ctx, self.graph.int_vars[from], self.graph.int_vars[new], val + offset, None) &&
				(self.distances[from][new] > val + offset || (self.distances[from][new] == val + offset && !self.direct_edge[from].contains(&new))) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.to = new;
				edge.val += offset;
				self.graph.active_in[new].push(ctx, e);
				let _ = self.direct_edge.get_mut(from).unwrap().insert(new);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(ctx, &e);
			}
		}
		for i in self.graph.open_out[old].open_iter(ctx) {
			let &e = self.graph.open_out[old].index(ctx, i);
			if check_vars_different(ctx, self.graph.int_vars[new],
									self.graph.int_vars[self.graph.edges[e].to],
									self.graph.edges[e].val - offset,
									self.graph.edges[e].bool_var.map(|b| self.graph.bool_vars[b])) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.from = new;
				edge.val -= offset;
				edge.out_index = self.graph.open_out[new].len();
				self.graph.open_out[new].push(e);
			} else {
				self.graph.close_imp_edge(ctx, e);
			}

		}
		for i in self.graph.open_in[old].open_iter(ctx) {
			let &e = self.graph.open_in[old].index(ctx, i);
			if check_vars_different(ctx, self.graph.int_vars[self.graph.edges[e].from],
									self.graph.int_vars[new],
									self.graph.edges[e].val + offset,
									self.graph.edges[e].bool_var.map(|b| self.graph.bool_vars[b])) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.to = new;
				edge.val += offset;
				edge.in_index = self.graph.open_in[new].len();
				self.graph.open_in[new].push(e);
			} else {
				self.graph.close_imp_edge(ctx, e);
			}
		}
		// Check consequences of all modified active edges
		for e in mod_edges {
			self.graph.propagate_edge_addition(ctx, e, true, true)?;
		}
		Ok(())

	}

	// Add an implied bound to the model.
	fn add_implied_bound<A: SimplificationActions<Target = Model>>(&mut self, actions: &mut A, bool_var: usize, int_var: usize, lt: bool, value: IntVal) {
		let bound = if lt {
			Box::new(BoolFormula::Atom(self.graph.int_vars[int_var].leq(value)))
		} else {
			Box::new(BoolFormula::Atom(self.graph.int_vars[int_var].geq(value)))
		};
		actions.add_constraint(BoolFormula::Implies(
			Box::new(BoolFormula::Atom(self.graph.bool_vars[bool_var])),
			bound,
		))
	}

	/// Check if nodes with fixed domain exist, if yes remove them from the graph.
	fn check_remove_fixed_nodes<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) where
		E: ReasoningEngine,
		for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
		IntDecision: ModelIntView<E>,
		BoolDecision: ModelBoolView<E>,
	{

		for n in 0..self.graph.num_nodes() {
			if self.graph.active[n] {
				if let Some(val) = self.graph.int_vars[n].val(ctx) {
					trace!("Var {n} has a fixed value - removing from graph");
					for &e in self.graph.active_out[n].iter(ctx) {
						let edge = &self.graph.edges[e];
						trace!("Removing outgoing edge {edge:?}");
						let _ = self.graph.active_in[edge.to].swap_remove_element(ctx, &e);
					}
					for &e in self.graph.active_in[n].iter(ctx) {
						let edge = &self.graph.edges[e];
						trace!("Removing incoming edge {edge:?}");
						let _ = self.graph.active_out[edge.from].swap_remove_element(ctx, &e);
					}
					for i in self.graph.open_out[n].open_iter(ctx) {
						let &e = self.graph.open_out[n].index(ctx, i);
						let edge = &self.graph.edges[e];
						trace!("Reemitting implied outgoing edge {edge:?}");
						self.add_implied_bound(ctx, edge.bool_var.unwrap(), edge.to, false, val - edge.val);
						self.graph.close_imp_edge(ctx, e);
					}
					for i in self.graph.open_in[n].open_iter(ctx) {
						let &e = self.graph.open_in[n].index(ctx, i);
						let edge = &self.graph.edges[e];
						trace!("Reemitting implied incoming edge {edge:?}");
						self.add_implied_bound(ctx, edge.bool_var.unwrap(), edge.from, true, val + edge.val);
						self.graph.close_imp_edge(ctx, e);
					}
				}
			}
		}

	}

	/// Check if nodes with no edges exist, if yes remove them from the graph.
	fn check_remove_isolated_nodes<A: TrailingActions>(&mut self, actions: &mut A) {

		for n in 0..self.graph.num_nodes() {
			if self.graph.active[n] &&
				self.graph.active_out[n].len(actions) == 0 &&
				self.graph.active_in[n].len(actions) == 0 &&
				self.graph.open_out[n].num_open(actions) == 0 &&
				self.graph.open_in[n].num_open(actions) == 0 {
				trace!("Var {n} has no edges - removing from graph");
			}
		}

	}

	/// Check if isolated booleans exist, if yes mark them as inactive.
	fn check_remove_isolated_booleans<A: TrailingActions>(&mut self, actions: &mut A) {
		for b in 0..self.graph.bool_implications.len() {
			if self.graph.bool_active[b] && self.graph.bool_implications[b].num_open(actions) == 0 {
				trace!("Boolean {b} has no edges - removing from graph");
				self.graph.bool_active[b] = false;
			}
		}
	}

	/// Return statistics about the size of the graph.
	pub(crate) fn output_statistics<A: TrailingActions>(&self, actions: &mut A) -> (usize, usize, usize, usize) {
		(self.graph.int_vars.len(), 
		 self.graph.bool_vars.len(), 
		 (0..self.graph.num_nodes()).into_iter().map(|n| self.graph.active_out[n].len(actions)).sum(),
		 (0..self.graph.num_nodes()).into_iter().map(|n| self.graph.open_out[n].num_open(actions)).sum())
	}

}

impl<E> Constraint<E> for DifferenceLogicModel
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = Model>,
	IntDecision: ModelIntView<E>,
	BoolDecision: ModelBoolView<E>,
{

	#[tracing::instrument(name = "diff_logic_simplify", level = "trace", skip(self, ctx))]
	fn simplify(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<SimplificationStatus, E::Conflict> {

		if !self.initialized {

			trace!("Starting initial propagation with graph: {}", self.graph.to_dot(ctx));
			self.bellman_ford_init_pi(ctx)?;
			let mut initial_lb_changes = (0..self.graph.num_nodes()).into_iter().collect();
			let mut initial_ub_changes = (0..self.graph.num_nodes()).into_iter().collect();
			self.graph.propagate_bounds(ctx, &mut initial_lb_changes, &mut initial_ub_changes)?;
			let fixed_bools = (0..self.graph.bool_vars.len()).into_iter()
				.filter(|&b| self.graph.bool_vars[b].val(ctx).is_some() && self.graph.bool_active[b]).collect();  //TODO isn't bool active always true here?
			self.graph.propagate_booleans(ctx, &fixed_bools, false, true)?;
			// Already do removals before Johnson's to reduce complexity of the graph
			self.check_remove_fixed_nodes(ctx);
			self.check_remove_isolated_nodes(ctx);
			self.johnson_full(ctx)?;

		} else {

			for n in 0..self.graph.int_vars.len() {
				if self.graph.active[n] {
					let alias = self.graph.int_vars[n].alias(ctx);
					if self.graph.int_vars[n] != alias {
						trace!("Var alias is different (was {:?}, is {:?})", self.graph.int_vars[n], alias);
						let (v_trans, vd) = update_transform(alias);
						if let Some(new) = self.int_var_index.get_index_of(&v_trans) {
							self.unify_nodes(ctx, n, new, vd)?;
						} else if !matches!(alias.0, IntDecisionInner::Const(_)) {
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
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)

	}

	fn to_solver(&self, ctx: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		trace!("Transforming DifferenceLogicGraph to solver");
		trace!("Immediately before transformation:");
		for (i, &v) in self.graph.int_vars.iter().enumerate() {
			if self.graph.active[i] {
				trace!("{v:?}");
			}
		}
		let int_vars = self.graph.int_vars.iter().enumerate()
			.filter_map(|(i, &v)| if self.graph.active[i] { Some(ctx.solver_int(v)) } else { None })
			.collect_vec();
		trace!("Transformed int vars:");
		for &v in int_vars.iter() {
			trace!("{v:?}: lb {:?}, ub: {:?}", v.lower_bound(ctx), v.upper_bound(ctx));
		}
		let bool_vars = self.graph.bool_vars.iter().enumerate()
			.filter_map(|(i, &v)| if self.graph.bool_active[i] { Some(ctx.solver_bool(v)) } else { None })
			.collect_vec();
		let graph_cell = Rc::new(RefCell::new(DifferenceLogicGraph::from(&self.graph, ctx, int_vars, bool_vars)));
		DifferenceLogicBounds::post(ctx, self.parameters.priority_level_bounds, graph_cell.clone());
		DifferenceLogicBooleans::post(ctx, self.parameters.priority_level_bools, self.parameters.use_inc_imp, graph_cell.clone());
		/*if self.parameters.branching > 0 { TODO experimental branching stuff
			DiffLogicBrancher::new_in(slv, &int_vars, &bool_vars, graph_cell, self.objective.map_or(true, |(_, o)| o == Goal::Minimize));
		}*/
		Ok(())
	}
}

impl<E> Propagator<E> for DifferenceLogicModel
where
	E: ReasoningEngine,
	IntDecision: ModelIntView<E>,
	BoolDecision: ModelBoolView<E>,
{
	
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		for &x in self.graph.int_vars.iter() {
			x.enqueue_when(ctx, IntPropCond::Bounds);  // TODO check to change this to advisors!
		}
		for &b in self.graph.bool_vars.iter() {
			b.enqueue_when_fixed(ctx); // TODO check to change this to advisors!
		}
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {

		let mut lower_bound_changes = IndexSet::default();
		let mut upper_bound_changes = IndexSet::default();
		for n in 0..self.graph.int_vars.len() {
			if !self.graph.active[n] {
				continue;
			}
			if self.graph.lower_bound[n].map_or(true, |v| v != self.graph.int_vars[n].lower_bound(ctx)) {
				let _ = lower_bound_changes.insert(n);
			}
			if self.graph.upper_bound[n].map_or(true, |v| v != self.graph.int_vars[n].upper_bound(ctx)) {
				let _ = upper_bound_changes.insert(n);
			}
		}
		let mut fixed_bools = IndexSet::default();
		for b in 0..self.graph.bool_vars.len() {
			if self.graph.bool_active[b] && self.graph.bool_vars[b].val(ctx).is_some() {
				let _ = fixed_bools.insert(b);
			}
		}
		
		self.graph.propagate_bounds(ctx, &mut lower_bound_changes, &mut upper_bound_changes)?;
		self.graph.propagate_booleans(ctx, &fixed_bools, true, true)?;

		Ok(())
		
	}
	
}
	

/*************************************************************
* Common graph structure used for simplification and solving *
*************************************************************/

#[derive(Debug, Clone, PartialEq, Eq)]
/// An edge in the difference logic graph (bool_var -> from - to <= val).
pub struct DiffEdge {
	/// Source node index.
	from: usize,
	/// Target node index.
	to: usize,
	/// Difference value.
	val: IntVal,
	/// Index of the Boolean for the difference constraints (None for globally active constraints).
	bool_var: Option<usize>,
	/// Index of this edge in the list of edges implied by the boolean
	bool_index: usize,
	/// Index of this edge in the list of open outgoing edges
	out_index: usize,
	/// Index of this edge in the list of open incoming edges
	in_index: usize,
}

impl DiffEdge {

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
	/// Whether a node is active.
	active: Vec<bool>,
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
	/// Number of nodes that are active.
	num_active_nodes: usize,
	/// Number of open implication edges.
	num_open_edges: TrailedInt,
	/// List of all edges in the graph. todo could make this a trailed list for dynamic addition
	edges: Vec<DiffEdge>,
	/// Map from boolean indices to their implied edges.
	bool_implications: Vec<TrailedOpenList<usize>>,
	/// Whether a boolean is active.
	bool_active: Vec<bool>,
	/// Storage for the visited state.
	visited_updates: Vec<usize>,
	/// Current lower bound updates.
	lb_updates: Vec<usize>,
	/// Current upper bound updates.
	ub_updates: Vec<usize>,
	/// Ordered list of decision booleans for each node.
	decision_bools: Vec<TrailedOpenList<(usize, IntVal)>>,
}

/// Return a vector where each element is either None if the position in the input is False,
/// or the current count of the occurrences of True in the input.
/// E.g., [false, true, true, false, true] results in [None, Some(0), Some(1), None, Some(2)].
fn remap_vec(vec: &Vec<bool>) -> Vec<Option<usize>> {
	vec.iter().scan(0usize, |count, &a| {
		if a {
			*count += 1;
			Some(Some(*count - 1))
		} else {
			Some(None)
		}
	}).collect_vec()
}

impl<I, B> DifferenceLogicGraph<I, B> {

	fn new<E: ConstructionActions>(solver: &mut E, int_vars: Vec<I>, bool_vars: Vec<B>) -> Self {
		let num_int = int_vars.len();
		let num_bool = bool_vars.len();
		Self {
			int_vars,
			bool_vars,
			active: vec![true; num_int],
			active_out: (0..num_int).into_iter().map(|_| TrailedList::new(solver, true)).collect_vec(),
			active_in: (0..num_int).into_iter().map(|_| TrailedList::new(solver, true)).collect_vec(),
			open_out: (0..num_int).into_iter().map(|_| TrailedOpenList::new(solver)).collect_vec(),
			open_in: (0..num_int).into_iter().map(|_| TrailedOpenList::new(solver)).collect_vec(),
			lower_bound: vec![None; num_int],
			upper_bound: vec![None; num_int],
			pi: vec![0; num_int],
			backtrace: vec![None; num_int],
			visited: vec![false; num_int],
			num_active_nodes: num_int,
			num_open_edges: solver.new_trailed_int(0),
			edges: Vec::new(),
			bool_implications: (0..num_bool).into_iter().map(|_| TrailedOpenList::new(solver)).collect_vec(),
			bool_active: vec![true; num_bool],
			visited_updates: Vec::new(),
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			decision_bools: (0..num_int).into_iter().map(|_| TrailedOpenList::new(solver)).collect_vec(),
		}
	}

	fn from<A, I1, B1>(from: &DifferenceLogicGraph<I1, B1>, ctx: &mut A, int_vars: Vec<I>, bool_vars: Vec<B>) -> Self
	where
		A: ReformulationActions + ?Sized,
	{
		let num_int = int_vars.len();
		let num_bool = bool_vars.len();
		let node_map = remap_vec(&from.active);
		let bool_map = remap_vec(&from.bool_active);
		let edge_map = (0..from.edges.len()).into_iter().map(|i| Some(i)).collect_vec(); // TODO filter out useless edges!
		Self {
			int_vars,
			bool_vars,
			active: vec![true; num_int],
			active_out: (0..from.num_nodes()).into_iter()
				.map(|n| TrailedList::from_data(ctx, from.active_out[n].iter(ctx)
					.map(|&e| edge_map[e].unwrap())
					.collect_vec(), false))
				.collect_vec(),
			active_in: (0..from.num_nodes()).into_iter()
				.map(|n| TrailedList::from_data(ctx, from.active_in[n].iter(ctx)
					.map(|&e| edge_map[e].unwrap())
					.collect_vec(), false))
				.collect_vec(),
			open_out: (0..num_int).into_iter()
				.map(|n| TrailedOpenList::from_data(ctx, from.open_out[n].open_iter(ctx)
					.filter_map(|i| edge_map[*from.open_out[n].index(ctx, i)])
					.collect_vec()))
				.collect_vec(),
			open_in: (0..num_int).into_iter()
				.map(|n| TrailedOpenList::from_data(ctx, from.open_in[n].open_iter(ctx)
					.filter_map(|i| edge_map[*from.open_in[n].index(ctx, i)])
					.collect_vec()))
				.collect_vec(),
			lower_bound: vec![None; num_int],
			upper_bound: vec![None; num_int],
			pi: node_map.iter().filter_map(|o| o.map(|n| from.pi[n])).collect_vec(),
			backtrace: vec![None; num_int],
			visited: vec![false; num_int],
			num_active_nodes: num_int,
			num_open_edges: ctx.new_trailed_int(ctx.trailed_int(from.num_open_edges)),
			edges: edge_map.iter().filter_map(|o| o.map(|e| from.edges[e].clone())).collect_vec(),
			bool_implications: (0..num_bool).into_iter()
				.map(|b| TrailedOpenList::from_data(ctx, from.bool_implications[b].open_iter(ctx)
					.filter_map(|i| bool_map[*from.bool_implications[b].index(ctx, i)])
					.collect_vec()))
				.collect_vec(),
			bool_active: vec![true; num_bool],
			visited_updates: Vec::new(),
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			decision_bools: (0..num_int).into_iter().map(|_| TrailedOpenList::new(ctx)).collect(),  // TODO
		}
	}

	/// Return the total number of nodes.
	fn num_nodes(&self) -> usize {
		self.active.len()
	}

	/// Add a new edge to the graph, return the index. Depending on the boolean, the edge is added 
	/// globally (boolean is None) or as an implied edge.
	fn new_edge<T: TrailingActions>(&mut self, actions: &mut T, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		if let Some(b) = edge.bool_var {
			edge.bool_index = self.bool_implications[b].len();
			self.bool_implications[b].push(index);
			edge.out_index = self.open_out[edge.from].len();
			self.open_out[edge.from].push(index);
			edge.in_index = self.open_in[edge.to].len();
			self.open_in[edge.to].push(index);
			let _ = actions.set_trailed_int(self.num_open_edges, actions.trailed_int(self.num_open_edges) + 1);
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
		let was_open = self.bool_implications[b].close(actions, bool_index, |&e, i| self.edges[e].bool_index = i) &
			self.open_out[from].close(actions, out_index, |&e, i| self.edges[e].out_index = i) &
			self.open_in[to].close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert!(was_open);
		let _ = actions.set_trailed_int(self.num_open_edges, actions.trailed_int(self.num_open_edges) - 1);
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

	/// Get the current lower bound for the node, either stored or from the search.
	fn get_cur_lower_bound<Ctx>(&self, ctx: &mut Ctx, n: usize) -> IntVal
	where
		I: IntInspectionActions<Ctx>,
	{
		match self.lower_bound[n] {
			Some(lb) => lb,
			None => self.int_vars[n].lower_bound(ctx),
		}
	}

	/// Update the stored lower bound for the node.
	fn update_lb(&mut self, n: usize, val: IntVal) {
		if self.lower_bound[n].is_none() {
			self.lb_updates.push(n);
		}
		self.lower_bound[n] = Some(val);
	}

	/// Get the current upper bound for the node, either stored or from the search.
	fn get_cur_upper_bound<Ctx>(&self, ctx: &mut Ctx, n: usize) -> IntVal
	where
		I: IntInspectionActions<Ctx>,
	{
		match self.upper_bound[n] {
			Some(ub) => ub,
			None => self.int_vars[n].upper_bound(ctx),
		}
	}

	/// Update the stored upper bound for the node.
	fn update_ub(&mut self, n: usize, val: IntVal) {
		if self.upper_bound[n].is_none() {
			self.ub_updates.push(n);
		}
		self.upper_bound[n] = Some(val);
	}

	/// Get the reason for a cycle of negative lengths (all booleans along the cycle).
	fn get_cycle_reason<Ctx>(&self, node: usize) -> impl ReasonBuilder<Ctx, B::Atom> + '_ where
		B: BoolPropagationActions<Ctx>,
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

	/// Check incremental addition of the edge given by index to the active graph.
	/// Returns true if addition is possible. Otherwise, false is returned for implied edges, and a
	/// conflict is caused by global edges.
	fn inc_sat<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, new_index: usize) -> Result<bool, E::Conflict> where
		E: ReasoningEngine,
		B: SolverBoolView<E>,
	{ // TODO unit tests

		let new_edge = &self.edges[new_index];
		trace!("Performing inc_sat on i{:?} - i{:?} <= {:?}", new_edge.from, new_edge.to, new_edge.val);
		let mut queue = PriorityQueue::default();
		let mut pi_new = IndexMap::default(); // todo Could be replaced by the visited state. Q1: Is state or map faster? Q2: Is keeping old pi in case of conflict better?
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
						if old.map_or(true, |Reverse(old_gamma)| gamma_t < old_gamma) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		// If the origin is in the queue, we have a cycle of negative length.
		if queue.get_priority(&new_edge.from).is_some() {
			trace!("Found cycle with negative length for b{:?}", new_edge.bool_var);
			if let Some(b) = new_edge.bool_var {
				self.bool_vars[b].set_val(ctx, false, self.get_cycle_reason(new_edge.from))?;
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

	/// Perform dijkstra from the given node to all relevant nodes in the graph, return a map of
	/// distances. Can be performed in forward or backward direction.
	fn dijkstra_relevant<A: TrailingActions>(&mut self, actions: &mut A, new_edge: usize, reverse: bool) -> IndexMap<usize, IntVal> {
		
		trace!("Starting relevant dijkstra for e{new_edge:?} in mode reverse={reverse}");
		self.reset_visit();
		let new_edge = &self.edges[new_edge];
		let origin = if reverse {new_edge.to} else {new_edge.from};
		let relevant_target = if reverse {new_edge.from} else {new_edge.to};
		let mut distances = IndexMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = PriorityQueue::default();
		let _ = queue.push(origin, Reverse((0, false)));
		let _ = queue.push(relevant_target, Reverse((new_edge.val + if reverse { self.pi[relevant_target] - self.pi[origin] } else { self.pi[origin] - self.pi[relevant_target] }, true)));
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse((dist, relevant))) = queue.pop().unwrap();
			self.visit(s);
			//trace!("dijkstra on current node {s:?} with dist {dist} and relevancy {relevant}");
			for &e in if reverse {self.active_in[s].iter(actions)} else {self.active_out[s].iter(actions)} {
				let edge = &self.edges[e];
				let target = if reverse {edge.from} else {edge.to};
				let new_dist = dist + edge.val + if reverse {self.pi[target] - self.pi[s]} else {self.pi[s] - self.pi[target]};
				if !self.visited[target] {
					// Cases where we want to propagate the relevancy of s to t (equals lexicographic order of (new_dist, relevant)):
					// - Path to t with lower distance than before
					// - Path to t with same distance as before and s is not relevant (prefer irrelevancy in ties)
					let new_relevant = relevant || (s == origin && target == relevant_target);
					let new_prio = Reverse((new_dist, new_relevant));
					let prev = queue.push_increase(target, new_prio);
					if prev.map_or(true, |old_prio| old_prio != new_prio) {
						if new_relevant {
							// A new shortest distance has been found, add new distance to the map, if key was not present before increase relevant count.
							//trace!("Target {target:?} set to relevant");
							if distances.insert(target, new_dist + if reverse { self.pi[origin] - self.pi[target] } else { self.pi[target] - self.pi[origin] }).is_none() {
								relevant_count += 1;
							}
						} else {
							// Remove old distance from the map, if key was present before decrease relevant count.
							//trace!("Target {target:?} set to irrelevant");
							if distances.swap_remove(&target).is_some() {
								relevant_count -= 1;
							}
						}
					}
					//trace!("dijkstra adding node {:?} with dist {new_dist} and relevancy {relevant}", target);
				}
			}
			if relevant {
				relevant_count -= 1;
			}
		}
		distances

	}

	/// Check if the new edge given by the index implies or falsifies any of the open edges.
	fn inc_imp<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, new_index: usize) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		B: SolverBoolView<E>,
	{
		
		if ctx.trailed_int(self.num_open_edges) == 0 {
			trace!("No open implications");
			return Ok(());
		}

		// Incoming paths to relevant nodes starting from u via uv.
		let incoming_u = self.dijkstra_relevant(ctx, new_index, false); // todo could store distances at nodes as well?
		trace!("incoming_u is {incoming_u:?}");
		// Outgoing paths from relevant nodes ending at v via uv.
		let outgoing_v = self.dijkstra_relevant(ctx, new_index, true);
		trace!("outgoing_v is {outgoing_v:?}"); // todo check how to include pi change check at this point?
		let indegree_u: usize = incoming_u.iter().map(|(&n, _)| self.open_in[n].num_open(ctx)).sum();
		let outdegree_v: usize = outgoing_v.iter().map(|(&n, _)| self.open_out[n].num_open(ctx)).sum();
		trace!("indegree: {indegree_u:?}, outdegree: {outdegree_v:?}");
		
		let new_edge_val = self.edges[new_index].val;
		
		if indegree_u < outdegree_v {
			for &n in incoming_u.keys() {
				for i in self.open_in[n].open_iter(ctx) {
					let &e = self.open_in[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, implied)");
					if outgoing_v.contains_key(&edge.from) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint {edge:?} is implied");
						self.close_imp_edge(ctx, e);
					}
				}
				for i in self.open_out[n].open_iter(ctx) {
					let &e = self.open_out[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, reverse)");
					if outgoing_v.contains_key(&edge.to) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 {
						trace!("Constraint {edge:?} is falsified since inverse is implied");
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;  // TODO could also try these ones lazy? Or keep track of path in dijkstra relevant?
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
					if incoming_u.contains_key(&edge.to) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint {:?} is implied", edge);
						self.close_imp_edge(ctx, e);
					}
				}
				for i in self.open_in[n].open_iter(ctx) {
					let &e = self.open_in[n].index(ctx, i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, reverse)");
					if incoming_u.contains_key(&edge.from) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 {
						trace!("Constraint {:?} is falsified since inverse is implied", edge);
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		}

		Ok(())
	}

	fn set_int_lower_bound<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, n: usize, value: IntVal, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{
		self.int_vars[n].set_lower_bound(ctx, value, |ctx: &mut E::PropagationCtx<'_>| {
			let mut reason = vec![self.int_vars[lb_var].lit(ctx, IntLitMeaning::GreaterEq(lb_val))];
			if let Some(b) = bool_var {
				reason.push(self.bool_vars[b].clone().into());
			}
			reason
		})?;
		Ok(())
	}

	fn set_int_upper_bound<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, n: usize, value: IntVal, bool_var: Option<usize>, ub_var: usize, ub_val: IntVal) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{
		self.int_vars[n].set_upper_bound(ctx, value,|ctx: &mut E::PropagationCtx<'_>| {
			let mut reason = vec![self.int_vars[ub_var].lit(ctx, IntLitMeaning::Less(ub_val + 1))];
			if let Some(b) = bool_var {
				reason.push(self.bool_vars[b].clone().into());
			}
			reason
		})?;
		Ok(())
	}

	/// Perform incremental updates of lower bounds.
	fn inc_lb<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, v_l: &mut IndexSet<usize>) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{  // TODO unit tests

		trace!("Running inc_lb on int vars {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|&n| {
			self.int_vars[n].lower_bound(ctx) + self.pi[n]
		}).max().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_l.iter() {
			let _ = queue.push(n, Reverse(pi0 - self.int_vars[n].lower_bound(ctx) - self.pi[n])); // TODO prevent 2. call to lower bound? and 3. call later?
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			if bound > self.get_cur_lower_bound(ctx, s) || v_l.contains(&s) {
				self.update_lb(s, bound);
				if bound > self.int_vars[s].lower_bound(ctx) {
					trace!("Updating lower bound for i{:?} to {bound}", s);
					let (prev, b) = self.backtrace[s].unwrap();
					let lb = self.get_cur_lower_bound(ctx, prev);
					self.set_int_lower_bound(ctx, s, bound, b, prev, lb)?;
					let _ = v_l.insert(s);
				}
				for &e in self.active_out[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.to] {
						let path = gamma_s + self.pi[s] + edge.val - self.pi[edge.to];
						let old = queue.push_increase(edge.to, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Perform incremental updates of upper bounds.
	fn inc_ub<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, v_u: &mut IndexSet<usize>) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{  // TODO unit tests

		trace!("Running inc_ub on int vars {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|&n| {
			self.int_vars[n].upper_bound(ctx) + self.pi[n]
		}).min().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_u.iter() {
			let _ = queue.push(n, Reverse(self.pi[n] + self.int_vars[n].upper_bound(ctx) - pi0));  // TODO prevent 2. call to lower bound? and 3. call later?
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			if bound < self.get_cur_upper_bound(ctx, s) || v_u.contains(&s) {
				self.update_ub(s, bound);
				if bound < self.int_vars[s].upper_bound(ctx) {
					trace!("Updating upper bound for i{:?} to {bound}", s);
					let (prev, b) = self.backtrace[s].unwrap();
					let ub = self.get_cur_upper_bound(ctx, prev);
					self.set_int_upper_bound(ctx, s, bound, b, prev, ub)?;
					let _ = v_u.insert(s);
				}
				for &e in self.active_in[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.from] {
						let path = gamma_s + self.pi[edge.from] + edge.val - self.pi[s];
						let old = queue.push_increase(edge.from, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							self.backtrace[edge.from] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	fn reset_bounds(&mut self) {
		for &n in self.lb_updates.iter() {
			self.lower_bound[n] = None;
		}
		for &n in self.ub_updates.iter() {
			self.upper_bound[n] = None;
		}
		self.lb_updates.clear();
		self.ub_updates.clear();
	}

	/// Set the given boolean variable to false (or create a conflict if None) with a lazy reason
	/// that encodes the given edge and lb_fixed boolean.
	fn set_bool_false<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, bool_var: Option<usize>, edge: usize, lb_fixed: bool) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		B: SolverBoolView<E>,
	{
		let data = if lb_fixed {
			edge as u64
		} else {
			-(edge as i64) as u64
		};
		if let Some(b) = bool_var {
			self.bool_vars[b].set_val(ctx, false, ctx.deferred_reason(data))?;
		} else {
			return Err(ctx.declare_conflict(ctx.deferred_reason(data)));
		}
		Ok(())
	}

	/// Propagate new bounds.
	fn propagate_bounds<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, lower_bound_changes: &mut IndexSet<usize>, upper_bound_changes: &mut IndexSet<usize>) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{
		
		trace!("Propagating bounds on lb changes {:?}, ub changes {:?}.", lower_bound_changes, upper_bound_changes);

		// Lower bound updates
		if !lower_bound_changes.is_empty() {
			self.inc_lb(ctx, lower_bound_changes)?;
		}

		// Upper bound updates
		if !upper_bound_changes.is_empty() {
			self.inc_ub(ctx, upper_bound_changes)?;
		}

		// Consequences of lower bound updates on open implied constraints
		for &n in lower_bound_changes.iter() {
			let lb = self.lower_bound[n].unwrap();

			for i in self.open_out[n].open_iter(ctx) {
				let &e = self.open_out[n].index(ctx, i);
				let edge = &self.edges[e];
				let target_ub = self.get_cur_upper_bound(ctx, edge.to);
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} is falsified by bounds.", edge);
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
					trace!("Constraint {:?} is implied by bounds.", edge);
					self.close_imp_edge(ctx, e);
				}
			}
		}

		// Consequences of upper bound updates on open implied constraints
		for &n in upper_bound_changes.iter() {
			let ub = self.upper_bound[n].unwrap();

			for i in self.open_out[n].open_iter(ctx) {
				let &e = self.open_out[n].index(ctx, i);
				let edge = &self.edges[e];
				if ub - self.get_cur_lower_bound(ctx, edge.to) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} is implied by bounds.", edge);
					self.close_imp_edge(ctx, e);
				}
			}

			for i in self.open_in[n].open_iter(ctx) {
				let &e = self.open_in[n].index(ctx, i);
				let edge = &self.edges[e];
				let source_lb = self.get_cur_lower_bound(ctx, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} is falsified by bounds.", edge);
					// Upper bound is lifted
					self.set_bool_false(ctx, edge.bool_var, e, true)?;
					self.close_imp_edge(ctx, e);
				}
			}
		}

		Ok(())
		
	}

	/// Propagate the addition of an edge, checking for conflicts and implications.
	fn propagate_edge_addition<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, e: usize, check_implied: bool, update_local_bounds: bool) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
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
			self.set_int_lower_bound(ctx, self.edges[e].to, lb_y, self.edges[e].bool_var, self.edges[e].from, source_lb)?;
            if update_local_bounds {
                self.update_lb(self.edges[e].to, lb_y);
            }
		}
		let target_ub = self.get_cur_upper_bound(ctx, self.edges[e].to);
		let ub_x = target_ub + self.edges[e].val;
		if ub_x < self.get_cur_upper_bound(ctx, self.edges[e].from) {
			// New edge caused upper bound change.
			self.set_int_upper_bound(ctx, self.edges[e].from, ub_x, self.edges[e].bool_var, self.edges[e].to, target_ub)?;
            if update_local_bounds {
                self.update_ub(self.edges[e].from, ub_x);
            }
		}
		Ok(())
	}

	/// Propagate fixed booleans.
	fn propagate_booleans<E>(&mut self, ctx: &mut E::PropagationCtx<'_>, fixed_bools: &IndexSet<usize>, check_implied: bool, update_local_bounds: bool) -> Result<(), E::Conflict> where
		E: ReasoningEngine,
		I: SolverIntView<E>,
		B: SolverBoolView<E>,
	{
		
		trace!("Propagating fixed booleans {:?}.", fixed_bools);
		for &b in fixed_bools.iter() {
			let val = self.bool_vars[b].val(ctx).unwrap();
			trace!("Boolean b{b:?} fixed to {val}");
			if val {
				//trace!("Graph before adding edges: {}", self.to_dot(adapter));
				// Consequences of setting the boolean to true -> add all implied edges.
				if self.bool_active[b] {
					for i in self.bool_implications[b].open_iter(ctx) {
						if let Some(&e) = self.bool_implications[b].index_opt(ctx, i) {
							trace!("Processing adding edge {:?}", self.edges[e]);
							self.close_imp_edge(ctx, e);
							self.activate_imp_edge(ctx, e);
							self.propagate_edge_addition(ctx, e, check_implied, update_local_bounds)?;
						}
					}
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				if self.bool_active[b] {
					for i in self.bool_implications[b].open_iter(ctx) {
						let &e = self.bool_implications[b].index(ctx, i);
						trace!("Closing edge {:?})", self.edges[e]);
						self.close_imp_edge(ctx, e);
					}
				}
			}
		}

		Ok(())

	}
	
	/// Generate a dot presentation of the active graph.
	fn to_dot<E>(&self, ctx: &mut E::PropagationCtx<'_>) -> String where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let mut out = "digraph {\n".to_owned();
		for n in (0..self.num_nodes()).filter(|&n| self.active[n]) {
			out.push_str(format!("\"{:?}\" [label=\"{:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 n,
								 n,
								 self.get_cur_lower_bound(ctx, n),
								 self.get_cur_upper_bound(ctx, n),
								 self.pi[n]).as_str());
			for &e in self.active_out[n].iter(ctx) {
				let edge = &self.edges[e];
				out.push_str(format!("\"{:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n", n, edge.to, edge.val, edge.bool_var).as_str());
			}
		}
		out += "}";
		out
	}

}

/********************************
* Propagators for solving phase *
********************************/

#[derive(Debug, Clone, PartialEq, Eq)]
/// Bounds consistent global difference constraint propagator.
pub struct DifferenceLogicBounds {
	/// Priority level for bounds propagation.
	priority_level: PriorityLevel,
	/// Shared reference to the difference logic graph.
	graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>,
	/// List of integer variable indices with reported lower bound changes.
	lower_bound_changes: IndexSet<usize>,
	/// List of integer variable indices with reported upper bound changes.
	upper_bound_changes: IndexSet<usize>,
}

impl DifferenceLogicBounds {

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E,
				   priority_level: PriorityLevel,
				   graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>) where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self {
			priority_level,
			graph: graph.clone(),
			lower_bound_changes: IndexSet::default(),
			upper_bound_changes: IndexSet::default(),
		});
	}

}

impl<E> Propagator<E> for DifferenceLogicBounds
where
	E: ReasoningEngine,
	IntView: SolverIntView<E>,
	BoolView: SolverBoolView<E>,
{
	fn advise_of_backtrack(&mut self, _ctx: &mut E::NotificationCtx<'_>) {
		trace!("Backtrack advise");
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		self.graph.borrow_mut().reset_bounds();
	}

	fn advise_of_int_change(&mut self, ctx: &mut E::NotificationCtx<'_>, data: u64, event: IntEvent) -> bool {
		let graph = self.graph.borrow_mut();
		let data = data as usize;
		let mut enqueue = false;
		if event == IntEvent::LowerBound || event == IntEvent::Fixed {
			if graph.lower_bound[data].map_or(true, |e| e < graph.int_vars[data].lower_bound(ctx)) {
				trace!("Integer i{data} lower bound change.");
				enqueue = self.lower_bound_changes.insert(data);
			}
		}
		if event == IntEvent::UpperBound || event == IntEvent::Fixed {
			if graph.upper_bound[data].map_or(true, |e| e > graph.int_vars[data].upper_bound(ctx)) {
				trace!("Integer i{data} upper bound change.");
				enqueue |= self.upper_bound_changes.insert(data);
			}
		}
		enqueue
	}

	fn explain(&mut self, ctx: &mut E::ExplanationCtx<'_>, _lit: E::Atom, data: u64) -> Conjunction<E::Atom> {
		let signed_data = data as i64;
		let graph = self.graph.borrow();
		let views = if signed_data < 0 {
			let edge = &graph.edges[-signed_data as usize];
			let target_ub = graph.int_vars[edge.to].upper_bound(ctx);
			let (lit_lb, IntLitMeaning::GreaterEq(meaning_lb)) = graph.int_vars[edge.from].lit_relaxed(ctx, IntLitMeaning::GreaterEq(target_ub + edge.val + 1)) else {
				unreachable!("IntLitMeaning should always be GreaterEq");
			};
			vec![lit_lb, graph.int_vars[edge.to].lit_relaxed(ctx, IntLitMeaning::Less(max(target_ub + 1, meaning_lb - edge.val))).0]
		} else {
			let edge = &self.graph.borrow().edges[signed_data as usize];
			let source_lb = graph.int_vars[edge.from].lower_bound(ctx);
			let (lit_ub, IntLitMeaning::Less(meaning_ub)) = graph.int_vars[edge.to].lit_relaxed(ctx, IntLitMeaning::Less(source_lb - edge.val)) else {
				unreachable!("IntLitMeaning should always be Less");
			};
			vec![graph.int_vars[edge.from].lit_relaxed(ctx, IntLitMeaning::GreaterEq(min(source_lb, meaning_ub + edge.val))).0, lit_ub]
		};
		trace!("Explaining {data} with {views:?}");
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
		self.graph.borrow_mut().propagate_bounds(ctx, &mut self.lower_bound_changes, &mut self.upper_bound_changes)?;
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		Ok(())
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Difference constraint boolean propagator.
pub struct DifferenceLogicBooleans {
	/// Priority level for bounds propagation.
	priority_level: PriorityLevel,
	/// Shared reference to the difference logic graph.
	graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>,
	/// List of boolean variable indices that have recently been reported as fixed to true.
	fixed_bools: IndexSet<usize>,
	/// Whether to proactively check implied constraints.
	use_inc_imp: bool,
}

impl DifferenceLogicBooleans {

	/// Create a new [`DifferenceLogicBooleans`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E,
				   priority_level: PriorityLevel,
				   use_inc_imp: bool,
				   graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>) where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self {
			priority_level,
			graph: graph.clone(),
			fixed_bools: IndexSet::default(),
			use_inc_imp,
		});
	}

}

impl<E> Propagator<E> for DifferenceLogicBooleans
where
	E: ReasoningEngine,
	IntView: SolverIntView<E>,
	BoolView: SolverBoolView<E>,
{
	fn advise_of_backtrack(&mut self, _ctx: &mut E::NotificationCtx<'_>) {
		trace!("Backtrack advise");
		self.fixed_bools.clear();
	}

	fn advise_of_bool_change(&mut self, _ctx: &mut E::NotificationCtx<'_>, data: u64) -> bool {
		trace!("Boolean b{data} fixed.");
		self.fixed_bools.insert(data as usize)
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
		self.graph.borrow_mut().propagate_booleans(ctx, &self.fixed_bools, self.use_inc_imp, false)?;
		self.fixed_bools.clear();
		Ok(())
	}

}

/**********************************************
* Branching strategies using difference logic *
**********************************************/

#[derive(Clone, Debug, PartialEq, Eq)]
/// Brancher that uses the current state of the difference logic graph to make branching decisions.
pub struct DiffLogicBrancher {
	/// Integer variables.
	int_vars: Vec<IntView>,
	/// Integer variable index in the graph.
	int_var_index: Vec<usize>,
	/// Boolean variables.
	bool_vars: Vec<BoolView>,
	/// Shared reference to difference logic graph
	graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>,
	/// The start of the unfixed variables in `int_vars`.
	next: TrailedInt,
	/// Whether to minimize or maximize
	minimize: bool,
}

impl DiffLogicBrancher {

	/// Create a new [`DiffLogicBrancher`]  and add to the end of the branching queue in the solver.
	pub fn new_in<A: BrancherInitActions + ?Sized>(solver: &mut A,
												   int_vars: &Vec<IntView>,
												   bool_vars: &Vec<BoolView>,
												   graph: Rc<RefCell<DifferenceLogicGraph<IntView, BoolView>>>,
												   minimize: bool) {

		trace!("Creating diff logic brancher");
		let graph_ref = graph.borrow();
		let int_var_index = (0..graph_ref.num_nodes()).into_iter().filter(|&n| graph_ref.active[n]).collect_vec();

		let next = solver.new_trailed_int(0);
		solver.push_brancher(Box::new(DiffLogicBrancher {
			int_vars: int_vars.clone(),
			int_var_index,
			bool_vars: bool_vars.clone(),
			graph: graph.clone(),
			next,
			minimize,
		}));

	}

}

impl<D: DecisionActions> Brancher<D> for DiffLogicBrancher
where
	IntView: IntDecisionActions<D, Atom=BoolView>,
	RawLit: BoolInspectionActions<D>,
{
	fn decide(&mut self, actions: &mut D) -> Decision {
		let mut begin = actions.trailed_int(self.next) as usize;

		// return if all variables have been assigned
		if begin == self.int_var_index.len() {
			return Decision::Exhausted;
		}

		// loop until decision found or exhausted
		loop {
			let mut graph = self.graph.borrow_mut();
			let mut selection = None;
			for i in begin..self.int_var_index.len() {
				let index = self.int_var_index[i];
				if self.int_vars[index].val(actions).is_some() || graph.decision_bools[index].peek(actions).is_none() {
					// move the exhausted variable to the front
					self.int_var_index.swap(i, begin);
					if let Some((next_i, score)) = selection {
						if next_i == begin {
							selection = Some((i, score));
						}
					}
					begin += 1;
				} else {
					let new_score = if self.minimize {
						(self.int_vars[index].lower_bound(actions), -graph.decision_bools[index].peek(actions).map_or(IntVal::MAX, |(_, val)| *val))
					} else {
						(-self.int_vars[index].upper_bound(actions), graph.decision_bools[index].peek(actions).map_or(IntVal::MIN, |(_, val)| *val))
					};
					if selection.map_or(true, |(_, sel_score)| new_score < sel_score) {
						selection = Some((i, new_score));
						trace!("{i} is better with score {new_score:?}");
					}
				}
			}
			// return if all variables have been assigned
			let Some((next_i, _)) = selection else {
				return Decision::Exhausted;
			};
			// update the next variable to the index of the first unfixed variable
			let _ = actions.set_trailed_int(self.next, begin as IntVal);

			let index = self.int_var_index[next_i];
			// If there are unfixed booleans, fix the next one
			let mut candidate = graph.decision_bools[index].pop(actions);
			while let Some((b, _)) = candidate {
				if self.bool_vars[*b].val(actions).is_some() {
					candidate = graph.decision_bools[index].pop(actions);
				} else {
					break;
				}
			}

			if let Some((b, _)) = candidate {
				if let BoolViewInner::Lit(lit) = self.bool_vars[*b].0 {
					return Decision::Select(lit);
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;
	use itertools::Itertools;
	use pindakaas::{Lit as RawLit, Var};
	use pindakaas::solver::propagation::SolvingActions;
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::{DiffEdge, DifferenceLogicModel, DifferenceLogicConstraint, DifferenceLogicGraph, DifferenceLogicCollection};
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, IntDecision, Model};
	use crate::actions::{BoolInspectionActions, IntSimplificationActions};
	use crate::constraints::{Constraint, SolverBoolView};
	use crate::helpers::linear_transform::LinearTransform;
	use crate::reformulate::{InitConfig, IntDecisionInner, ReformulationContext};
	use crate::solver::engine::Engine;
	use crate::solver::{BoolView, IntView};
	use crate::solver::solving_context::SolvingContext;
	use crate::solver::Value::Int;

	// TODO adapt level when definition changes
	const PRIO_BOUNDS: u8 = 2;
	const PRIO_BOOLS: u8 = 1;
	const LEVEL: u32 = 2;

	struct DummyActions;

	// Dummy implementation of [`SolvingActions`] to allow creating a [`SolvingContext`]
	impl SolvingActions for DummyActions {
		fn is_decision(&mut self, _lit: RawLit) -> bool {
			panic!("not implemented")
		}

		fn new_observed_var(&mut self) -> Var {
			panic!("not implemented")
		}

		fn phase(&mut self, _lit: RawLit) {
			panic!("not implemented")
		}

		fn unphase(&mut self, _lit: RawLit) {
			panic!("not implemented")
		}
	}

	#[test]
	#[traced_test]
	fn test_relevant_dijkstra() {
		let mut prb = Model::default();
		let b = prb.new_bool_var();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..10).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = vec![map.get_bool(&mut slv, b)];
		let mut graph = DifferenceLogicGraph::new(&mut prb, int_vars, bool_vars);  // TODO need to set pi here?
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		for (x, y, d) in vec![(0, 1, 1), (0, 2, 1), (0, 4, 1),
							  (1, 4, 1), (1, 5, 1), (2, 4, 1), (3, 4, 1), (3, 5, 1),
							  (4, 6, 1), (4, 8, 1),
							  (5, 6, 1), (5, 7, 1), (5, 8, 1), (5, 9, 1),
							  (7, 9, 1), (8, 9, 1)] {
			let _ = graph.new_edge(&mut ctx, DiffEdge::new(x, y, d, None));
		}
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(4, 5, 1, Some(0)));

		let outgoing_x = graph.dijkstra_relevant(&mut ctx, new_index, false);
		trace!("{:?}", outgoing_x);
		assert_eq!(outgoing_x.len(), 2);
		assert!(outgoing_x.contains_key(&5));
		assert!(outgoing_x.contains_key(&7));
		let incoming_y = graph.dijkstra_relevant(&mut ctx, new_index, true);
		trace!("{:?}", incoming_y);
		assert_eq!(incoming_y.len(), 2);
		assert!(incoming_y.contains_key(&2));
		assert!(incoming_y.contains_key(&4));
	}

	#[test]
	#[traced_test]
	fn test_inc_imp() where
		BoolView: SolverBoolView<Engine>
	{
		let mut prb = Model::default();
		let bools = (0..3).into_iter().map(|_| prb.new_bool_var()).collect_vec();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..3).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = bools.into_iter().map(|b| map.get_bool(&mut slv, b)).collect_vec();
		let mut graph = DifferenceLogicGraph::new(&mut prb, int_vars, bool_vars.clone());  // TODO need to set pi here?
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _  = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 1, 2, Some(2)));
		let _ = graph.inc_imp(&mut ctx, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap().lit,
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(bool_vars[1].val(&mut ctx).is_none());
		assert!(bool_vars[2].val(&mut ctx).is_none());
		assert_eq!(graph.open_out[2].num_open(&ctx), 1);
		assert_eq!(graph.open_in[2].num_open(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_inc_imp2() where
		BoolView: SolverBoolView<Engine>
	{
		let mut prb = Model::default();
		let bools = (0..4).into_iter().map(|_| prb.new_bool_var()).collect_vec();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..4).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = bools.into_iter().map(|b| map.get_bool(&mut slv, b)).collect_vec();
		let mut graph = DifferenceLogicGraph::new(&mut prb, int_vars, bool_vars.clone());  // TODO need to set pi here?
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let _  = graph.new_edge(&mut ctx, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut ctx, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_edge(&mut ctx, DiffEdge::new(0, 3, 2, Some(3)));
		let _ = graph.inc_imp(&mut ctx, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap().lit,
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(bool_vars[1].val(&mut ctx).is_none());
		assert!(bool_vars[2].val(&mut ctx).is_none());
		assert!(bool_vars[3].val(&mut ctx).is_none());
		assert_eq!(graph.open_out[0].num_open(&ctx), 2);
		assert_eq!(graph.open_in[0].num_open(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=5]));
		let b = prb.new_bool_var();
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[1], int_vars[2], 4));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], -2));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views = int_vars.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		let b_view = IntView::from(map.get_bool(&mut slv, b));
		slv.assert_all_solutions(&[int_views[0], int_views[1], int_views[2], b_view], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			let Int(b) = sol[3] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}, b = {b}");
			x - y <= -2 && y - z <= 3 && (b < 1 || y - z <= 4) && (b < 1 || x - z <= -2)
		});
	}

	#[test]
	#[traced_test]
	fn test_paper_medium() {
		let mut prb = Model::default();
		let int_vars5 = prb.new_int_vars(4, RangeList::from_iter([1..=5]));
		let int_vars4 = prb.new_int_vars(2, RangeList::from_iter([1..=4]));
		let b = prb.new_bool_var();
		let c = prb.new_bool_var();
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars5[0], int_vars5[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars5[1], int_vars5[2], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars5[2], int_vars4[0], -1));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars4[0], int_vars4[1], 2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars5[0], int_vars5[3], 1));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars5[3], int_vars5[2], -1));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars5[0], int_vars5[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars5[1], int_vars5[2], 4));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars5[1], int_vars4[1], 1));
		diff_logic.add(DifferenceLogicConstraint::Implied(!c, int_vars4[1], int_vars5[1], -2));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views5 = int_vars5.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		let int_views4 = int_vars4.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		let b_view = IntView::from(map.get_bool(&mut slv, b));
		let c_view = IntView::from(map.get_bool(&mut slv, c));
		slv.assert_all_solutions(&[int_views5[0], int_views5[1], int_views5[2], int_views4[0], int_views4[1], int_views5[3], b_view, c_view], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			let Int(u) = sol[3] else { return false };
			let Int(v) = sol[4] else { return false };
			let Int(t) = sol[5] else { return false };
			let Int(b) = sol[6] else { return false };
			let Int(c) = sol[7] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}, u = {u}, v = {v}, t = {t}, b = {b}, c = {c}");
			x - y <= -2 && y - z <= 3 && z - u <= -1 && u - v <= 2 && x - t <= 1 && t - z <= -1 
				&& (b < 1 || x - z <= -2) && (b < 1 || y - z <= 4) && (c < 1 || y - v <= 1) && (c == 1 || y - v > 1)
		});
	}

	#[test]
	#[traced_test]
	fn test_conflict() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], -2));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_err());
	}

	#[test]
	#[traced_test]
	fn test_equal() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], -1));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views = int_vars.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		slv.assert_all_solutions(&[int_views[0], int_views[1], int_views[2]], move |sol| {
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
		let int_vars = prb.new_int_vars(4, RangeList::from_iter([1..=10]));
		let b = prb.new_bool_var();
		let c = prb.new_bool_var();
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[1], int_vars[0], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[2], int_vars[0], -1));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[3].0 else {
			panic!("Should not happen");
		};
		assert!(int_vars[0].unify(&mut prb, IntDecision(IntDecisionInner::Linear(LinearTransform {scale: NonZero::new(2).unwrap(), offset: 1}, var_index))).is_ok());
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views = int_vars.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		let b_view = IntView::from(map.get_bool(&mut slv, b));
		let c_view = IntView::from(map.get_bool(&mut slv, c));
		slv.assert_all_solutions(&[int_views[0], int_views[1], int_views[2], int_views[3], b_view, c_view], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			let Int(t) = sol[3] else { return false };
			let Int(b) = sol[4] else { return false };
			let Int(c) = sol[5] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}, t = {t}, b = {b}, c = {c}");
			x - y <= -2 && z - x <= 3 && (b < 1 || x - z <= 2) && (b < 1 || x - y <= -2) && (c < 1 || y - x <= 2) && (c < 1 || z - x <= -1) && 2 * t + 1 == x
		});
	}

	#[test]
	#[traced_test]
	fn test_unification() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let b = prb.new_bool_var();
		let c = prb.new_bool_var();
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[1], int_vars[0], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[2], int_vars[0], -1));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[2].0 else {
			panic!("Should not happen");
		};
		assert!(int_vars[0].unify(&mut prb, IntDecision(IntDecisionInner::Linear(LinearTransform::offset(1), var_index))).is_ok());
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views = int_vars.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		let b_view = IntView::from(map.get_bool(&mut slv, b));
		let c_view = IntView::from(map.get_bool(&mut slv, c));
		slv.assert_all_solutions(&[int_views[0], int_views[1], int_views[2], b_view, c_view], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			let Int(b) = sol[3] else { return false };
			let Int(c) = sol[4] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}, b = {b}, c = {c}");
			x - y <= -2 && z - x <= 3 && (b < 1 || x - z <= 2) && (b < 1 || x - y <= -2) && (c < 1 || y - x <= 2) && (c < 1 || z - x <= -1) && z + 1 == x
		});
	}

	#[test]
	#[traced_test]
	fn test_constants() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogicCollection::new(PRIO_BOUNDS, PRIO_BOOLS, true, 0, None);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 5));
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL)
			.expect("Creating model failed")
			.expect("Model is empty");
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());
		assert!(int_vars[0].unify(&mut prb, IntDecision::from(5)).is_ok());
		assert!(int_vars[2].unify(&mut prb, IntDecision::from(5)).is_ok());
		assert!(<DifferenceLogicModel as Constraint<Model>>::simplify(&mut diff_logic_model, &mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
			trail: &prb.trail,
		};
		assert!(<DifferenceLogicModel as Constraint<Model>>::to_solver(&mut diff_logic_model, &mut actions).is_ok());
		let int_views = int_vars.iter().map(|&v| map.get_int(&mut slv, v)).collect_vec();
		slv.assert_all_solutions(&[int_views[0], int_views[1], int_views[2]], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			trace!("Checking x = {x}, y = {y}, z = {z}");
			x - y <= 3 && y - z <= -2 && x == 5 && z == 5
		});

	}

}
