//! Structure and algorithms for a global difference logic propagator.

use std::cell::RefCell;
use std::cmp::{max, min, Reverse};
use std::fmt::Debug;
use std::hash::{BuildHasher, Hash};
use std::mem;
use std::rc::Rc;
use itertools::Itertools;
use pindakaas::Lit as RawLit;
use pindakaas::propositional_logic::Formula;
use rustc_hash::FxHasher;
use tracing::trace;
use crate::solver::activation_list::{IntEvent, IntPropCond};
use crate::solver::{BoolView, BoolViewInner, Goal, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, BoolFormula, Conjunction, IntDecision, IntVal, Model};
use crate::actions::{BrancherInitActions, ConstraintInitActions, DecisionActions, TrailingActions};
use crate::branchers::{Brancher, Decision};
use crate::helpers::initial_trail::InitialTrail;
use crate::helpers::linear_transform::LinearTransform;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::TrailedOpenList;
use crate::reformulate::{BoolDecisionInner, IntDecisionIndex, IntDecisionInner};
use crate::solver::trail::TrailedInt;

// Redefine hash-based types using the fast FxBuildHasher.
#[derive(Copy, Clone, Default, Debug)]
/// Custom definition to derive Debug
pub struct FxBuildHasher;

impl BuildHasher for FxBuildHasher {
	type Hasher = FxHasher;
	fn build_hasher(&self) -> FxHasher {
		FxHasher::default()
	}
}

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
fn add_implied_not_equals(diff_model: &mut DifferenceLogicModel, model: &mut Model, b: BoolDecision, x: IntDecision, y: IntDecision, d: IntVal) {
	let decision1 = model.new_bool_var();
	let decision2 = model.new_bool_var();
	*model += Formula::Or(vec![Formula::from(!b), Formula::from(decision1), Formula::from(decision2)]);
	*model += Formula::Or(vec![Formula::from(!decision1), Formula::from(!decision2)]);
	diff_model.add_implied_constraint(decision1, x, y, d - 1);
	diff_model.add_implied_constraint(decision2, y, x, -d - 1);
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
	pub(crate) fn process(&mut self, model: &mut Model, level: u32) -> DifferenceLogicModel {
		let mut diff_model = DifferenceLogicModel::new(self.parameters.clone(), self.boolean_or.clone(), self.objective.clone()); // TODO maybe not clone boolean_or?
		for raw in self.raw_constraints.iter() {
			match raw {
				// Always post global, implied, and reified constraints TODO could check if they are isolated etc?
				DifferenceLogicConstraint::Global(x, y, d) => diff_model.add_global_constraint(*x, *y, *d),
				DifferenceLogicConstraint::Implied(b, x, y, d) => diff_model.add_implied_constraint(*b, *x, *y, *d),
				DifferenceLogicConstraint::Reified(b, x, y, d) => {
					diff_model.add_implied_constraint(*b, *x, *y, *d);
					diff_model.add_implied_constraint(!*b, *y, *x, -*d - 1);
				},
				// b -> x - y == d is transformed to b -> x - y <= d and b -> x - y >= d.
				DifferenceLogicConstraint::ImpliedEquals(b, x, y, d) => {
					if level & 0b1 > 0 {
						diff_model.add_implied_constraint(*b, *x, *y, *d);
						diff_model.add_implied_constraint(*b, *y, *x, -*d);
					}
					if level & 0b1 == 0 || level & 0b10 > 0 {
						*model += (*x - *y).eq(*d).implied_by(*b);
					}
				},
				// x - y != d is transformed to b -> x - y < d and !b -> x - y > d for a new boolean variable b.
				DifferenceLogicConstraint::NotEquals(x, y, d) => {
					if level & 0b100 > 0 {
						let decision = model.new_bool_var();
						diff_model.add_implied_constraint(decision, *x, *y, *d - 1);
						diff_model.add_implied_constraint(!decision, *y, *x, -*d - 1);
					}
					if level & 0b100 == 0 || level & 0b1000 > 0 {
						*model += (*x - *y).ne(*d);
					}
				},
				// b -> x - y != d is transformed to b -> c \/ e; !c \/ !e; c -> x - y < d; e -> x - y > d for new boolean variables c and e.
				DifferenceLogicConstraint::ImpliedNotEquals(b, x, y, d) => {
					if level & 0b10_000 > 0 {
						add_implied_not_equals(&mut diff_model, model, *b, *x, *y, *d);
					}
					if level & 0b10_000 == 0 || level & 0b100_000 > 0 {
						*model += (*x - *y).ne(*d).implied_by(*b);
					}
				},
				// b <-> x - y == d is transformed to b -> x - y == d and !b -> x - y != d
				DifferenceLogicConstraint::ReifiedEquals(b, x, y, d) => {
					if level & 0b1000_000 > 0 {
						diff_model.add_implied_constraint(*b, *x, *y, *d);
						diff_model.add_implied_constraint(*b, *y, *x, -*d);
						add_implied_not_equals(&mut diff_model, model, !*b, *x, *y, *d);
					}
					if level & 0b1000_000 == 0 || level & 0b10_000_000 > 0 {
						*model += (*x - *y).eq(*d).reified_by(*b);
					}
				},
			}
		}
		diff_model
	}
	
}

/*********************************************************
* Model of difference logic for the simplification stage *
*********************************************************/

#[derive(Debug, Clone, PartialEq, Eq)]
/// Representation of set of potential difference constraints within a model.
pub struct DifferenceLogicModel {
	/// User-defined parameters for difference logic.
	parameters: DifferenceLogicParameters,
	/// Collection of boolean OR clauses for detecting conflicting edges.
	boolean_or: IndexSet<(BoolDecision, BoolDecision)>,
	/// Objective (if it exists)
	objective: Option<(IntDecision, Goal)>,
	/// List of global difference constraints to post to the solver.
	global_constraints: Vec<(IntDecision, IntDecision, IntVal)>,
	/// List of implied difference constraints to post to the solver.
	imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
	/// Mapping of integer decision variables to their index.
	int_var_index: IndexSet<IntDecision>,
	/// Mapping of boolean decision variables to their index.
	bool_var_index: IndexSet<BoolDecision>,
	/// Initial trail.
	initial_trail: InitialTrail,
	/// Integer decision variables.
	int_vars: Vec<IntDecision>,
	/// Boolean decision variables.
	bool_vars: Vec<BoolDecision>,
	/// Initial difference logic graph for simplification stage
	initial_graph: Option<DifferenceLogicSimplifier>,
}

impl DifferenceLogicModel {

	pub(crate) fn new(parameters: DifferenceLogicParameters, boolean_or: IndexSet<(BoolDecision, BoolDecision)>, objective: Option<(IntDecision, Goal)>) -> Self {
		Self {
			parameters,
			boolean_or,
			objective,
			global_constraints: Vec::new(),
			imp_constraints: Vec::new(),
			int_var_index: IndexSet::default(),
			bool_var_index: IndexSet::default(),
			initial_trail: InitialTrail::new(),
			int_vars: Vec::new(),
			bool_vars: Vec::new(),
			initial_graph: None,
		}
	}

	/// Add a global constraint.
	fn add_global_constraint(&mut self, x: IntDecision, y: IntDecision, d: IntVal) {
		let _ = self.int_var_index.insert(x);
		let _ = self.int_var_index.insert(y);
		self.global_constraints.push((x, y, d));
	}

	/// Add an implied constraint.
	fn add_implied_constraint(&mut self, b: BoolDecision, x: IntDecision, y: IntDecision, d: IntVal) {
		let _ = self.bool_var_index.insert(b);
		let _ = self.int_var_index.insert(x);
		let _ = self.int_var_index.insert(y);
		self.imp_constraints.push((b, x, y, d));
	}

	/// Return statistics of the captured difference logic constraints:
	/// (# integer variables, # boolean variables, # globally active constraints, # implied constraints)
	pub(crate) fn output_statistics(&self) -> (usize, usize, usize, usize) {
		(self.int_var_index.len(), self.bool_var_index.len(), self.global_constraints.len(), self.imp_constraints.len())
	}

}

fn check_vars_different<A: SimplificationActions>(actions: &mut A, x: IntDecision, y: IntDecision, d: IntVal, b: Option<BoolDecision>) -> Result<bool, ReformulationError> {
	if x == y && d >= 0 {
		trace!("Removing redundant {b:?} implies {x:?} - {y:?} <= {d:?}");
		return Ok(false);
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
		return Ok(false);
	}
	Ok(true)
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
struct DifferenceLogicSimplifier {
	/// Constraint graph.
	graph: DifferenceLogicGraph,
	/// Minimum distances in the global graph.
	distances: Vec<Vec<IntVal>>,
	/// Set of nodes reachable with a direct edge of minimum distance for each node.
	direct_edge: Vec<HashSet<usize>>,

}

impl DifferenceLogicSimplifier {

	fn new(graph: DifferenceLogicGraph) -> Self {
		let len = graph.num_nodes();
		Self {
			graph,
			distances: vec![vec![IntVal::MAX; len]; len],
			direct_edge: vec![HashSet::default(); len],
		}

	}

	/// Compute initial pi values by assuming an additional vertex with a 0-cost path to every other
	/// vertex and applying Bellman-Ford. Fail if a negative cycle is detected.
	fn bellman_ford_init_pi(&mut self, initial_trail: &mut InitialTrail) -> Result<(), ReformulationError> {
		trace!("Calculating initial pi values.");
		let mut distance = vec![0; self.graph.num_nodes() + 1];
		//let mut predecessor = vec![self.nodes.len(); self.nodes.len() + 1];
		let mut changed = false;
		for _ in 0..self.graph.num_nodes() {  // TODO fail faster in case of negative cycle?
			changed = false;
			for n in 0..self.graph.num_nodes() {
				for &e in self.graph.active_out[n].iter(initial_trail) {
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
				for &e in self.graph.active_out[n].iter(initial_trail) {
					let edge = &self.graph.edges[e];
					if distance[edge.from] + edge.val < distance[edge.to] {
						trace!("Found negative cycle!");
						return Err(ReformulationError::TrivialUnsatisfiable);  // TODO output cycle (not needed at the moment)?
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
	fn johnson_full<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>) -> Result<(), ReformulationError> {

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
				for &index in self.graph.active_out[s].iter(adapter.initial_trail) {
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
			while i < self.graph.active_out[n].len(adapter.initial_trail) {
				let &e = self.graph.active_out[n].index(adapter.initial_trail, i);
				let edge = &self.graph.edges[e];
				if self.distances[n][edge.to] < edge.val || (self.distances[n][edge.to] == edge.val && reached.contains(&edge.to)) {
					trace!("Global edge {edge:?} is redundant, shortest path of length {} found", self.distances[n][edge.to]);
					let _ = self.graph.active_out[n].swap_remove(adapter.initial_trail, i);
					let _ = self.graph.active_in[edge.to].swap_remove_element(adapter.initial_trail, &e);
				} else {
					let _ = reached.insert(edge.to);
					i += 1;
				}
			}

			for i in self.graph.open_out[n].open_iter(adapter.initial_trail) {
				let &e = self.graph.open_out[n].index(adapter.initial_trail, i);
				let edge = &self.graph.edges[e];
				if self.distances[n][edge.to] <= edge.val {
					trace!("Implied edge {edge:?} is redundant, shortest path of length {} found", self.distances[n][edge.to]);
					self.graph.close_imp_edge(adapter.initial_trail, e);
				}
			}

			for i in self.graph.open_in[n].open_iter(adapter.initial_trail) {
				let &e = self.graph.open_in[n].index(adapter.initial_trail, i);
				let edge = &self.graph.edges[e];
				if self.distances[n][edge.from] < -edge.val {
					trace!("Implied edge {edge:?} is falsified, opposite shortest path of length {} found", self.distances[n][edge.from]);
					adapter.actions.set_bool(!edge.bool_var.map_or(BoolDecision::from(true), |b| adapter.bool_vars[b]))?;  // TODO no reason recorded here (not needed at the moment)
					self.graph.close_imp_edge(adapter.initial_trail, e);
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
					adapter.actions.unify_int(adapter.int_vars[prev], adapter.int_vars[cur] + self.distances[prev][cur])?;
					cur = prev;
					self.distances[cur][cur] = IntVal::MAX;
				}
			}
		}

		Ok(())

	}

	/// Check if the underlying variables are different, if not reemit the potentially implied difference constraint.
	fn check_vars_different<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>, x: usize, y: usize, d: IntVal, b: Option<usize>) -> Result<bool, ReformulationError> {
		check_vars_different(adapter.actions, adapter.int_vars[x], adapter.int_vars[y], d, b.map(|b| adapter.bool_vars[b]))
	}

	/// Remove the given node from the trailing infrastructure.
	fn trail_remove_node(&mut self, initial_trail: &mut InitialTrail, n: usize) {
		self.graph.active_out[n].remove_trail(initial_trail);
		self.graph.active_in[n].remove_trail(initial_trail);
		self.graph.open_out[n].remove_trail(initial_trail);
		self.graph.open_in[n].remove_trail(initial_trail);
		self.graph.active[n] = false;
		self.graph.num_active_nodes -= 1;
	}

	/// Update the offset of a node, including the value of all edges.
	fn update_node_offset<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>, n: usize, offset: IntVal) -> Result<(), ReformulationError> {

		trace!("Updating the offset of node {n} by {offset}");
		self.graph.pi[n] += offset;
		let mut i = 0;
		while i < self.graph.active_out[n].len(adapter.initial_trail) {
			let &e = self.graph.active_out[n].index(adapter.initial_trail, i);
			let to = self.graph.edges[e].to;
			if self.check_vars_different(adapter, n, to, self.graph.edges[e].val, None)? {
				self.graph.edges.get_mut(e).unwrap().val -= offset;
				i += 1;
			} else {
				let _ = self.graph.active_out[n].swap_remove(adapter.initial_trail, i);
				let _ = self.graph.active_in[to].swap_remove_element(adapter.initial_trail, &e);
			}
		}
		i = 0;
		while i < self.graph.active_in[n].len(adapter.initial_trail) {
			let &e = self.graph.active_in[n].index(adapter.initial_trail, i);
			let from = self.graph.edges[e].from;
			if self.check_vars_different(adapter, from, n, self.graph.edges[e].val, None)? {
				self.graph.edges.get_mut(e).unwrap().val += offset;
				i += 1;
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(adapter.initial_trail, &e);
				let _ = self.graph.active_in[n].swap_remove(adapter.initial_trail, i);
			}
		}
		for i in self.graph.open_out[n].open_iter(adapter.initial_trail) {
			let &e = self.graph.open_out[n].index(adapter.initial_trail, i);
			if self.check_vars_different(adapter, n, self.graph.edges[e].to, self.graph.edges[e].val, self.graph.edges[e].bool_var)? {
				self.graph.edges.get_mut(e).unwrap().val -= offset;
			} else {
				self.graph.close_imp_edge(adapter.initial_trail, e);
			}
		}
		for i in self.graph.open_in[n].open_iter(adapter.initial_trail) {
			let &e = self.graph.open_in[n].index(adapter.initial_trail, i);
			if self.check_vars_different(adapter, self.graph.edges[e].from, n, self.graph.edges[e].val, self.graph.edges[e].bool_var)? {
				self.graph.edges.get_mut(e).unwrap().val += offset;
			} else {
				self.graph.close_imp_edge(adapter.initial_trail, e);
			}
		}
		Ok(())

	}

	/// Moves all edges from the old node to the new node, adapted by the given offset.
	fn unify_nodes<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>, old: usize, new: usize, offset: IntVal) -> Result<(), ReformulationError> {

		trace!("Moving all edges from node {old} to node {new} with offset {offset}");
		let mut mod_edges = Vec::new();
		for i in 0..self.graph.active_out[old].len(adapter.initial_trail) {
			let &e = self.graph.active_out[old].index(adapter.initial_trail, i);
			let to = self.graph.edges[e].to;
			let val = self.graph.edges[e].val;
			if self.check_vars_different(adapter, new, to, val - offset, None)? && (self.distances[new][to] > val - offset || (self.distances[new][to] == val - offset && !self.direct_edge[new].contains(&to))) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.from = new;
				edge.val -= offset;
				self.graph.active_out[new].push(adapter.initial_trail, e);
				let _ = self.direct_edge.get_mut(new).unwrap().insert(edge.to);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_in[to].swap_remove_element(adapter.initial_trail, &e);
			}
		}
		for i in 0..self.graph.active_in[old].len(adapter.initial_trail) {
			let &e = self.graph.active_in[old].index(adapter.initial_trail, i);
			let from = self.graph.edges[e].from;
			let val = self.graph.edges[e].val;
			if self.check_vars_different(adapter, from, new, val + offset, None)? && (self.distances[from][new] > val + offset || (self.distances[from][new] == val + offset && !self.direct_edge[from].contains(&new))) {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.to = new;
				edge.val += offset;
				self.graph.active_in[new].push(adapter.initial_trail, e);
				let _ = self.direct_edge.get_mut(from).unwrap().insert(new);
				mod_edges.push(e);
			} else {
				let _ = self.graph.active_out[from].swap_remove_element(adapter.initial_trail, &e);
			}
		}
		for i in self.graph.open_out[old].open_iter(adapter.initial_trail) {
			let &e = self.graph.open_out[old].index(adapter.initial_trail, i);
			if self.check_vars_different(adapter, new, self.graph.edges[e].to, self.graph.edges[e].val - offset, self.graph.edges[e].bool_var)? {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.from = new;
				edge.val -= offset;
				edge.out_index = self.graph.open_out[new].len();
				self.graph.open_out[new].push(e);
			} else {
				self.graph.close_imp_edge(adapter.initial_trail, e);
			}

		}
		for i in self.graph.open_in[old].open_iter(adapter.initial_trail) {
			let &e = self.graph.open_in[old].index(adapter.initial_trail, i);
			if self.check_vars_different(adapter, self.graph.edges[e].from, new, self.graph.edges[e].val + offset, self.graph.edges[e].bool_var)? {
				let edge = self.graph.edges.get_mut(e).unwrap();
				edge.to = new;
				edge.val += offset;
				edge.in_index = self.graph.open_in[new].len();
				self.graph.open_in[new].push(e);
			} else {
				self.graph.close_imp_edge(adapter.initial_trail, e);
			}
		}
		self.trail_remove_node(adapter.initial_trail, old);
		// Check consequences of all modified active edges
		for e in mod_edges {
			self.graph.propagate_edge_addition(adapter, e, true, true)?;
		}
		Ok(())

	}

	// Add an implied bound to the model.
	fn add_implied_bound<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>, bool_var: usize, int_var: usize, lt: bool, value: IntVal) {
		let bound = if lt {
			Box::new(BoolFormula::Atom(adapter.int_vars[int_var].leq(value)))
		} else {
			Box::new(BoolFormula::Atom(adapter.int_vars[int_var].geq(value)))
		};
		adapter.actions.add_constraint(BoolFormula::Implies(
			Box::new(BoolFormula::Atom(adapter.bool_vars[bool_var])),
			bound,
		))
	}

	/// Check if nodes with fixed domain exist, if yes remove them from the graph.
	fn check_remove_fixed_nodes<A: SimplificationActions>(&mut self, adapter: &mut SimplificationModelAdapter<A>) {

		for n in 0..self.graph.num_nodes() {
			if self.graph.active[n] && adapter.get_int_lower_bound(n) == adapter.get_int_upper_bound(n) {
				trace!("Var {n} has a fixed value - removing from graph");
				let val = adapter.get_int_lower_bound(n);
				for &e in self.graph.active_out[n].iter(adapter.initial_trail) {
					let edge = &self.graph.edges[e];
					trace!("Removing outgoing edge {edge:?}");
					let _ = self.graph.active_in[edge.to].swap_remove_element(adapter.initial_trail, &e);
				}
				for &e in self.graph.active_in[n].iter(adapter.initial_trail) {
					let edge = &self.graph.edges[e];
					trace!("Removing incoming edge {edge:?}");
					let _ = self.graph.active_out[edge.from].swap_remove_element(adapter.initial_trail, &e);
				}
				for i in self.graph.open_out[n].open_iter(adapter.initial_trail) {
					let &e = self.graph.open_out[n].index(adapter.initial_trail, i);
					let edge = &self.graph.edges[e];
					trace!("Reemitting implied outgoing edge {edge:?}");
					self.add_implied_bound(adapter, edge.bool_var.unwrap(), edge.to, false, val - edge.val);
					self.graph.close_imp_edge(adapter.initial_trail, e);
				}
				for i in self.graph.open_in[n].open_iter(adapter.initial_trail) {
					let &e = self.graph.open_in[n].index(adapter.initial_trail, i);
					let edge = &self.graph.edges[e];
					trace!("Reemitting implied incoming edge {edge:?}");
					self.add_implied_bound(adapter, edge.bool_var.unwrap(), edge.from, true, val + edge.val);
					self.graph.close_imp_edge(adapter.initial_trail, e);
				}
				self.trail_remove_node(adapter.initial_trail, n);
			}
		}

	}

	/// Check if nodes with no edges exist, if yes remove them from the graph.
	fn check_remove_isolated_nodes(&mut self, initial_trail: &mut InitialTrail) {

		for n in 0..self.graph.num_nodes() {
			if self.graph.active[n] &&
				self.graph.active_out[n].len(initial_trail) == 0 &&
				self.graph.active_in[n].len(initial_trail) == 0 &&
				self.graph.open_out[n].num_open(initial_trail) == 0 &&
				self.graph.open_in[n].num_open(initial_trail) == 0 {
				trace!("Var {n} has no edges - removing from graph");
				self.trail_remove_node(initial_trail, n);
			}
		}

	}

	/// Check if isolated booleans exist, if yes mark them as inactive.
	fn check_remove_isolated_booleans(&mut self, initial_trail: &mut InitialTrail) {
		for b in 0..self.graph.bool_implications.len() {
			if self.graph.bool_active[b] && self.graph.bool_implications[b].num_open(initial_trail) == 0 {
				trace!("Boolean {b} has no edges - removing from graph");
				self.graph.bool_implications[b].remove_trail(initial_trail);
				self.graph.bool_active[b] = false;
			}
		}
	}

}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogicModel {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for &x in self.int_var_index.iter() {
			actions.simplify_on_change_int(x);
		}
		for &b in self.bool_var_index.iter() {
			actions.simplify_on_change_bool(b);
		}
		
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {

		// In the initial run, the graph needs to be built
		if self.initial_graph.is_none() {
			// Variables might be removed or transformed, so rebuild index
			self.int_var_index.clear();
			self.bool_var_index.clear();
			let mut trimmed_constraints = Vec::new();
			let mut trimmed_imp_constraints = Vec::new();

			for &(x, y, d) in self.global_constraints.iter() {
				if check_vars_different(actions, x, y, d, None)? {
					let (x_trans, xd) = update_transform(x);
					let (y_trans, yd) = update_transform(y);
					trimmed_constraints.push((self.int_var_index.insert_full(x_trans).0,
											  self.int_var_index.insert_full(y_trans).0,
											  d - xd + yd));
				}
			}

			for &(b, x, y, d) in self.imp_constraints.iter() {
				if check_vars_different(actions, x, y, d, Some(b))? {
					let (x_trans, xd) = update_transform(x);
					let (y_trans, yd) = update_transform(y);
					if let Some(val) = actions.get_bool_val(b) {
						// Boolean is already fixed: Global constraint if true, skipped if false.
						trace!("Fixed boolean {b:?} ({val}) for {x:?} - {y:?} <= {d:?}");
						if val {
							trimmed_constraints.push((self.int_var_index.insert_full(x_trans).0,
													  self.int_var_index.insert_full(y_trans).0,
													  d - xd + yd));
						}
					} else {
						trimmed_imp_constraints.push((self.bool_var_index.insert_full(b).0,
													  self.int_var_index.insert_full(x_trans).0,
													  self.int_var_index.insert_full(y_trans).0,
													  d - xd + yd));
					}
				}
			}

			trace!("Creating DifferenceLogicGraph for {} int and {} bool vars, {} global and {} implied edges.", self.int_var_index.len(), self.bool_var_index.len(), trimmed_constraints.len(), trimmed_imp_constraints.len());
			let mut graph = DifferenceLogicGraph::new(&mut self.initial_trail, self.int_var_index.len(), self.bool_var_index.len());
			self.int_vars = self.int_var_index.iter().map(|&v| v).collect_vec();
			trace!("Original int vars:");
			for &v in self.int_vars.iter() {
				trace!("{v:?}: lb {:?}, ub: {:?}", actions.get_int_lower_bound(v), actions.get_int_upper_bound(v));
			}
			self.bool_vars = self.bool_var_index.iter().map(|&v| v).collect_vec();

			// Add global constraints
			for (x, y, d) in trimmed_constraints.into_iter() {
				let _ = graph.new_edge(&mut self.initial_trail, DiffEdge::new(x, y, d, None));
			}

			let mut decision_bool_cache = vec![Vec::new(); self.int_vars.len()];
			// Add implied constraints
			for (b, x, y, d) in trimmed_imp_constraints.into_iter() {
				let _ = graph.new_edge(&mut self.initial_trail, DiffEdge::new(x, y, d, Some(b)));
				for i in graph.open_in[x].open_iter(&self.initial_trail) {
					let e_xor = *graph.open_in[x].index(&self.initial_trail, i);
					let edge = &graph.edges[e_xor];
					if edge.from == y && edge.val + d < 0 && self.boolean_or.contains(&(self.bool_vars[b], self.bool_vars[edge.bool_var.unwrap()])) {
						trace!("Found pair of implied edges in XOR configuration between {x} and {y} (lengths {d}, {})", edge.val);
						actions.unify_bool(self.bool_vars[b], !self.bool_vars[edge.bool_var.unwrap()])?;
						decision_bool_cache[x].push((d, b));
						decision_bool_cache[y].push((edge.val, edge.bool_var.unwrap()));
					}
				}
			}
			// TODO investigate to do this collection differently?
			for (i1, &b1) in self.bool_vars.iter().enumerate() {
				if let Some(i2) = self.bool_var_index.get_index_of(&!b1) {
					for ei1 in graph.bool_implications[i1].open_iter(&self.initial_trail) {
						let &e1 = graph.bool_implications[i1].index(&self.initial_trail, ei1);
						for ei2 in graph.bool_implications[i2].open_iter(&self.initial_trail) {
							let &e2 = graph.bool_implications[i2].index(&self.initial_trail, ei2);
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

			let mut initial_lb_changes = (0..self.int_vars.len()).into_iter().collect();
			let mut initial_ub_changes = (0..self.int_vars.len()).into_iter().collect();
			let mut initial_graph = DifferenceLogicSimplifier::new(graph);
			let mut adapter = SimplificationModelAdapter::new(actions, &mut self.initial_trail, &mut self.int_vars, &self.bool_vars);
			trace!("Starting initial propagation with graph: {}", initial_graph.graph.to_dot(&mut adapter));
			initial_graph.bellman_ford_init_pi(adapter.initial_trail)?;
			initial_graph.graph.propagate_bounds(&mut adapter, &mut initial_lb_changes, &mut initial_ub_changes)?;
			let fixed_bools = (0..adapter.bool_vars.len()).into_iter()
				.filter(|&b| adapter.get_bool_val(b).is_some() && initial_graph.graph.bool_active[b]).collect();
			initial_graph.graph.propagate_booleans(&mut adapter, &fixed_bools, false, true)?;
			// Already do removals before Johnson's to reduce complexity of the graph
			initial_graph.check_remove_fixed_nodes(&mut adapter);
			initial_graph.check_remove_isolated_nodes(adapter.initial_trail);
			if initial_graph.graph.num_active_nodes == 0 {
				// If no nodes are left, there is nothing more to do
				trace!("No more nodes left, return subsumed");
				return Ok(SimplificationStatus::Subsumed);
			}
			initial_graph.johnson_full(&mut adapter)?;
			self.initial_graph = Some(initial_graph);
			
		} else {
			
			let initial_graph = self.initial_graph.as_mut().unwrap();
			
			trace!("Repeated call to simplify");
			let mut adapter = SimplificationModelAdapter::new(actions, &mut self.initial_trail, &mut self.int_vars, &self.bool_vars);
			let mut has_change = false;
			for n in 0..adapter.int_vars.len() {
				if initial_graph.graph.active[n] {
					let alias = adapter.actions.resolve_alias(adapter.int_vars[n]);
					if adapter.int_vars[n] != alias {
						trace!("Var alias is different (was {:?}, is {:?})", adapter.int_vars[n], alias);
						let (v_trans, vd) = update_transform(alias);
						if let Some(new) = self.int_var_index.get_index_of(&v_trans) {
							initial_graph.unify_nodes(&mut adapter, n, new, vd)?;
						} else if !matches!(alias.0, IntDecisionInner::Const(_)) {
							*initial_graph.graph.lower_bound[n].as_mut().unwrap() -= vd;
							*initial_graph.graph.upper_bound[n].as_mut().unwrap() -= vd;
							initial_graph.update_node_offset(&mut adapter, n, vd)?;
							adapter.int_vars[n] = v_trans;
						}
						has_change = true;
					}
				}
			}
			let mut lower_bound_changes = IndexSet::default();
			let mut upper_bound_changes = IndexSet::default();
			for n in 0..adapter.int_vars.len() {
				if !initial_graph.graph.active[n] {
					continue;
				}
				if initial_graph.graph.lower_bound[n].map_or(true, |v| v != adapter.get_int_lower_bound(n)) {
					let _ = lower_bound_changes.insert(n);
					has_change = true;
				}
				if initial_graph.graph.upper_bound[n].map_or(true, |v| v != adapter.get_int_upper_bound(n)) {
					let _ = upper_bound_changes.insert(n);
					has_change = true;
				}
			}
			let mut fixed_bools = IndexSet::default();
			for b in 0..self.bool_vars.len() {
				if adapter.get_bool_val(b).is_some() && initial_graph.graph.bool_active[b] {
					let _ = fixed_bools.insert(b);
					has_change = true;
				}
			}
			if !has_change {
				trace!("No more changes for now, exit");
				return Ok(SimplificationStatus::NoFixpoint);
			}
			initial_graph.graph.propagate_bounds(&mut adapter, &mut lower_bound_changes, &mut upper_bound_changes)?;
			initial_graph.graph.propagate_booleans(&mut adapter, &fixed_bools, true, true)?;

		}

		// Common postprocessing: Reduce graph
		let initial_graph = self.initial_graph.as_mut().unwrap();
		let mut adapter = SimplificationModelAdapter::new(actions, &mut self.initial_trail, &mut self.int_vars, &self.bool_vars);
		initial_graph.check_remove_fixed_nodes(&mut adapter);
		initial_graph.check_remove_isolated_nodes(adapter.initial_trail);
		if initial_graph.graph.num_active_nodes == 0 {
			// If no nodes are left, there is nothing more to do
			trace!("No more nodes left, return subsumed");
			return Ok(SimplificationStatus::Subsumed);
		}
		initial_graph.check_remove_isolated_booleans(adapter.initial_trail);
		trace!("Graph at the end of simplify: {}", initial_graph.graph.to_dot(&mut adapter));
		// Repeat simplification until (local) fixpoint
		self.simplify(actions)

	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		trace!("Transforming DifferenceLogicGraph to solver");
		let mut initial_graph = mem::replace(&mut self.initial_graph, None).unwrap(); // TODO copy and reduce vs. replace?
		self.initial_trail.init_trail(slv);
		initial_graph.graph.init_trail(&mut self.initial_trail);
		initial_graph.graph.reset_bounds();
		trace!("Immediately before transformation:");
		for (i, &v) in self.int_vars.iter().enumerate() {
			if initial_graph.graph.active[i] {
				trace!("{v:?}");
			}
		}
		let int_vars = self.int_vars.iter().map(|&v| slv.get_solver_int(v)).collect_vec();
		trace!("Transformed int vars:");
		for (i, &v) in int_vars.iter().enumerate() {
			if initial_graph.graph.active[i] {
				trace!("{v:?}: lb {:?}, ub: {:?}", slv.get_int_lower_bound(v), slv.get_int_upper_bound(v));
			}
		}
		let bool_vars = self.bool_vars.iter().map(|&v| slv.get_solver_bool(v)).collect_vec();
		let graph_cell = Rc::new(RefCell::new(initial_graph.graph));
		DifferenceLogicBounds::new_in(slv, &int_vars, &bool_vars, self.parameters.priority_level_bounds, graph_cell.clone());
		DifferenceLogicBooleans::new_in(slv, &int_vars, &bool_vars, self.parameters.priority_level_bools, self.parameters.use_inc_imp, graph_cell.clone());
		if self.parameters.branching > 0 {
			DiffLogicBrancher::new_in(slv, &int_vars, &bool_vars, graph_cell, self.objective.map_or(true, |(_, o)| o == Goal::Minimize));
		}
		Ok(())
	}
}


#[derive(Debug, PartialEq, Eq)]
/// A model adapter using [SimplificationActions], [IntDecision], and [BoolDecision] for use during simplification.
struct SimplificationModelAdapter<'a, S> {
	actions: &'a mut S,
	initial_trail: &'a mut InitialTrail,
	int_vars: &'a mut Vec<IntDecision>,
	bool_vars: &'a Vec<BoolDecision>,
}

impl<'a, S: SimplificationActions> SimplificationModelAdapter<'a, S> {

	fn new(actions: &'a mut S, initial_trail: &'a mut InitialTrail, int_vars: &'a mut Vec<IntDecision>, bool_vars: &'a Vec<BoolDecision>) -> Self {
		Self {
			actions,
			initial_trail,
			int_vars,
			bool_vars,
		}
	}

}

impl<S: SimplificationActions> ModelAdapter<ReformulationError> for SimplificationModelAdapter<'_, S> {

	fn get_int_lower_bound(&self, n: usize) -> IntVal {
		self.actions.get_int_lower_bound(self.int_vars[n])
	}

	fn set_int_lower_bound(&mut self, n: usize, value: IntVal, _bool_var: Option<usize>, _lb_var: usize, _lb_val: IntVal) -> Result<(), ReformulationError> {
		self.actions.set_int_lower_bound(self.int_vars[n], value)?;
		Ok(())
	}

	fn get_int_upper_bound(&self, n: usize) -> IntVal {
		self.actions.get_int_upper_bound(self.int_vars[n])
	}

	fn set_int_upper_bound(&mut self, n: usize, value: IntVal, _bool_var: Option<usize>, _ub_var: usize, _ub_val: IntVal) -> Result<(), ReformulationError> {
		self.actions.set_int_upper_bound(self.int_vars[n], value)?;
		Ok(())
	}

	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions {
		self.initial_trail
	}

	fn get_bool_val(&self, n: usize) -> Option<bool> {
		self.actions.get_bool_val(self.bool_vars[n])
	}

	fn process_negative_cycle(&mut self, var: Option<usize>, _reason: Vec<usize>) -> Result<(), ReformulationError> {
		let var = var.map_or(BoolDecision::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var)?;
		Ok(())
	}

	fn set_bool_false(&mut self, bool_var: Option<usize>, _edge: usize, _lb_fixed: bool) -> Result<(), ReformulationError> {
		let var = bool_var.map_or(BoolDecision::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var)?;
		Ok(())
	}

}

/*************************************************************
* Common graph structure used for simplification and solving *
*************************************************************/

/// Provides access to the current state of the model independent of representation.
trait ModelAdapter<E> {

	/// Return the lower bound for the variable identified by index.
	fn get_int_lower_bound(&self, n: usize) -> IntVal;

	/// Set the lower bound for the variable identified by index as a consequence of the boolean and
	/// the given lower bound.
	fn set_int_lower_bound(&mut self, n: usize, value: IntVal, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal) -> Result<(), E>;

	/// Return the upper bound for the variable identified by index.
	fn get_int_upper_bound(&self, n: usize) -> IntVal;

	/// Set the upper bound for the variable identified by index as a consequence of the boolean and
	/// the given upper bound.
	fn set_int_upper_bound(&mut self, n: usize, value: IntVal, bool_var: Option<usize>, ub_var: usize, ub_val: IntVal) -> Result<(), E>;

	/// Return the infrastructure to deal with trailed integers.
	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions;

	/// Get the value of the boolean variable identified by index if it is set.
	fn get_bool_val(&self, n: usize) -> Option<bool>;

	/// Enforce the negation of the boolean variable identified by index with the reason given as an
	/// array of boolean variables. Fail if var is None.
	fn process_negative_cycle(&mut self, var: Option<usize>, reason: Vec<usize>) -> Result<(), E>;

	/// Enforce the negation of the boolean variable identified by index with a reason given by a
	/// lower and upper bound.
	fn set_bool_false(&mut self, bool_var: Option<usize>, edge: usize, lb_fixed: bool) -> Result<(), E>;

}

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
pub struct DifferenceLogicGraph {
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

impl DifferenceLogicGraph {

	fn new(initial_trail: &mut InitialTrail, int_vars: usize, bool_vars: usize) -> Self {
		Self {
			active: vec![true; int_vars],
			active_out: (0..int_vars).into_iter().map(|_| TrailedList::new(initial_trail)).collect(),
			active_in: (0..int_vars).into_iter().map(|_| TrailedList::new(initial_trail)).collect(),
			open_out: (0..int_vars).into_iter().map(|_| TrailedOpenList::new(initial_trail)).collect(),
			open_in: (0..int_vars).into_iter().map(|_| TrailedOpenList::new(initial_trail)).collect(),
			lower_bound: vec![None; int_vars],
			upper_bound: vec![None; int_vars],
			pi: vec![0; int_vars],
			backtrace: vec![None; int_vars],
			visited: vec![false; int_vars],
			num_active_nodes: int_vars,
			num_open_edges: initial_trail.new_trailed_int(0),
			edges: Vec::new(),
			bool_implications: (0..bool_vars).into_iter().map(|_| TrailedOpenList::new(initial_trail)).collect(),
			bool_active: vec![true; bool_vars],
			visited_updates: Vec::new(),
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			decision_bools: (0..int_vars).into_iter().map(|_| TrailedOpenList::new(initial_trail)).collect(),
		}
	}

	/// Return the total number of nodes.
	fn num_nodes(&self) -> usize {
		self.active.len()
	}

	/// Initialize the trailed infrastructure for this graph.
	fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		for n in (0..self.num_nodes()).filter(|&n| self.active[n]).into_iter() {
			self.active_out[n].init_trail(initial_trail);
			self.active_in[n].init_trail(initial_trail);
			self.open_out[n].init_trail(initial_trail);
			self.open_in[n].init_trail(initial_trail);
			self.decision_bools[n].init_trail(initial_trail);
		}
		for b in 0..self.bool_implications.len() {
			if self.bool_active[b] {
				self.bool_implications[b].init_trail(initial_trail);
			}
		}
		self.num_open_edges = initial_trail.map_to_trail(self.num_open_edges);
	}

	/// Add a new edge to the graph, return the index. Depending on the boolean, the edge is added 
	/// globally (boolean is None) or as an implied edge.
	fn new_edge<T: TrailingActions + ?Sized>(&mut self, actions: &mut T, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		if let Some(b) = edge.bool_var {
			edge.bool_index = self.bool_implications[b].len();
			self.bool_implications[b].push(index);
			edge.out_index = self.open_out[edge.from].len();
			self.open_out[edge.from].push(index);
			edge.in_index = self.open_in[edge.to].len();
			self.open_in[edge.to].push(index);
			let _ = actions.set_trailed_int(self.num_open_edges, actions.get_trailed_int(self.num_open_edges) + 1);
		} else {
			self.active_out[edge.from].push(actions, index);
			self.active_in[edge.to].push(actions, index);
		}
		self.edges.push(edge);
		index
	}

	/// Activate the implied edge given by the index.
	fn activate_imp_edge<T: TrailingActions + ?Sized>(&mut self, actions: &mut T, index: usize) {
		let edge = &self.edges[index];
		self.active_out[edge.from].push(actions, index);
		self.active_in[edge.to].push(actions, index);
	}

	/// Close the implied edge given by the index.
	fn close_imp_edge<T: TrailingActions + ?Sized>(&mut self, actions: &mut T, e: usize) {
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
		let _ = actions.set_trailed_int(self.num_open_edges, actions.get_trailed_int(self.num_open_edges) - 1);
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
	fn get_cur_lower_bound<E, A: ModelAdapter<E>>(&self, adapter: &A, n: usize) -> IntVal {
		match self.lower_bound[n] {
			Some(lb) => lb,
			None => adapter.get_int_lower_bound(n),
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
	fn get_cur_upper_bound<E, A: ModelAdapter<E>>(&self, adapter: &A, n: usize) -> IntVal {
		match self.upper_bound[n] {
			Some(ub) => ub,
			None => adapter.get_int_upper_bound(n),
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
	fn get_cycle_reason(&self, node: usize) -> Vec<usize> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = self.backtrace[var] {
			if let Some(b) = b {
				reason.push(b);
			}
			var = cur;
		}
		reason
	}

	/// Check incremental addition of the edge given by index to the active graph.
	/// Returns true if addition is possible. Otherwise, false is returned for implied edges, and a
	/// conflict is caused by global edges.
	fn inc_sat<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, new_index: usize) -> Result<bool, E> { // TODO unit tests

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
			for &e in self.active_out[s].iter(adapter.get_trailing_actions()) {
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
			adapter.process_negative_cycle(new_edge.bool_var, self.get_cycle_reason(new_edge.from))?;
			return Ok(false);
		}
		for (var, val) in pi_new {
			self.pi[var] = val;
		}
		Ok(true)
	}

	/// Perform dijkstra from the given node to all relevant nodes in the graph, return a map of
	/// distances. Can be performed in forward or backward direction.
	fn dijkstra_relevant<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, new_edge: usize, reverse: bool) -> IndexMap<usize, IntVal> {
		
		trace!("Starting relevant dijkstra for e{new_edge:?} in mode reverse={reverse}");
		self.reset_visit();
		let new_edge = &self.edges[new_edge];
		let origin = if reverse {new_edge.to} else {new_edge.from};
		let relevant_target = if reverse {new_edge.from} else {new_edge.to};
		let mut distances = IndexMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = PriorityQueue::default();
		let _ = queue.push(origin, Reverse(0));
		let _ = queue.push(relevant_target, Reverse(new_edge.val + if reverse { self.pi[relevant_target] - self.pi[origin] } else { self.pi[origin] - self.pi[relevant_target] }));
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			self.visit(s);
			let s_relevant = distances.contains_key(&s);
			//trace!("dijkstra on current node {s:?} with dist {dist}");
			for &e in if reverse {self.active_in[s].iter(adapter.get_trailing_actions())} else {self.active_out[s].iter(adapter.get_trailing_actions())} {
				let edge = &self.edges[e];
				let target = if reverse {edge.from} else {edge.to};
				let new_dist = dist + edge.val + if reverse {self.pi[target] - self.pi[s]} else {self.pi[s] - self.pi[target]};
				if !self.visited[target] {
					let prev = queue.push_increase(target, Reverse(new_dist));
					// Cases where we want to propagate the relevancy of s to t:
					// - First path to t (equal to previous distance of infinity)
					// - Path to t with lower distance than before
					// - Path to t with same distance as before and s is not relevant (prefer irrelevancy in ties)
					if prev.map_or(true, |Reverse(old_dist)| new_dist < old_dist || (new_dist == old_dist && !s_relevant)) {
						if s_relevant || target == relevant_target {
							// Add new distance to the map, if key was not present before increase relevant count.
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
					//trace!("dijkstra adding node {:?} with dist {new_dist}", target.var);
				}
			}
			if s_relevant {
				relevant_count -= 1;
			}
		}
		distances

	}

	/// Check if the new edge given by the index implies or falsifies any of the open edges.
	fn inc_imp<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, new_index: usize) -> Result<(), E> {
		
		if adapter.get_trailing_actions().get_trailed_int(self.num_open_edges) == 0 {
			trace!("No open implications");
			return Ok(());
		}

		// Incoming paths to relevant nodes starting from u via uv.
		let incoming_u = self.dijkstra_relevant(adapter, new_index, false); // todo could store distances at nodes as well?
		trace!("incoming_u is {incoming_u:?}");
		// Outgoing paths from relevant nodes ending at v via uv.
		let outgoing_v = self.dijkstra_relevant(adapter, new_index, true);
		trace!("outgoing_v is {outgoing_v:?}"); // todo check how to include pi change check at this point?
		let indegree_u: usize = incoming_u.iter().map(|(&n, _)| self.open_in[n].num_open(adapter.get_trailing_actions())).sum();
		let outdegree_v: usize = outgoing_v.iter().map(|(&n, _)| self.open_out[n].num_open(adapter.get_trailing_actions())).sum();
		trace!("indegree: {indegree_u:?}, outdegree: {outdegree_v:?}");
		
		let new_edge_val = self.edges[new_index].val;
		
		if indegree_u < outdegree_v {
			for &n in incoming_u.keys() {
				for i in self.open_in[n].open_iter(adapter.get_trailing_actions()) {
					let &e = self.open_in[n].index(adapter.get_trailing_actions(), i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, implied)");
					if outgoing_v.contains_key(&edge.from) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint {edge:?} is implied");
						self.close_imp_edge(adapter.get_trailing_actions(), e);
					}
				}
				for i in self.open_out[n].open_iter(adapter.get_trailing_actions()) {
					let &e = self.open_out[n].index(adapter.get_trailing_actions(), i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, reverse)");
					if outgoing_v.contains_key(&edge.to) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 {
						trace!("Constraint {edge:?} is falsified since inverse is implied");
						self.close_imp_edge(adapter.get_trailing_actions(), e);
						let result = self.inc_sat(adapter, e)?;  // TODO could also try these ones lazy? Or keep track of path in dijkstra relevant?
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		} else {
			for &n in outgoing_v.keys() {
				for i in self.open_out[n].open_iter(adapter.get_trailing_actions()) {
					let &e = self.open_out[n].index(adapter.get_trailing_actions(), i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, implied)");
					if incoming_u.contains_key(&edge.to) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint {:?} is implied", edge);
						self.close_imp_edge(adapter.get_trailing_actions(), e);
					}
				}
				for i in self.open_in[n].open_iter(adapter.get_trailing_actions()) {
					let &e = self.open_in[n].index(adapter.get_trailing_actions(), i);
					let edge = &self.edges[e];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, reverse)");
					if incoming_u.contains_key(&edge.from) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 {
						trace!("Constraint {:?} is falsified since inverse is implied", edge);
						self.close_imp_edge(adapter.get_trailing_actions(), e);
						let result = self.inc_sat(adapter, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		}

		Ok(())
	}

	/// Perform incremental updates of lower bounds.
	fn inc_lb<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, v_l: &mut IndexSet<usize>) -> Result<(), E> {  // TODO unit tests

		trace!("Running inc_lb on int vars {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|&n| {
			adapter.get_int_lower_bound(n) + self.pi[n]
		}).max().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_l.iter() {
			let _ = queue.push(n, Reverse(pi0 - adapter.get_int_lower_bound(n) - self.pi[n]));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			if bound > self.get_cur_lower_bound(adapter, s) || v_l.contains(&s) {
				self.update_lb(s, bound);
				if bound > adapter.get_int_lower_bound(s) {
					trace!("Updating lower bound for i{:?} to {bound}", s);
					let (prev, b) = self.backtrace[s].unwrap();
					adapter.set_int_lower_bound(s, bound, b, prev, self.get_cur_lower_bound(adapter, prev))?;
					let _ = v_l.insert(s);
				}
				for &e in self.active_out[s].iter(adapter.get_trailing_actions()) {
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
	fn inc_ub<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, v_u: &mut IndexSet<usize>) -> Result<(), E> {  // TODO unit tests

		trace!("Running inc_ub on int vars {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|&n| {
			adapter.get_int_upper_bound(n) + self.pi[n]
		}).min().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_u.iter() {
			let _ = queue.push(n, Reverse(self.pi[n] + adapter.get_int_upper_bound(n) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			if bound < self.get_cur_upper_bound(adapter, s) || v_u.contains(&s) {
				self.update_ub(s, bound);
				if bound < adapter.get_int_upper_bound(s) {
					trace!("Updating upper bound for i{:?} to {bound}", s);
					let (prev, b) = self.backtrace[s].unwrap();
					adapter.set_int_upper_bound(s, bound, b, prev, self.get_cur_upper_bound(adapter, prev))?;
					let _ = v_u.insert(s);
				}
				for &e in self.active_in[s].iter(adapter.get_trailing_actions()) {
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

	/// Propagate new bounds.
	fn propagate_bounds<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, lower_bound_changes: &mut IndexSet<usize>, upper_bound_changes: &mut IndexSet<usize>) -> Result<(), E> {
		
		trace!("Propagating bounds on lb changes {:?}, ub changes {:?}.", lower_bound_changes, upper_bound_changes);

		// Lower bound updates
		if !lower_bound_changes.is_empty() {
			self.inc_lb(adapter, lower_bound_changes)?;
		}

		// Upper bound updates
		if !upper_bound_changes.is_empty() {
			self.inc_ub(adapter, upper_bound_changes)?;
		}

		// Consequences of lower bound updates on open implied constraints
		for &n in lower_bound_changes.iter() {
			let lb = self.lower_bound[n].unwrap();

			for i in self.open_out[n].open_iter(adapter.get_trailing_actions()) {
				let &e = self.open_out[n].index(adapter.get_trailing_actions(), i);
				let edge = &self.edges[e];
				let target_ub = self.get_cur_upper_bound(adapter, edge.to);
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} is falsified by bounds.", edge);
					// Lower bound is lifted
					adapter.set_bool_false(edge.bool_var, e, false)?;
					self.close_imp_edge(adapter.get_trailing_actions(), e);
				}
			}

			for i in self.open_in[n].open_iter(adapter.get_trailing_actions()) {
				let &e = self.open_in[n].index(adapter.get_trailing_actions(), i);
				let edge = &self.edges[e];
				if self.get_cur_upper_bound(adapter, edge.from) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} is implied by bounds.", edge);
					self.close_imp_edge(adapter.get_trailing_actions(), e);
				}
			}
		}

		// Consequences of upper bound updates on open implied constraints
		for &n in upper_bound_changes.iter() {
			let ub = self.upper_bound[n].unwrap();

			for i in self.open_out[n].open_iter(adapter.get_trailing_actions()) {
				let &e = self.open_out[n].index(adapter.get_trailing_actions(), i);
				let edge = &self.edges[e];
				if ub - self.get_cur_lower_bound(adapter, edge.to) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} is implied by bounds.", edge);
					self.close_imp_edge(adapter.get_trailing_actions(), e);
				}
			}

			for i in self.open_in[n].open_iter(adapter.get_trailing_actions()) {
				let &e = self.open_in[n].index(adapter.get_trailing_actions(), i);
				let edge = &self.edges[e];
				let source_lb = self.get_cur_lower_bound(adapter, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} is falsified by bounds.", edge);
					// Upper bound is lifted
					adapter.set_bool_false(edge.bool_var, e, true)?;
					self.close_imp_edge(adapter.get_trailing_actions(), e);
				}
			}
		}

		Ok(())
		
	}

	/// Propagate the addition of an edge, checking for conflicts and implications.
	fn propagate_edge_addition<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, e: usize, check_implied: bool, update_local_bounds: bool) -> Result<(), E> {
		// If the edge can't be added, a conflict will be generated
		let result = self.inc_sat(adapter, e)?;
		debug_assert!(result, "Adding {e} should be possible or cause a conflict!");
		if check_implied {
			// If the edge was added, check the status of open edges.
			self.inc_imp(adapter, e)?;
		}
		let edge = &self.edges[e];
		let source_lb = self.get_cur_lower_bound(adapter, edge.from);
		let lb_y = source_lb - edge.val;
		if lb_y > self.get_cur_lower_bound(adapter, edge.to) {
			// New edge caused lower bound change.
			adapter.set_int_lower_bound(edge.to, lb_y, edge.bool_var, edge.from, source_lb)?;
            if update_local_bounds {
                self.update_lb(edge.to, lb_y);
            }
		}
		let edge = &self.edges[e];
		let target_ub = self.get_cur_upper_bound(adapter, edge.to);
		let ub_x = target_ub + edge.val;
		if ub_x < self.get_cur_upper_bound(adapter, edge.from) {
			// New edge caused upper bound change.
			adapter.set_int_upper_bound(edge.from, ub_x, edge.bool_var, edge.to, target_ub)?;
            if update_local_bounds {
                self.update_ub(edge.from, ub_x);
            }
		}
		Ok(())
	}

	/// Propagate fixed booleans.
	fn propagate_booleans<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, fixed_bools: &IndexSet<usize>, check_implied: bool, update_local_bounds: bool) -> Result<(), E> {
		
		trace!("Propagating fixed booleans {:?}.", fixed_bools);
		for &b in fixed_bools.iter() {
			let val = adapter.get_bool_val(b).unwrap();
			trace!("Boolean b{b:?} fixed to {val}");
			if val {
				// Consequences of setting the boolean to true -> add all implied edges.
				if self.bool_active[b] {
					for i in self.bool_implications[b].open_iter(adapter.get_trailing_actions()) {
						if let Some(&e) = self.bool_implications[b].index_opt(adapter.get_trailing_actions(), i) {
							trace!("Processing adding edge {:?}", self.edges[e]);
							self.close_imp_edge(adapter.get_trailing_actions(), e);
							self.activate_imp_edge(adapter.get_trailing_actions(), e);
							self.propagate_edge_addition(adapter, e, check_implied, update_local_bounds)?;
						}
					}
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				if self.bool_active[b] {
					for i in self.bool_implications[b].open_iter(adapter.get_trailing_actions()) {
						let &e = self.bool_implications[b].index(adapter.get_trailing_actions(), i);
						trace!("Closing edge {:?})", self.edges[e]);
						self.close_imp_edge(adapter.get_trailing_actions(), e);
					}
				}
			}
		}

		Ok(())

	}
	
	/// Generate a dot presentation of the active graph.
	fn to_dot<E, A: ModelAdapter<E>>(&self, adapter: &mut A) -> String {
		let mut out = "digraph {\n".to_owned();
		for n in (0..self.num_nodes()).filter(|&n| self.active[n]) {
			out.push_str(format!("\"{:?}\" [label=\"{:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 n,
								 n,
								 self.get_cur_lower_bound(adapter, n),
								 self.get_cur_upper_bound(adapter, n),
								 self.pi[n]).as_str());
			for &e in self.active_out[n].iter(adapter.get_trailing_actions()) {
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

#[derive(Debug, PartialEq, Eq)]
/// A model adapter using [PropagationActions], [IntView], and [BoolView] for use during solving.
struct SolverModelAdapter<'a, P> {
	actions: &'a mut P,
	int_vars: &'a Vec<IntView>,
	bool_vars: &'a Vec<BoolView>,
}

impl<'a, P: PropagationActions> SolverModelAdapter<'a, P> {

	fn new(actions: &'a mut P, int_vars: &'a Vec<IntView>, bool_vars: &'a Vec<BoolView>) -> Self {
		Self {
			actions,
			int_vars,
			bool_vars,
		}
	}

}

impl<P: PropagationActions> ModelAdapter<Conflict> for SolverModelAdapter<'_, P> {

	fn get_int_lower_bound(&self, v: usize) -> IntVal {
		self.actions.get_int_lower_bound(self.int_vars[v])
	}

	fn set_int_lower_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal) -> Result<(), Conflict> {
		self.actions.set_int_lower_bound(self.int_vars[v], value,
										 |a: &mut P| vec![bool_var.map_or(BoolView::from(true), |i| self.bool_vars[i]),
														  a.get_int_lit(self.int_vars[lb_var], IntLitMeaning::GreaterEq(lb_val))])?;
		Ok(())
	}

	fn get_int_upper_bound(&self, v: usize) -> IntVal {
		self.actions.get_int_upper_bound(self.int_vars[v])
	}

	fn set_int_upper_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, ub_var: usize, ub_val: IntVal) -> Result<(), Conflict> {
		self.actions.set_int_upper_bound(self.int_vars[v], value,
										 |a: &mut P| vec![bool_var.map_or(BoolView::from(true), |i| self.bool_vars[i]),
														  a.get_int_lit(self.int_vars[ub_var], IntLitMeaning::Less(ub_val + 1))])?;
		Ok(())
	}

	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions {
		self.actions
	}

	fn get_bool_val(&self, v: usize) -> Option<bool> {
		self.actions.get_bool_val(self.bool_vars[v])
	}

	fn process_negative_cycle(&mut self, var: Option<usize>, reason: Vec<usize>) -> Result<(), Conflict> {
		let var = var.map_or(BoolView::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var, reason.into_iter().map(|i| self.bool_vars[i]).collect_vec())?;
		Ok(())
	}

	fn set_bool_false(&mut self, bool_var: Option<usize>, edge: usize, lb_fixed: bool) -> Result<(), Conflict> {
		let var = bool_var.map_or(BoolView::from(true), |i| self.bool_vars[i]);
		let data = if lb_fixed {
			edge as u64
		} else {
			-(edge as i64) as u64
		};
		self.actions.set_bool(!var, self.actions.deferred_reason(data))?;
		Ok(())
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Bounds consistent global difference constraint propagator.
pub struct DifferenceLogicBounds {
	/// Integer variables.
	int_vars: Vec<IntView>,
	/// Boolean variables.
	bool_vars: Vec<BoolView>,
	/// Shared reference to difference logic graph
	graph: Rc<RefCell<DifferenceLogicGraph>>,
	/// List of integer variable indices with reported lower bound changes.
	lower_bound_changes: IndexSet<usize>,
	/// List of integer variable indices with reported upper bound changes.
	upper_bound_changes: IndexSet<usize>,
}

impl DifferenceLogicBounds {

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<I: PropagatorInitActions + ?Sized>(solver: &mut I,
													 int_vars: &Vec<IntView>,
													 bool_vars: &Vec<BoolView>,
													 priority_level: PriorityLevel,
													 graph: Rc<RefCell<DifferenceLogicGraph>>) {

		let graph_ref = graph.borrow();
		let node_active = (0..graph_ref.num_nodes()).into_iter().filter(|&n| graph_ref.active[n]).collect_vec();
		let bool_active = (0..graph_ref.bool_implications.len()).into_iter().filter(|&b| graph_ref.bool_active[b]).collect_vec();
		trace!("Creating bounds propagator for {} int and {} bool vars", node_active.len(), bool_active.len());

		let prop = solver.add_propagator(
			Box::new(Self {
				int_vars: int_vars.clone(),
				bool_vars: bool_vars.clone(),
				graph: graph.clone(),
				lower_bound_changes: IndexSet::default(),
				upper_bound_changes: IndexSet::default(),
			}),
			priority_level,
		);

		for i in node_active.into_iter() {
			solver.advise_on_int_change(prop, int_vars[i], IntPropCond::Bounds, i as u64);
		}
		solver.advise_on_backtrack(prop);

	}

}

impl<P, E> Propagator<P, E> for DifferenceLogicBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{

	fn advise_of_backtrack(&mut self, _actions: &mut E) {
		trace!("Backtrack advise");
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		self.graph.borrow_mut().reset_bounds();
	}

	fn advise_of_int_change(&mut self, actions: &mut E, view: IntView, event: IntEvent, data: u64) -> bool {
		let graph = self.graph.borrow_mut();
		let data = data as usize;
		let mut enqueue = false;
		if event == IntEvent::LowerBound || event == IntEvent::Fixed {
			if graph.lower_bound[data].map_or(true, |e| e < actions.get_int_lower_bound(view)) {
				trace!("Integer i{data} lower bound change.");
				enqueue = self.lower_bound_changes.insert(data);
			}
		}
		if event == IntEvent::UpperBound || event == IntEvent::Fixed {
			if graph.upper_bound[data].map_or(true, |e| e > actions.get_int_upper_bound(view)) {
				trace!("Integer i{data} upper bound change.");
				enqueue |= self.upper_bound_changes.insert(data);
			}
		}
		enqueue
	}

	#[tracing::instrument(name = "difference_logic_bounds", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut model_adapter = SolverModelAdapter::new(actions, &self.int_vars, &self.bool_vars);
		self.graph.borrow_mut().propagate_bounds(&mut model_adapter, &mut self.lower_bound_changes, &mut self.upper_bound_changes)?;
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		Ok(())
	}

	fn explain(&mut self, actions: &mut E, _lit: Option<RawLit>, data: u64) -> Conjunction {
		let signed_data = data as i64;
		let views = if signed_data < 0 {
			let edge = &self.graph.borrow().edges[-signed_data as usize];
			let target_ub = actions.get_int_upper_bound(self.int_vars[edge.to]);
			let (lit_lb, IntLitMeaning::GreaterEq(meaning_lb)) = actions.get_int_lit_relaxed(self.int_vars[edge.from], IntLitMeaning::GreaterEq(target_ub + edge.val + 1)) else {
				unreachable!("IntLitMeaning should always be GreaterEq");
			};
			vec![lit_lb, actions.get_int_lit_relaxed(self.int_vars[edge.to], IntLitMeaning::Less(max(target_ub + 1, meaning_lb - edge.val))).0]
		} else {
			let edge = &self.graph.borrow().edges[signed_data as usize];
			let source_lb = actions.get_int_lower_bound(self.int_vars[edge.from]);
			let (lit_ub, IntLitMeaning::Less(meaning_ub)) = actions.get_int_lit_relaxed(self.int_vars[edge.to], IntLitMeaning::Less(source_lb - edge.val)) else {
				unreachable!("IntLitMeaning should always be Less");
			};
			vec![actions.get_int_lit_relaxed(self.int_vars[edge.from], IntLitMeaning::GreaterEq(min(source_lb, meaning_ub + edge.val))).0, lit_ub]
		};
		trace!("Explaining {data} with {views:?}");
		views.iter()
			.filter_map(|bv| match bv.0 {
				BoolViewInner::Lit(l) => Some(l),
				BoolViewInner::Const(true) => None,
				BoolViewInner::Const(false) => {
					unreachable!(
						"Unexpected false literal in the explanation of an edge falsified by bounds."
					)
				}
			})
			.collect()  // TODO should this be global? (same as in other propagator)
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Difference constraint boolean propagator.
pub struct DifferenceLogicBooleans {
	/// Integer variables.
	int_vars: Vec<IntView>,
	/// Boolean variables.
	bool_vars: Vec<BoolView>,
	/// Shared reference to difference logic graph
	graph: Rc<RefCell<DifferenceLogicGraph>>,
	/// List of boolean variable indices that have recently been reported as fixed to true.
	fixed_bools: IndexSet<usize>,
	/// Whether to proactively check implied constraints.
	use_inc_imp: bool,
}

impl DifferenceLogicBooleans {

	/// Create a new [`DifferenceLogicBooleans`] propagator and post it in the solver.
	pub fn new_in<I: PropagatorInitActions + ?Sized>(solver: &mut I,
													 int_vars: &Vec<IntView>,
													 bool_vars: &Vec<BoolView>,
													 priority_level: PriorityLevel,
													 use_inc_imp: bool,
													 graph: Rc<RefCell<DifferenceLogicGraph>>) {

		let graph_ref = graph.borrow();
		let node_active = (0..graph_ref.num_nodes()).into_iter().filter(|&n| graph_ref.active[n]).collect_vec();
		let bool_active = (0..graph_ref.bool_implications.len()).into_iter().filter(|&b| graph_ref.bool_active[b]).collect_vec();
		trace!("Creating boolean propagator for {} int and {} bool vars", node_active.len(), bool_active.len());

		let prop = solver.add_propagator(
			Box::new(Self {
				int_vars: int_vars.clone(),
				bool_vars: bool_vars.clone(),
				graph: graph.clone(),
				fixed_bools: IndexSet::default(),
				use_inc_imp,
			}),
			priority_level,
		);

		for i in bool_active.into_iter() {
			solver.advise_on_bool_change(prop, bool_vars[i], i as u64);
		}
		solver.advise_on_backtrack(prop);

	}

}

impl<P, E> Propagator<P, E> for DifferenceLogicBooleans
where
	P: PropagationActions,
	E: ExplanationActions,
{

	fn advise_of_backtrack(&mut self, _actions: &mut E) {
		trace!("Backtrack advise");
		self.fixed_bools.clear();
	}

	fn advise_of_bool_change(&mut self, _actions: &mut E, _view: BoolView, data: u64) -> bool {
		trace!("Boolean b{data} fixed.");
		self.fixed_bools.insert(data as usize)
	}

	#[tracing::instrument(name = "difference_logic_booleans", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut model_adapter = SolverModelAdapter::new(actions, &self.int_vars, &self.bool_vars);
		self.graph.borrow_mut().propagate_booleans(&mut model_adapter, &self.fixed_bools, self.use_inc_imp, false)?;
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
	graph: Rc<RefCell<DifferenceLogicGraph>>,
	/// The start of the unfixed variables in `int_vars`.
	next: TrailedInt,
	/// Whether to minimize or maximize
	minimize: bool,
}

impl DiffLogicBrancher {

	/// Create a new [`DiffLogicBrancher`]  and add to the end of the branching queue in the solver.
	pub fn new_in<I: BrancherInitActions + ?Sized>(solver: &mut I,
												   int_vars: &Vec<IntView>,
												   bool_vars: &Vec<BoolView>,
												   graph: Rc<RefCell<DifferenceLogicGraph>>,
												   minimize: bool) {

		trace!("Creating diff logic brancher");

		let next = solver.new_trailed_int(0);
		solver.push_brancher(Box::new(DiffLogicBrancher {
			int_vars: int_vars.clone(),
			int_var_index: (0..int_vars.len()).into_iter().collect_vec(),
			bool_vars: bool_vars.clone(),
			graph: graph.clone(),
			next,
			minimize,
		}));

	}

}

impl<D: DecisionActions> Brancher<D> for DiffLogicBrancher {
	fn decide(&mut self, actions: &mut D) -> Decision {
		let mut begin = actions.get_trailed_int(self.next) as usize;

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
				if actions.get_int_lower_bound(self.int_vars[index]) == actions.get_int_upper_bound(self.int_vars[index]) || graph.decision_bools[index].peek(actions).is_none() {
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
						(actions.get_int_lower_bound(self.int_vars[index]), -graph.decision_bools[index].peek(actions).map_or(IntVal::MAX, |(_, val)| *val))
					} else {
						(-actions.get_int_upper_bound(self.int_vars[index]), graph.decision_bools[index].peek(actions).map_or(IntVal::MIN, |(_, val)| *val))
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
				if actions.get_bool_val(self.bool_vars[*b]).is_some() {
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

	use crate::constraints::difference_logic::{DiffEdge, DifferenceLogicModel, DifferenceLogicConstraint, DifferenceLogicGraph, ModelAdapter, SolverModelAdapter, DifferenceLogicCollection};
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, IntDecision, Model};
	use crate::actions::{SimplificationActions, TrailingActions};
	use crate::constraints::Constraint;
	use crate::helpers::initial_trail::InitialTrail;
	use crate::helpers::linear_transform::LinearTransform;
	use crate::reformulate::{InitConfig, IntDecisionInner, ReformulationContext};
	use crate::solver::IntView;
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
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len(), bool_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
  		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		for (x, y, d) in vec![(0, 1, 1), (0, 2, 1), (0, 4, 1),
							  (1, 4, 1), (1, 5, 1), (2, 4, 1), (3, 4, 1), (3, 5, 1),
							  (4, 6, 1), (4, 8, 1),
							  (5, 6, 1), (5, 7, 1), (5, 8, 1), (5, 9, 1),
							  (7, 9, 1), (8, 9, 1)] {
			let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(x, y, d, None));
		}
		let new_index = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(4, 5, 1, Some(0)));

		let outgoing_x = graph.dijkstra_relevant(&mut model_adapter, new_index, false);
		trace!("{:?}", outgoing_x);
		assert_eq!(outgoing_x.len(), 2);
		assert!(outgoing_x.contains_key(&5));
		assert!(outgoing_x.contains_key(&7));
		let incoming_y = graph.dijkstra_relevant(&mut model_adapter, new_index, true);
		trace!("{:?}", incoming_y);
		assert_eq!(incoming_y.len(), 2);
		assert!(incoming_y.contains_key(&2));
		assert!(incoming_y.contains_key(&4));
	}

	#[test]
	#[traced_test]
	fn test_inc_imp() {
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
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len(), bool_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 1, 2, Some(2)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap().lit,
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert_eq!(graph.open_out[2].num_open(&ctx), 1);
		assert_eq!(graph.open_in[2].num_open(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_inc_imp2() {
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
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len(), bool_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let mut dummy_actions = DummyActions;
		let mut engine = slv.engine.borrow_mut();
		let mut ctx = SolvingContext::new(&mut dummy_actions, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 3, 2, Some(3)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap().lit,
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert!(ctx.get_bool_val(bool_vars[3]).is_none());
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_err());
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[3].0 else {
			panic!("Should not happen");
		};
		assert!(prb.unify_int(int_vars[0], IntDecision(IntDecisionInner::Linear(LinearTransform {scale: NonZero::new(2).unwrap(), offset: 1}, var_index))).is_ok());
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[2].0 else {
			panic!("Should not happen");
		};
		assert!(prb.unify_int(int_vars[0], IntDecision(IntDecisionInner::Linear(LinearTransform::offset(1), var_index))).is_ok());
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
		let mut diff_logic_model = diff_logic.process(&mut prb, LEVEL);
		assert!(diff_logic_model.simplify(&mut prb).is_ok());
		assert!(prb.unify_int(int_vars[0], IntDecision::from(5)).is_ok());
		assert!(prb.unify_int(int_vars[2], IntDecision::from(5)).is_ok());
		assert!(diff_logic_model.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
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
