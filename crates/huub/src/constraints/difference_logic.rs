//! Structure and algorithms for a global difference logic propagator.

use std::cell::RefCell;
use std::cmp::Reverse;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::iter::once;
use std::rc::Rc;
use pindakaas::propositional_logic::Formula;
use rustc_hash::FxBuildHasher;
use tracing::trace;
use crate::solver::activation_list::IntPropCond;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, IntDecision, IntVal, Model};
use crate::actions::TrailingActions;
use crate::helpers::initial_trail::InitialTrail;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::{TrailedOpenList, TrailedOpenListIterator};
use crate::solver::trail::TrailedInt;

// Redefine hash-based types using the fast FxBuildHasher.
type IndexSet<T> = indexmap::IndexSet<T, FxBuildHasher>;
type IndexMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;
type PriorityQueue<I, P> = priority_queue::PriorityQueue<I, P, FxBuildHasher>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Different types of (potential) difference logic constraints.
pub enum DifferenceLogicConstraint {
	/// A globally active difference constraint:x - y <= d
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of set of potential difference constraints within a model.
pub struct DifferenceLogic {
	/// Priority of the difference logic propagator
	priority_level: PriorityLevel,
	/// List of raw potential difference constraints.
	raw_constraints: Vec<DifferenceLogicConstraint>,
	/// List of global difference constraints to post to the solver.
	global_constraints: Vec<(IntDecision, IntDecision, IntVal)>,
	/// List of implied difference constraints to post to the solver.
	imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
}

/// Transform an implied not equals constraint to implied difference constraints by introducing 3 new boolean decision variables.
fn add_implied_not_equals(imp_constraints: &mut Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>, model: &mut Model, b: BoolDecision, x: IntDecision, y: IntDecision, d: IntVal) {
	let decision1 = model.new_bool_var();
	let decision2 = model.new_bool_var();
	*model += Formula::Or(vec![Formula::from(!b), Formula::from(decision1), Formula::from(decision2)]);
	*model += Formula::Or(vec![Formula::from(!decision1), Formula::from(!decision2)]);
	imp_constraints.push((decision1, x, y, d - 1));
	imp_constraints.push((decision2, y, x, -d - 1));
}

impl DifferenceLogic {
	
	pub(crate) fn new(priority_level: PriorityLevel) -> Self {
		Self {
			priority_level,
			raw_constraints: Vec::new(),
			global_constraints: Vec::new(),
			imp_constraints: Vec::new(),
		}
	}

	/// Add a raw difference constraint.
	pub(crate) fn add(&mut self, constraint: DifferenceLogicConstraint) {
		self.raw_constraints.push(constraint);
	}

	/// Process the raw difference constraints, transform them to global and implied difference
	/// constraints and / or reemit them as standalone constraints depending on the given level
	/// parameter (binary encoding).
	pub(crate) fn process(&mut self, model: &mut Model, level: u32) -> (usize, usize, usize, usize) {
		for raw in self.raw_constraints.iter() {
			match raw {
				// Always post global, implied, and reified constraints TODO could check if they are isolated etc?
				DifferenceLogicConstraint::Global(x, y, d) => self.global_constraints.push((*x, *y, *d)),
				DifferenceLogicConstraint::Implied(b, x, y, d) => self.imp_constraints.push((*b, *x, *y, *d)),
				DifferenceLogicConstraint::Reified(b, x, y, d) => {
					self.imp_constraints.push((*b, *x, *y, *d));
					self.imp_constraints.push((!*b, *y, *x, -*d - 1));
				},
				// b -> x - y == d is transformed to b -> x - y <= d and b -> x - y >= d.
				DifferenceLogicConstraint::ImpliedEquals(b, x, y, d) => {
					if level & 0b1 > 0 {
						self.imp_constraints.push((*b, *x, *y, *d));
						self.imp_constraints.push((*b, *y, *x, -*d));
					}
					if level & 0b1 == 0 || level & 0b10 > 0 {
						*model += (*x - *y).eq(*d).implied_by(*b);
					}
				},
				// x - y != d is transformed to b -> x - y < d and !b -> x - y > d for a new boolean variable b.
				DifferenceLogicConstraint::NotEquals(x, y, d) => {
					if level & 0b100 > 0 {
						let decision = model.new_bool_var();
						self.imp_constraints.push((decision, *x, *y, *d - 1));
						self.imp_constraints.push((!decision, *y, *x, -*d - 1));
					}
					if level & 0b100 == 0 || level & 0b1000 > 0 {
						*model += (*x - *y).ne(*d);
					}
				},
				// b -> x - y != d is transformed to b -> c \/ e; !c \/ !e; c -> x - y < d; e -> x - y > d for new boolean variables c and e.
				DifferenceLogicConstraint::ImpliedNotEquals(b, x, y, d) => {
					if level & 0b10_000 > 0 {
						add_implied_not_equals(&mut self.imp_constraints, model, *b, *x, *y, *d);
					}
					if level & 0b10_000 == 0 || level & 0b100_000 > 0 {
						*model += (*x - *y).ne(*d).implied_by(*b);
					}
				},
				// b <-> x - y == d is transformed to b -> x - y == d and !b -> x - y != d
				DifferenceLogicConstraint::ReifiedEquals(b, x, y, d) => {
					if level & 0b1000_000 > 0 {
						self.imp_constraints.push((*b, *x, *y, *d));
						self.imp_constraints.push((*b, *y, *x, -*d));
						add_implied_not_equals(&mut self.imp_constraints, model, !*b, *x, *y, *d);
					}
					if level & 0b1000_000 == 0 || level & 0b10_000_000 > 0 {
						*model += (*x - *y).eq(*d).reified_by(*b);
					}
				},
			}
		}
		self.output_statistics()
	}
	
	/// Return statistics of the captured difference logic constraints:
	/// (# integer variables, # boolean variables, # globally active constraints, # implied constraints)
	pub(crate) fn output_statistics(&self) -> (usize, usize, usize, usize) {
		let mut int_vars = IndexSet::default();
		let mut bool_vars = IndexSet::default();
		for &(x, y, _) in self.global_constraints.iter() {
			let _ = int_vars.insert(x);
			let _ = int_vars.insert(y);
		}
		for &(b, x, y, _) in self.imp_constraints.iter() {
			let _ = bool_vars.insert(b);
			let _ = int_vars.insert(x);
			let _ = int_vars.insert(y);
		}
		(int_vars.len(), bool_vars.len(), self.global_constraints.len(), self.imp_constraints.len())
	}
	
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// todo can we already do graph simplification here?
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		// todo do simplification first, then transform graph here
		trace!("DifferenceLogic to_solver with {} constraints and {} imp_constraints", self.global_constraints.len(), self.imp_constraints.len());
		let constraints: Vec<_> = self.global_constraints.iter()
			.map(|&(x, y, d)| (slv.get_solver_int(x), slv.get_solver_int(y), d))
			.collect();
		let imp_constraints: Vec<_> = self.imp_constraints.iter()
			.map(|&(b, x, y, d)| (slv.get_solver_bool(b), slv.get_solver_int(x), slv.get_solver_int(y), d))
			.collect();
		DifferenceLogicBounds::new_in(slv, self.priority_level, constraints, imp_constraints);
		Ok(())
	}
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
			out_index: 0,
			in_index: 0,
		}
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A node in the difference logic graph.
pub struct VarNode {
	/// List of active outgoing edges.
	edges: TrailedList<usize>,
	/// List of active incoming edges.
	reverse_edges: TrailedList<usize>,
	/// Potential function value.
	pi: IntVal,
	/// Backtrace for shortest path calculations.
	backtrace: Option<(usize, Option<usize>)>,
	/// Visited state.
	visited: bool,
	/// Updated lower bound.
	lower_bound: Option<IntVal>,
	/// Updated upper bound.
	upper_bound: Option<IntVal>,
	/// List of open outgoing edges.
	open_edges: TrailedOpenList<usize>,
	/// List of open incoming edges.
	open_reverse_edges: TrailedOpenList<usize>,
}

impl VarNode {

	fn new(initial_trail: &mut InitialTrail) -> Self {
		Self {
			edges: TrailedList::new(initial_trail),
			reverse_edges: TrailedList::new(initial_trail),
			pi: 0,
			backtrace: None,
			visited: false,
			lower_bound: None,
			upper_bound: None,
			open_edges: TrailedOpenList::new(initial_trail),
			open_reverse_edges: TrailedOpenList::new(initial_trail),
		}
	}

	/// Initialize the trailed infrastructure for this node.
	fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		self.edges.init_trail(initial_trail);
		self.reverse_edges.init_trail(initial_trail);
		self.open_edges.init_trail(initial_trail);
		self.open_reverse_edges.init_trail(initial_trail);
	}

}

#[derive(Clone, PartialEq, Eq)]
/// A hashable reference to a node in the difference logic graph.
pub struct VarNodeRef {  // todo deal with the case that a node represents multiple vars! code_generation: var + linear transform are both in the graph. Could also be vars that are equal on the root node or similar structures!
	/// Variable index associated with the node.
	var: usize,
	/// Reference to the node.
	node: Rc<RefCell<VarNode>>,
}

impl VarNodeRef {
	fn new(initial_trail: &mut InitialTrail, var: usize) -> Self {
		Self {
			var,
			node: Rc::new(RefCell::new(VarNode::new(initial_trail))),
		}
	}
}

impl Debug for VarNodeRef {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("VarNodeRef")
			.field("var", &self.var)
			.finish()
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A graph of difference constraints.
pub struct DifferenceLogicGraph {
	/// List of all nodes in the graph.
	nodes: Vec<VarNodeRef>,
	/// List of all edges in the graph. todo could make this a trailed list for dynamic addition
	edges: Vec<DiffEdge>,
	/// Storage for the visited state.
	visited: Vec<usize>,
	/// Number of open implication edges.
	open_imp_edges: TrailedInt,
}

impl DifferenceLogicGraph {

	fn new(initial_trail: &mut InitialTrail, int_vars: usize) -> Self {
		Self {
			nodes: (0..int_vars).into_iter().map(|v| VarNodeRef::new(initial_trail, v)).collect(),
			edges: Vec::new(),
			visited: Vec::new(),
			open_imp_edges: initial_trail.new_trailed_int(0),
		}
	}

	/// Initialize the trailed infrastructure for this graph.
	fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		for node in self.nodes.iter() {
			node.node.borrow_mut().init_trail(initial_trail);
		}
		self.open_imp_edges = initial_trail.map_to_trail(self.open_imp_edges);
	}

	/// Add a new globally active edge to the graph, return the index.
	fn new_edge<A: ModelAdapter>(&mut self, adapter: &mut A, edge: DiffEdge) -> usize {
		let index = self.edges.len();
		self.nodes[edge.from].node.borrow_mut().edges.push(adapter.get_trailing_actions(), index);
		self.nodes[edge.to].node.borrow_mut().reverse_edges.push(adapter.get_trailing_actions(), index);
		self.edges.push(edge);
		index
	}

	/// Add a new open implied edge to the graph, return the index.
	fn new_imp_edge<A: ModelAdapter>(&mut self, adapter: &mut A, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		let mut from = self.nodes[edge.from].node.borrow_mut();
		edge.out_index = from.open_edges.len();
		from.open_edges.push(self.edges.len());
		let mut to = self.nodes[edge.to].node.borrow_mut();
		edge.in_index = to.open_reverse_edges.len();
		to.open_reverse_edges.push(self.edges.len());
		self.edges.push(edge);
		let actions = adapter.get_trailing_actions();
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) + 1);
		index
	}

	/// Activate the implied edge given by the index.
	fn activate_imp_edge<A: ModelAdapter>(&self, adapter: &mut A, index: usize) {
		let edge = &self.edges[index];
		self.nodes[edge.from].node.borrow_mut().edges.push(adapter.get_trailing_actions(), index);
		self.nodes[edge.to].node.borrow_mut().reverse_edges.push(adapter.get_trailing_actions(), index);
	}

	/// Close the implied edge given by the index.
	/// Return true if the edge got closed by this call, false if it was already closed.
	fn close_imp_edge<A: ModelAdapter>(&mut self, adapter: &mut A, index: usize) -> bool {
		let &from = &self.edges[index].from;
		let &to = &self.edges[index].to;
		let out_index = self.edges[index].out_index;
		let in_index = self.edges[index].in_index;
		let actions = adapter.get_trailing_actions();
		let was_open = self.nodes[from].node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i) &&
			self.nodes[to].node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		if was_open {
			let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
		}
		was_open
	}

	/// Close the implied edge given by the index while iterating open edges in forward direction.
	fn close_imp_edge_forward<A: ModelAdapter>(&mut self, adapter: &mut A, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = open.close(actions, |&e, i| self.edges[e].out_index = i);
		let &to = &self.edges[index].to;
		let in_index = self.edges[index].in_index;
		let _ = self.nodes[to].node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
	}

	/// Close the implied edge given by the index while iterating open edges in backward direction.
	fn close_imp_edge_backward<A: ModelAdapter>(&mut self, adapter: &mut A, rev_open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = rev_open.close(actions, |&e, i| self.edges[e].in_index = i);
		let &from = &self.edges[index].from;
		let out_index = self.edges[index].out_index;
		let _ = self.nodes[from].node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i);
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
	}

	/// Mark the given node as visited.
	fn visit(&mut self, node: usize) {
		self.nodes[node].node.borrow_mut().visited = true;
		self.visited.push(node);
	}

	/// Reset the visited state of all nodes.
	fn reset_visit(&mut self) {
		for &node in self.visited.iter() {
			self.nodes[node].node.borrow_mut().visited = false;
		}
		self.visited.clear();
	}

	/// Get the current lower bound for the node, either stored or from the search.
	fn get_cur_lower_bound<A: ModelAdapter>(&self, adapter: &A, v: usize) -> IntVal {
		match self.nodes[v].node.borrow().lower_bound {
			Some(lb) => lb,
			None => adapter.get_int_lower_bound(v),
		}
	}

	/// Update the stored lower bound for the node.
	fn update_lb(&self, node: usize, val: IntVal, lb_updates: &mut Vec<usize>) {
		self.nodes[node].node.borrow_mut().lower_bound = Some(val);
		lb_updates.push(node);
	}

	/// Reset stored lower bounds of all nodes.
	fn reset_lb_updates(&self, lb_updates: &mut Vec<usize>) {
		for &node in lb_updates.iter() {
			self.nodes[node].node.borrow_mut().lower_bound = None;
		}
		lb_updates.clear();
	}

	/// Get the current upper bound for the node, either stored or from the search.
	fn get_cur_upper_bound<A: ModelAdapter>(&self, adapter: &A, v: usize) -> IntVal {
		match self.nodes[v].node.borrow().upper_bound {
			Some(ub) => ub,
			None => adapter.get_int_upper_bound(v),
		}
	}

	/// Update the stored upper bound for the node.
	fn update_ub(&mut self, node: usize, val: IntVal, ub_updates: &mut Vec<usize>) {
		self.nodes[node].node.borrow_mut().upper_bound = Some(val);
		ub_updates.push(node);
	}

	/// Reset stored upper bounds of all nodes.
	fn reset_ub_updates(&mut self, ub_updates: &mut Vec<usize>) {
		for &node in ub_updates.iter() {
			self.nodes[node].node.borrow_mut().upper_bound = None;
		}
		ub_updates.clear();
	}

	/// Get the reason for a cycle of negative lengths (all booleans along the cycle).
	fn get_cycle_reason(&self, node: usize) -> Vec<usize> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = self.nodes[var].node.borrow().backtrace {
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
	fn inc_sat<A: ModelAdapter>(&mut self, adapter: &mut A, new_index: usize) -> Result<bool, Conflict> {

		let new_edge = &self.edges[new_index];
		let from = &self.nodes[new_edge.from];
		let to = &self.nodes[new_edge.to];
		trace!("Performing inc_sat on i{:?} - i{:?} <= {:?}", from.var, to.var, new_edge.val);
		let mut queue = PriorityQueue::default();
		let mut pi_new = IndexMap::default(); // todo Could be replaced by the visited state. Q1: Is state or map faster? Q2: Is keeping old pi in case of conflict better?
		to.node.borrow_mut().backtrace = None;
		let gamma_v = from.node.borrow().pi + new_edge.val - to.node.borrow().pi;
		if gamma_v < 0 {
			let _ = queue.push(new_edge.to, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&new_edge.from).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let node_s = &self.nodes[s].node.borrow();
			let _ = pi_new.insert(s, node_s.pi + gamma_s);
			for &index in node_s.edges.iter(adapter.get_trailing_actions()) {
				let edge = &self.edges[index];
				let mut node_t = self.nodes[edge.to].node.borrow_mut();
				if !pi_new.contains_key(&edge.to) {
					let gamma_t = pi_new[&s] + edge.val - node_t.pi;
					if gamma_t < 0 {
						let old = queue.push_increase(edge.to, Reverse(gamma_t));
						if old.map_or(true, |Reverse(old_gamma)| gamma_t < old_gamma) {
							node_t.backtrace = Some((s, edge.bool_var));
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
			self.nodes[var].node.borrow_mut().pi = val;
		}
		Ok(true)
	}

	/// Perform dijkstra from the given node to all relevant nodes in the graph, return a map of
	/// distances. Can be performed in forward or backward direction.
	fn dijkstra_relevant<A: ModelAdapter>(&mut self, adapter: &mut A, new_edge: usize, reverse: bool) -> IndexMap<usize, IntVal> {
		
		trace!("Starting relevant dijkstra for e{new_edge:?} in mode reverse={reverse}");
		self.reset_visit();
		let new_edge = &self.edges[new_edge];
		let origin = if reverse {new_edge.to} else {new_edge.from};
		let pi_origin = self.nodes[origin].node.borrow().pi;
		let relevant_target = if reverse {new_edge.from} else {new_edge.to};
		let mut distances = IndexMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = PriorityQueue::default();
		let _ = queue.push(origin, Reverse(0));
		let pi_relevant = self.nodes[relevant_target].node.borrow().pi;
		let _ = queue.push(relevant_target, Reverse(new_edge.val + if reverse { pi_relevant - pi_origin } else { pi_origin - pi_relevant }));
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			self.visit(s);
			let node_s = self.nodes[s].node.borrow();
			let s_relevant = distances.contains_key(&s);
			//trace!("dijkstra on current node {s:?} with dist {dist}");
			for &index in if reverse {node_s.reverse_edges.iter(adapter.get_trailing_actions())} else {node_s.edges.iter(adapter.get_trailing_actions())} {
				let edge = &self.edges[index];
				let target = if reverse {edge.from} else {edge.to};
				let node_t = self.nodes[target].node.borrow();
				let new_dist = dist + edge.val + if reverse {node_t.pi - node_s.pi} else {node_s.pi - node_t.pi};
				if !node_t.visited {
					let prev = queue.push_increase(target, Reverse(new_dist));
					// Cases where we want to propagate the relevancy of s to t:
					// - First path to t (equal to previous distance of infinity)
					// - Path to t with lower distance than before
					// - Path to t with same distance as before and s is not relevant (prefer irrelevancy in ties)
					if prev.map_or(true, |Reverse(old_dist)| new_dist < old_dist || (new_dist == old_dist && !s_relevant)) {
						if s_relevant || target == relevant_target {
							// Add new distance to the map, if key was not present before increase relevant count.
							//trace!("Target {target:?} set to relevant");
							if distances.insert(target, new_dist + if reverse {pi_origin - node_t.pi} else {node_t.pi - pi_origin}).is_none() {
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
	fn inc_imp<A: ModelAdapter>(&mut self, adapter: &mut A, new_index: usize) -> Result<(), Conflict> {
		
		if adapter.get_trailing_actions().get_trailed_int(self.open_imp_edges) == 0 {
			trace!("No open implications");
			return Ok(());
		}

		// Incoming paths to relevant nodes starting from u via uv.
		let incoming_u = self.dijkstra_relevant(adapter, new_index, false); // todo could store distances at nodes as well?
		trace!("incoming_u is {incoming_u:?}");
		// Outgoing paths from relevant nodes ending at v via uv.
		let outgoing_v = self.dijkstra_relevant(adapter, new_index, true);
		trace!("outgoing_v is {outgoing_v:?}"); // todo check how to include pi change check at this point?
		let indegree_u: usize = incoming_u.iter().map(|(&v, _)| self.nodes[v].node.borrow().open_reverse_edges.open_len(adapter.get_trailing_actions())).sum();
		let outdegree_v: usize = outgoing_v.iter().map(|(&v, _)| self.nodes[v].node.borrow().open_edges.open_len(adapter.get_trailing_actions())).sum();
		trace!("indegree: {indegree_u:?}, outdegree: {outdegree_v:?}");
		
		let new_edge_val = self.edges[new_index].val;
		let mut fail_indices = Vec::new();
		
		if indegree_u < outdegree_v {
			for &var in incoming_u.keys() {
				let temp_node = self.nodes[var].clone();
				let mut node = temp_node.node.borrow_mut();
				let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = rev_open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, implied)");
					if outgoing_v.contains_key(&edge.from) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint i{:?} - i{:?} <= {} is implied", edge.from, edge.to, edge.val);
						self.close_imp_edge_backward(adapter, &mut rev_open, index);
					}
				}
				let mut open = node.open_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, reverse)");
					if outgoing_v.contains_key(&edge.to) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 { // todo slight double work for reified constraints
						trace!("Constraint i{:?} - i{:?} <= {} is falsified since inverse is implied", edge.from, edge.to, edge.val);
						fail_indices.push(index);
						self.close_imp_edge_forward(adapter, &mut open, index);
					}
				}
			}
		} else {
			for &var in outgoing_v.keys() {
				let temp_node = self.nodes[var].clone();
				let mut node = temp_node.node.borrow_mut();
				let mut open = node.open_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, implied)");
					if incoming_u.contains_key(&edge.to) && outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val {
						trace!("Constraint i{:?} - i{:?} <= {} is implied", edge.from, edge.to, edge.val);
						self.close_imp_edge_forward(adapter, &mut open, index);
					}
				}
				let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = rev_open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, reverse)");
					if incoming_u.contains_key(&edge.from) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 { // todo slight double work for reified constraints
						trace!("Constraint i{:?} - i{:?} <= {} is falsified since inverse is implied", edge.from, edge.to, edge.val);
						fail_indices.push(index);
						self.close_imp_edge_backward(adapter, &mut rev_open, index);
					}
				}
			}
		}

		for index in fail_indices {  // todo check if we want this here or immediately inside the loops?
			let _ = self.inc_sat(adapter, index)?;
		}

		Ok(())
	}

	/// Perform incremental updates of lower bounds.
	fn inc_lb<A: ModelAdapter>(&mut self, adapter: &mut A, v_l: &IndexSet<usize>, lb_updates: &mut Vec<usize>) -> Result<(), Conflict> {

		trace!("Running inc_lb on int vars {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|&n| {
			adapter.get_int_lower_bound(n) + self.nodes[n].node.borrow().pi
		}).max().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_l.iter() {
			// Min value indicates that successors still need to be considered.
			self.update_lb(n, IntVal::MIN, lb_updates);
			let _ = queue.push(n, Reverse(pi0 - adapter.get_int_lower_bound(n) - self.nodes[n].node.borrow().pi));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let ref_s = &self.nodes[s];
			let bound = pi0 - gamma_s - ref_s.node.borrow().pi;
			if bound > self.get_cur_lower_bound(adapter, s) {
				self.update_lb(s, bound, lb_updates);
				let node_s = ref_s.node.borrow();
				if bound > adapter.get_int_lower_bound(s) {
					trace!("Updating lower bound for i{:?} to {bound}", ref_s.var);
					let (prev, b) = node_s.backtrace.unwrap();
					adapter.set_int_lower_bound(s, bound, b, self.nodes[prev].var, self.get_cur_lower_bound(adapter, prev))?;
				}
				for &index in node_s.edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[index];
					let mut node_t = self.nodes[edge.to].node.borrow_mut();
					if !node_t.visited {
						let path = gamma_s + node_s.pi + edge.val - node_t.pi;
						let old = queue.push_increase(edge.to, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							node_t.backtrace = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Perform incremental updates of upper bounds.
	fn inc_ub<A: ModelAdapter>(&mut self, adapter: &mut A, v_u: &IndexSet<usize>, ub_updates: &mut Vec<usize>) -> Result<(), Conflict> {

		trace!("Running inc_ub on int vars {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|&n| {
			adapter.get_int_upper_bound(n) + self.nodes[n].node.borrow().pi
		}).min().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_u.iter() {
			// Max value indicates that predecessors still need to be considered.
			self.update_ub(n, IntVal::MAX, ub_updates);
			let _ = queue.push(n, Reverse(self.nodes[n].node.borrow().pi + adapter.get_int_upper_bound(n) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let ref_s = self.nodes[s].clone();
			let bound = pi0 + gamma_s - ref_s.node.borrow().pi;
			if bound < self.get_cur_upper_bound(adapter, s) {
				self.update_ub(s, bound, ub_updates);
				let node_s = ref_s.node.borrow();
				if bound < adapter.get_int_upper_bound(s) {
					trace!("Updating upper bound for i{:?} to {bound}", ref_s.var);
					let (prev, b) = node_s.backtrace.unwrap();
					adapter.set_int_upper_bound(s, bound, b, self.nodes[prev].var, self.get_cur_upper_bound(adapter, prev))?;

				}
				for &index in node_s.reverse_edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[index];
					let mut node_t = self.nodes[edge.from].node.borrow_mut();
					if !node_t.visited {
						let path = gamma_s + node_t.pi + edge.val - node_s.pi;
						let old = queue.push_increase(edge.from, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							node_t.backtrace = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}


	/// Propagate new bounds and fixed booleans.
	fn propagate<A: ModelAdapter>(&mut self, adapter: &mut A, state: &mut DifferenceLogicState) -> Result<(), Conflict> {

		trace!("Propagating bounds on lb changes {:?}, ub changes {:?}, fixed booleans {:?}.", state.lower_bound_changes, state.upper_bound_changes, state.fixed_bools);

		// Lower bound updates
		if !state.lower_bound_changes.is_empty() {
			self.inc_lb(adapter, &state.lower_bound_changes, &mut state.lb_updates)?;
		}

		// Upper bound updates
		if !state.upper_bound_changes.is_empty() {
			self.inc_ub(adapter, &state.upper_bound_changes, &mut state.ub_updates)?;
		}

		// Consequences of lower bound updates on open implied constraints
		for &n in state.lb_updates.iter() {

			let node_ref = self.nodes[n].clone();
			let mut node = node_ref.node.borrow_mut();
			let lb = node.lower_bound.unwrap();

			let mut open = node.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				let target_ub = self.get_cur_upper_bound(adapter, edge.to);
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is falsified by bounds.", edge.bool_var, node_ref.var, edge.to, edge.val);
					adapter.set_bool(edge.bool_var, node_ref.var, lb, self.nodes[edge.to].var, target_ub)?;
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if self.get_cur_upper_bound(adapter, edge.from) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is implied by bounds.", edge.bool_var, edge.from, node_ref.var, edge.val);
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}

		}

		// Consequences of upper bound updates on open implied constraints
		for &n in state.ub_updates.iter() {

			let node_ref = self.nodes[n].clone();
			let mut node = node_ref.node.borrow_mut();
			let ub = node.upper_bound.unwrap();

			let mut open = node.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if ub - self.get_cur_lower_bound(adapter, edge.to) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is implied by bounds.", edge.bool_var, node_ref.var, edge.to, edge.val);
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				let source_lb = self.get_cur_lower_bound(adapter, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is falsified by bounds.", edge.bool_var, edge.from, node_ref.var, edge.val);
					adapter.set_bool(edge.bool_var, self.nodes[edge.from].var, source_lb, node_ref.var, ub)?;
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}

		}

		// Handle fixed booleans
		for &b in state.fixed_bools.iter() {
			let val = adapter.get_bool_val(b).unwrap();
			trace!("Boolean b{b:?} fixed to {val}");
			if val {
				// Consequences of setting the boolean to true -> add all implied edges.
				for &index in state.bool_implications[b].iter() {
					let closed_now = self.close_imp_edge(adapter, index);
					trace!("Processing adding edge i{:?} - i{:?} <= {:?} (open: {closed_now})", self.edges[index].from, self.edges[index].to, self.edges[index].val);
					// Only continue if the edge was not already closed.
					if closed_now {
						// If the edge can't be added, a conflict will be generated
						if self.inc_sat(adapter, index)? {
							self.activate_imp_edge(adapter, index);
							// If the edge was added, check the status of open edges.
							self.inc_imp(adapter, index)?;
							let edge = &self.edges[index];
							let lb_y = -edge.val + self.get_cur_lower_bound(adapter, edge.from);
							if lb_y > self.get_cur_lower_bound(adapter, edge.to) {
								// New edge caused lower bound change.
								adapter.set_int_lower_bound(self.nodes[edge.to].var, lb_y, Some(b), self.nodes[edge.from].var, self.get_cur_lower_bound(adapter, edge.from))?;
								self.update_lb(edge.to, lb_y, &mut state.lb_updates);
							}
							let ub_x = edge.val + self.get_cur_upper_bound(adapter, edge.to);
							if ub_x < self.get_cur_upper_bound(adapter, edge.from) {
								// New edge caused upper bound change.
								adapter.set_int_upper_bound(self.nodes[edge.from].var, ub_x, Some(b), self.nodes[edge.to].var, self.get_cur_upper_bound(adapter, edge.to))?;
								self.update_ub(edge.from, ub_x, &mut state.ub_updates);
							}
						}
					}
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				for &index in state.bool_implications[b].iter() {
					let edge_closed = self.close_imp_edge(adapter, index);
					trace!("Closing edge i{:?} - i{:?} <= {:?} (open: {edge_closed})", self.edges[index].from, self.edges[index].to, self.edges[index].val);
				}
			}
		}

		//trace!("Current graph after implied checks: {}", self.graph.to_dot(actions));

		// All state changes are done, new ones as a consequence will be propagated
		state.reset_var_changes();
		Ok(())

	}


	/// Generate a dot presentation of the active graph.
	fn to_dot<A: ModelAdapter>(&self, adapter: &mut A) -> String {
		let mut out = "digraph {\n".to_owned();
		for (n, v) in self.nodes.iter().enumerate() {
			let node = v.node.borrow();
			out.push_str(format!("\"{:?}\" [label=\"{:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 v.var,
								 v.var,
								 self.get_cur_lower_bound(adapter, n),
								 self.get_cur_upper_bound(adapter, n),
								 node.pi).as_str());
			for &index in node.edges.iter(adapter.get_trailing_actions()) {
				let edge = &self.edges[index];
				out.push_str(format!("\"{:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n", v.var, self.nodes[edge.to].var, edge.val, edge.bool_var).as_str());
			}
		}
		out += "}";
		out
	}

}


/// Provides access to the current state of the model independent of representation.
trait ModelAdapter {
	
	/// Return the lower bound for the variable identified by index.
	fn get_int_lower_bound(&self, v: usize) -> IntVal;

	/// Set the lower bound for the variable identified by index as a consequence of the boolean and 
	/// the given lower bound.
	fn set_int_lower_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal) -> Result<(), Conflict>;

	/// Return the upper bound for the variable identified by index.
	fn get_int_upper_bound(&self, v: usize) -> IntVal;

	/// Set the upper bound for the variable identified by index as a consequence of the boolean and 
	/// the given upper bound.
	fn set_int_upper_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, ub_var: usize, ub_val: IntVal) -> Result<(), Conflict>;
	
	/// Return the infrastructure to deal with trailed integers.
	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions;
	
	/// Get the value of the boolean variable identified by index if it is set.
	fn get_bool_val(&self, v: usize) -> Option<bool>;

	/// Enforce the negation of the boolean variable identified by index with the reason given as an
	/// array of boolean variables. Fail if var is None.
	fn process_negative_cycle(&mut self, var: Option<usize>, reason: Vec<usize>) -> Result<(), Conflict>;

	/// Enforce the negation boolean variable identified by index with a reason given by a lower and 
	/// upper bound.
	fn set_bool(&mut self, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal, ub_var: usize, ub_val: IntVal) -> Result<(), Conflict>;
	
}

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

impl<P: PropagationActions> ModelAdapter for SolverModelAdapter<'_, P> {
	
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
		self.actions.set_bool(!var, reason.into_iter().map(|i| self.bool_vars[i]).collect::<Vec<_>>())?;
		Ok(())
	}

	fn set_bool(&mut self, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal, ub_var: usize, ub_val: IntVal) -> Result<(), Conflict> {
		let var = bool_var.map_or(BoolView::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var, |a: &mut P| vec![a.get_int_lit(self.int_vars[lb_var], IntLitMeaning::GreaterEq(lb_val)),
													 a.get_int_lit(self.int_vars[ub_var], IntLitMeaning::Less(ub_val + 1))])?;
		Ok(())
	}
	
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Propagator state data.
pub struct DifferenceLogicState {
	/// List of variables with updated lower bounds.
	lb_updates: Vec<usize>,
	/// List of variables with updated upper bounds.
	ub_updates: Vec<usize>,
	/// Map from boolean indices to their implied edges.
	bool_implications: Vec<Vec<usize>>,
	/// List of integer variable indices with reported lower bound changes.
	lower_bound_changes: IndexSet<usize>,
	/// List of integer variable indices with reported upper bound changes.
	upper_bound_changes: IndexSet<usize>,
	/// List of boolean variable indices that have recently been reported as fixed to true.
	fixed_bools: IndexSet<usize>,
}

impl DifferenceLogicState {
	
	fn new(int_vars: usize, bool_vars: usize) -> Self {
		Self {
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			bool_implications: (0..bool_vars).into_iter().map(|_| Vec::new()).collect(),
			lower_bound_changes: (0..int_vars).into_iter().collect(),
			upper_bound_changes: (0..int_vars).into_iter().collect(),
			fixed_bools: IndexSet::default(),
		}
	}
	
	fn reset_var_changes(&mut self) {
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		self.fixed_bools.clear();
	}	
	
}

#[derive(Debug, Clone, PartialEq, Eq)]  // todo do we need Hash here?
/// Bounds consistent global difference constraint propagator.
pub struct DifferenceLogicBounds {
	/// Integer variables.
	int_vars: Vec<IntView>,
	/// Boolean variables.
	bool_vars: Vec<BoolView>,
	/// Constraint graph.
	graph: DifferenceLogicGraph,
	/// List of constraints. todo currently initial list, not to be modified later?
	constraints: Vec<(usize, usize, IntVal)>,
	/// List of implied constraints. todo currently initial list, not to be modified later?
	imp_constraints: Vec<(usize, usize, usize, IntVal)>,
	/// Propagator state data.
	state: DifferenceLogicState,
}

impl DifferenceLogicBounds {

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<I: PropagatorInitActions + ?Sized>(solver: &mut I,
													 priority_level: PriorityLevel,
													 constraints: Vec<(IntView, IntView, IntVal)>,
													 imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>) {

		// todo at this point there might be some variables that have merged into a constant. For now we still keep them as otherwise the initial bound propagation will not be done. They should be dropped after simplify!
		// todo this is a workaround if edges now are completely redundant connecting the same variable. Should only happen if both sides collapse to the same constant?
		trace!("Original constraint lengths: {} and {}.", constraints.len(), imp_constraints.len());
		let trimmed_constraints = constraints.into_iter().filter(|&(x, y, d)| {
			assert!(x != y || d == 0);  // todo this would mean a failure at the root node, deal with this in simplification
			x != y
		}).collect::<Vec<_>>();
		let trimmed_imp_constraints = imp_constraints.into_iter().filter(|&(_, x, y, d)| {
			assert!(x != y || d == 0);  // todo this would mean fixing the boolean at the root node to false, deal with this in simplification
			x != y
		}).collect::<Vec<_>>();
		trace!("Constraint lengths after trimming self-loops: {} and {}.", trimmed_constraints.len(), trimmed_imp_constraints.len());
		
		let mut int_var_map = IndexMap::default();
		for var in trimmed_constraints.iter().flat_map(|&(x, y, _)| once(x).chain(once(y)))
			.chain(trimmed_imp_constraints.iter().flat_map(|&(_, x, y, _)| once(x).chain(once(y)))) {
			if !int_var_map.contains_key(&var) {
				let _ = int_var_map.insert(var, int_var_map.len());
			}
		}
		
		let mut bool_var_map = IndexMap::default();
		for var in trimmed_imp_constraints.iter().map(|&(b, _, _, _)| b) {
			if !bool_var_map.contains_key(&var) {
				let _ = bool_var_map.insert(var, bool_var_map.len());
			}
		}

		trace!("Creating DifferenceLogicBounds propagator for {} int and {} bool vars.", int_var_map.len(), bool_var_map.len());
		
		let mut initial_trail = InitialTrail::new();
		let int_vars: Vec<_> = int_var_map.iter().map(|(&v, _)| v).collect();
		let bool_vars = bool_var_map.iter().map(|(&v, _)| v).collect();
		
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len());
		initial_trail.init_trail(solver);
		graph.init_trail(&mut initial_trail);

		let state = DifferenceLogicState::new(int_var_map.len(), bool_var_map.len());

		let prop = solver.add_propagator(
			Box::new(Self {
				int_vars,
				bool_vars,
				graph,
				constraints: trimmed_constraints.iter().map(|&(x, y, d)| (int_var_map[&x], int_var_map[&y], d)).collect(),
				imp_constraints: trimmed_imp_constraints.iter().map(|&(b, x, y, d)| (bool_var_map[&b], int_var_map[&x], int_var_map[&y], d)).collect(),
				state,
			}),
			priority_level,
		);
		for (&v, &i) in int_var_map.iter() {
			solver.advise_on_int_change(prop, v, IntPropCond::LowerBound, i as u64);
			solver.advise_on_int_change(prop, v, IntPropCond::UpperBound, i as u64);
		}
		for (&v, &i) in bool_var_map.iter() {
			solver.advise_on_bool_change(prop, v, i as u64);
		}
		solver.advise_on_backtrack(prop);
		solver.enqueue_now(prop); // todo might be removed
	}

}

impl<P, E> Propagator<P, E> for DifferenceLogicBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn advise_of_bool_change(&mut self, _actions: &mut E, _view: BoolView, data: u64) -> bool {
		trace!("Boolean b{data} fixed.");
		let _ = self.state.fixed_bools.insert(data as usize);
		true
	}

	fn advise_of_int_change(&mut self, _actions: &mut E, _view: IntView, condition: IntPropCond, data: u64) -> bool {
		trace!("Integer i{data} changed on condition {condition:?}.");
		let _ = match condition {
			IntPropCond::LowerBound => self.state.lower_bound_changes.insert(data as usize),
			IntPropCond::UpperBound => self.state.upper_bound_changes.insert(data as usize),
			_ => unreachable!("Condition was never enqueued."),
		};
		true
	}

	fn advise_of_backtrack(&mut self, _actions: &mut E) -> bool {
		trace!("Backtrack advise");
		self.state.reset_var_changes();
		false
	}


	#[tracing::instrument(name = "difference_logic", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		
		let mut model_adapter = SolverModelAdapter::new(actions, &self.int_vars, &self.bool_vars);

		let mut graph_change = false; //todo remove

		for &(b, x, y, d) in self.imp_constraints.iter() {
			let index = self.graph.new_imp_edge(&mut model_adapter, DiffEdge::new(x, y, d, Some(b)));
			self.state.bool_implications.get_mut(b).unwrap().push(index);
		}
		self.imp_constraints.clear();

		for &(x, y, d) in self.constraints.iter() {  // todo this should be done earlier and simplified in the process
			graph_change = true;
			let edge = DiffEdge::new(x, y, d, None);
			let index = self.graph.new_edge(&mut model_adapter, edge);
			let _ = self.graph.inc_sat(&mut model_adapter, index)?;
			//trace!("Graph after adding new edge: {}", self.graph.to_dot(actions));
			self.graph.inc_imp(&mut model_adapter, index)?;
		}
		self.constraints.clear();

		self.graph.reset_lb_updates(&mut self.state.lb_updates);
		self.graph.reset_ub_updates(&mut self.state.ub_updates);

		/*trace!("Full state before propagate bounds:");
		for (v, node) in self.graph.graph.iter() {
			trace!("{v:?}: {:?}", node.node.borrow().deref());
		}
		for edge in self.graph.edges.iter() {
			trace!("{edge:?}");
		}*/

		if let Err(e) = self.graph.propagate(&mut model_adapter, &mut self.state) {
			self.state.reset_var_changes();
			return Err(e);
		}

		if graph_change {
			trace!("Initial graph: {}", self.graph.to_dot(&mut model_adapter));
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::solver::propagation::PropagatingSolver;
	use pindakaas::Lit as RawLit;
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::{DiffEdge, DifferenceLogicBounds, DifferenceLogicGraph, SolverModelAdapter};
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, Model};
	use crate::actions::TrailingActions;
	use crate::helpers::initial_trail::InitialTrail;
	use crate::reformulate::InitConfig;
	use crate::solver::IntView;
	use crate::solver::queue::PriorityLevel;
	use crate::solver::solving_context::SolvingContext;
	use crate::solver::Value::Int;

	#[test]
	#[traced_test]
	fn test_relevant_dijkstra() {  // TODO test other methods like this
		let mut prb = Model::default();
		let (mut slv, _): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..10).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = vec![];
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
  		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		for (x, y, d) in vec![(0, 1, 1), (0, 2, 1), (0, 4, 1),
							  (1, 4, 1), (1, 5, 1), (2, 4, 1), (3, 4, 1), (3, 5, 1),
							  (4, 6, 1), (4, 8, 1),
							  (5, 6, 1), (5, 7, 1), (5, 8, 1), (5, 9, 1),
							  (7, 9, 1), (8, 9, 1)] {
			let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(x, y, d, None));
		}
		let new_index = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(4, 5, 1, None));

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
		let bools = (0..3).into_iter().map(|_| prb.new_bool_var()).collect::<Vec<_>>();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..3).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = bools.into_iter().map(|b| map.get_bool(&mut slv, b)).collect::<Vec<_>>();
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut model_adapter, DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(2, 1, 2, Some(2)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap(),
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert_eq!(graph.nodes[2].node.borrow().open_edges.open_len(&ctx), 1);
		assert_eq!(graph.nodes[2].node.borrow().open_reverse_edges.open_len(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_inc_imp2() {
		let mut prb = Model::default();
		let bools = (0..4).into_iter().map(|_| prb.new_bool_var()).collect::<Vec<_>>();
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let int_vars: Vec<_> = (0..4).into_iter().map(|_| IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		)).collect();
		let bool_vars = bools.into_iter().map(|b| map.get_bool(&mut slv, b)).collect::<Vec<_>>();
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_vars.len());
		initial_trail.init_trail(&mut slv);
		graph.init_trail(&mut initial_trail);
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut model_adapter, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_imp_edge(&mut model_adapter, DiffEdge::new(0, 3, 2, Some(3)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap(),
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert!(ctx.get_bool_val(bool_vars[3]).is_none());
		assert_eq!(graph.nodes[0].node.borrow().open_edges.open_len(&ctx), 2);
		assert_eq!(graph.nodes[0].node.borrow().open_reverse_edges.open_len(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple() {
		let mut prb = Model::default();
		let b = prb.new_bool_var();

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let b = map.get_bool(&mut slv, b);

		let x = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let y = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let z = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		DifferenceLogicBounds::new_in(&mut slv, PriorityLevel::Low, vec![(x, y, -2), (y, z, 3)],
									  vec![(b, y, z, 4), (b, x, z, -2)]);
		slv.assert_all_solutions(&[x, y, z, IntView::from(b)], move |sol| {
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
		let b = prb.new_bool_var();
		let c = prb.new_bool_var();

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let b = map.get_bool(&mut slv, b);
		let c = map.get_bool(&mut slv, c);

		let x = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let y = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let z = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let u = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let v = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let t = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		DifferenceLogicBounds::new_in(&mut slv, PriorityLevel::Low, vec![(x, y, -2), (y, z, 3), (z, u, -1), (u, v, 2), (x, t, 1), (t, z, -1)],
									  vec![(b, x, z, -2), (b, y, z, 4), (c, y, v, 1), (!c, v, y, -2)]);
		slv.assert_all_solutions(&[x, y, z, u, v, t, IntView::from(b), IntView::from(c)], move |sol| {
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
	fn test_conflict() {  // TODO this one fails
		let mut prb = Model::default();
		let (mut slv, _): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();

		let x = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let y = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let z = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		DifferenceLogicBounds::new_in(&mut slv, PriorityLevel::Low, vec![(x, y, 3), (y, z, -2), (z, x, -2)], vec![]);
		slv.assert_unsatisfiable();
	}

}
