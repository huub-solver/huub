//! Structure and algorithms for a global difference logic propagator.

use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher, RandomState};
use std::iter::once;
use std::ops::Deref;
use std::rc::Rc;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use priority_queue::PriorityQueue;
use tracing::trace;
use crate::solver::activation_list::{IntEvent, IntPropCond};
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, IntDecision, IntVal};
use crate::actions::InspectionActions;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::{TrailedOpenList, TrailedOpenListIterator};


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of set of difference constraints within a model.
pub struct DifferenceLogic {
	/// List of difference constraints.
	pub(crate) constraints: Vec<(IntDecision, IntDecision, IntVal)>,
	/// List of implied difference constraints.
	pub(crate) imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// todo can we already do graph simplification here?
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		// todo do simplification first, then transform graph here
		trace!("DifferenceLogic to_solver with {} constraints and {} imp_constraints", self.constraints.len(), self.imp_constraints.len());
		let constraints: Vec<_> = self.constraints.iter()
			.map(|(x, y, d)| (slv.get_solver_int(*x), slv.get_solver_int(*y), *d))
			.collect();
		let imp_constraints: Vec<_> = self.imp_constraints.iter()
			.map(|(b, x, y, d)| (slv.get_solver_bool(*b), slv.get_solver_int(*x), slv.get_solver_int(*y), *d))
			.collect();
		DifferenceLogicBounds::new_in(slv, constraints, imp_constraints);
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// An edge in the difference logic graph (bool_var -> source - target <= val).
pub struct DiffEdge {
	/// Source node.
	from: VarNodeRef,
	/// Target node.
	to: VarNodeRef,
	/// Difference value.
	val: IntVal,
	/// Boolean for the difference constraints (true for globally active constraints).
	bool_var: BoolView,
	/// Index of this edge in the list of open outgoing edges
	out_index: usize,
	/// Index of this edge in the list of open incoming edges
	in_index: usize,
}

impl DiffEdge {

	fn new(from: VarNodeRef, to: VarNodeRef, val: IntVal, bool_var: BoolView) -> Self {
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
	backtrace: Option<(VarNodeRef, BoolView)>,
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

	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			edges: TrailedList::new(actions),
			reverse_edges: TrailedList::new(actions),
			pi: 0,
			backtrace: None,
			visited: false,
			lower_bound: None,
			upper_bound: None,
			open_edges: TrailedOpenList::new(actions),
			open_reverse_edges: TrailedOpenList::new(actions),
		}
	}

}

#[derive(Clone, PartialEq, Eq)]  // todo should we implement Eq only on the IntView?
/// A hashable reference to a node in the difference logic graph.
pub struct VarNodeRef {
	/// Variable associated with the node.
	var: IntView,
	/// Reference to the node.
	node: Rc<RefCell<VarNode>>,
}

impl VarNodeRef {
	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A, var: IntView) -> Self {
		Self {
			var,
			node: Rc::new(RefCell::new(VarNode::new(actions))),
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

impl Hash for VarNodeRef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.var.hash(state);
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A graph of difference constraints.
pub struct DifferenceLogicGraph {
	/// Mapping from variables to nodes.
	nodes: HashMap<IntView, VarNodeRef>,
	/// List of all edges in the graph. todo could make this a trailed list for dynamic addition
	edges: Vec<DiffEdge>,
	/// Storage for the visited state.
	visited: Vec<VarNodeRef>,
}

impl DifferenceLogicGraph {

	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A, int_vars: Vec<IntView>) -> Self {
		Self {
			nodes: int_vars.iter().map(|&v| (v, VarNodeRef::new(actions, v))).collect(),
			edges: Vec::new(),
			visited: Vec::new(),
		}
	}

	/// Add a new globally active edge to the graph, return the index.
	fn new_edge<P: PropagationActions>(&mut self, actions: &mut P, edge: DiffEdge) -> usize {
		let index = self.edges.len();
		edge.from.node.borrow_mut().edges.push(actions, index);
		edge.to.node.borrow_mut().reverse_edges.push(actions, index);
		self.edges.push(edge);
		index
	}

	/// Add a new open implied edge to the graph, return the index.
	fn new_imp_edge(&mut self, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		edge.out_index = edge.from.node.borrow_mut().open_edges.len();
		edge.in_index = edge.to.node.borrow_mut().open_reverse_edges.len();
		edge.from.node.borrow_mut().open_edges.push(self.edges.len());
		edge.to.node.borrow_mut().open_reverse_edges.push(self.edges.len());
		self.edges.push(edge);
		index
	}

	/// Activate the implied edge given by the index.
	fn activate_imp_edge<P: PropagationActions>(&mut self, actions: &mut P, index: usize) {
		let edge = &self.edges[index];
		edge.from.node.borrow_mut().edges.push(actions, index);
		edge.to.node.borrow_mut().reverse_edges.push(actions, index);
	}

	/// Close the implied edge given by the index.
	/// Return true if the edge got closed by this call, false if it was already closed.
	fn close_imp_edge<P: PropagationActions>(&mut self, actions: &mut P, index: usize) -> bool {
		let from = &self.edges[index].from.clone();
		let to = &self.edges[index].to.clone();
		let out_index = self.edges[index].out_index;
		let in_index = self.edges[index].in_index;
		from.node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i) &&
			to.node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i)
	}

	/// Close the implied edge given by the index while iterating open edges in forward direction.
	fn close_imp_edge_forward<P: PropagationActions>(&mut self, actions: &mut P, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let _ = open.close(actions, |&e, i| self.edges[e].out_index = i);
		let to = &self.edges[index].to.clone();
		let in_index = self.edges[index].in_index;
		let _ = to.node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
	}

	/// Close the implied edge given by the index while iterating open edges in backward direction.
	fn close_imp_edge_backward<P: PropagationActions>(&mut self, actions: &mut P, rev_open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let _ = rev_open.close(actions, |&e, i| self.edges[e].in_index = i);
		let from = &self.edges[index].from.clone();
		let out_index = self.edges[index].out_index;
		let _ = from.node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i);
	}

	/// Mark the given node as visited.
	fn visit(&mut self, node: VarNodeRef) {
		node.node.borrow_mut().visited = true;
		self.visited.push(node);
	}

	/// Reset the visited state of all nodes.
	fn reset_visit(&mut self) {
		for node in self.visited.iter() {
			node.node.borrow_mut().visited = false;
		}
		self.visited.clear();
	}

	/// Get the current lower bound for the node, either stored or from the search.
	fn get_cur_lower_bound<I: InspectionActions>(&self, actions: &I, v: VarNodeRef) -> IntVal {
		let node = v.node.borrow();
		match node.lower_bound {
			Some(lb) => lb,
			None => actions.get_int_lower_bound(v.var),
		}
	}

	/// Update the stored lower bound for the node.
	fn update_lb(&self, node: VarNodeRef, val: IntVal, lb_updates: &mut Vec<VarNodeRef>) {
		node.node.borrow_mut().lower_bound = Some(val);
		lb_updates.push(node);
	}

	/// Reset stored lower bounds of all nodes.
	fn reset_lb_updates(&self, lb_updates: &mut Vec<VarNodeRef>) {
		for node in lb_updates.iter() {
			node.node.borrow_mut().lower_bound = None;
		}
		lb_updates.clear();
	}

	/// Get the current upper bound for the node, either stored or from the search.
	fn get_cur_upper_bound<I: InspectionActions>(&self, actions: &I, v: VarNodeRef) -> IntVal {
		let node = v.node.borrow();
		match node.upper_bound {
			Some(ub) => ub,
			None => actions.get_int_upper_bound(v.var),
		}
	}

	/// Update the stored upper bound for the node.

	fn update_ub(&mut self, node: VarNodeRef, val: IntVal, ub_updates: &mut Vec<VarNodeRef>) {
		node.node.borrow_mut().upper_bound = Some(val);
		ub_updates.push(node);
	}

	/// Reset stored upper bounds of all nodes.
	fn reset_ub_updates(&mut self, ub_updates: &mut Vec<VarNodeRef>) {
		for node in ub_updates.iter() {
			node.node.borrow_mut().upper_bound = None;
		}
		ub_updates.clear();
	}

	/// Get the reason for a cycle of negative lengths (all booleans along the cycle).
	fn get_cycle_reason(&self, node: VarNodeRef) -> Vec<BoolView> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = &var.clone().node.borrow().backtrace {
			reason.push(*b);
			var = cur.clone();
		}
		reason
	}

	/// Check incremental addition of the edge given by index to the active graph.
	/// Returns true if addition is possible. Otherwise, false is returned for implied edges, and a
	/// conflict is caused by global edges.
	fn inc_sat<P: PropagationActions>(&mut self, actions: &mut P, new_index: usize) -> Result<bool, Conflict> {

		let new_edge = &self.edges[new_index];
		trace!("Performing inc_sat on {:?}, {:?}, {:?}", new_edge.from.var, new_edge.to.var, new_edge.val);
		let mut queue = PriorityQueue::new();
		let mut pi_new = IndexMap::new(); // todo Could be replaced by the visited state. Q1: Is state or map faster? Q2: Is keeping old pi in case of conflict better?
		new_edge.to.node.borrow_mut().backtrace = None;
		let gamma_v = new_edge.from.node.borrow().pi + new_edge.val - new_edge.to.node.borrow().pi;
		if gamma_v < 0 {
			let _ = queue.push(new_edge.to.clone(), Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&new_edge.from).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let node_s = s.node.borrow();
			let _ = pi_new.insert(s.var, node_s.pi + gamma_s);
			for index in node_s.edges.iter(actions) {
				let edge = &self.edges[*index];
				let mut node_t = edge.to.node.borrow_mut();
				if !pi_new.contains_key(&edge.to.var) {
					let gamma_t = pi_new[&s.var] + edge.val - node_t.pi;
					if gamma_t < 0 {
						let old = queue.push_increase(edge.to.clone(), Reverse(gamma_t));
						if old.map_or(true, |Reverse(old_gamma)| gamma_t < old_gamma) {
							node_t.backtrace = Some((s.clone(), edge.bool_var));
						}
					}
				}
			}
		}
		// If the origin is in the queue, we have a cycle of negative length.
		if queue.get_priority(&new_edge.from).is_some() {
			trace!("Found cycle with negative length");
			actions.set_bool(!new_edge.bool_var, self.get_cycle_reason(new_edge.from.clone()))?;
			return Ok(false);
		}
		for (var, val) in pi_new {
			self.nodes[&var].node.borrow_mut().pi = val;
		}
		Ok(true)
	}

	/// Perform dijkstra from the given node to all other nodes in the graph, return a map of
	/// distances. Can be performed in forward or backward direction.
	fn dijkstra<P: PropagationActions>(&mut self, actions: &mut P, source: VarNodeRef, reverse: bool) -> HashMap<IntView, IntVal> {

		trace!("Starting dijkstra for {source:?} in mode reverse={reverse}");
		let mut distances = HashMap::new();  // todo?
		let mut queue = PriorityQueue::new();
		let _ = distances.insert(source.var, 0);
		let _ = queue.push(source.clone(), Reverse(0));
		while !queue.is_empty() {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			let node_s = s.node.borrow();
			//trace!("dijkstra on current node {s:?} with dist {dist}");
			for index in if reverse {node_s.reverse_edges.iter(actions)} else {node_s.edges.iter(actions)} {
				let edge = &self.edges[*index];
				let target = if reverse {edge.from.clone()} else {edge.to.clone()};
				let node_t = target.node.borrow();
				let new_dist = dist + edge.val + ((node_s.pi - node_t.pi) * if reverse {-1} else {1}); //todo could write differently without if
				if !distances.contains_key(&target.var) || distances[&target.var] > new_dist {
					let _ = queue.push(target.clone(), Reverse(new_dist));
					//trace!("dijkstra adding node {:?} with dist {new_dist}", edge.node);
				}
			}
		}
		distances

	}

	/// Check if the new edge given by the index implies or falsifies any of the open edges.
	fn inc_imp<P: PropagationActions>(&mut self, actions: &mut P, new_index: usize) -> Result<(), Conflict> {

		let outgoing_u = self.dijkstra(actions, self.edges[new_index].from.clone(), false);
		let incoming_v = self.dijkstra(actions, self.edges[new_index].to.clone(), true);
		let changed: IndexSet<&IntView, RandomState> = IndexSet::from_iter(outgoing_u.keys().chain(incoming_v.keys()));  //todo rewrite this!!!
		let new_edge_val = self.edges[new_index].val;
		let mut fail_indices = Vec::new();

		for &n in changed.iter() {
			let temp_node = self.nodes[&n].clone();
			let mut node = temp_node.node.borrow_mut();
			let mut open = node.open_edges.iter(actions);
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if outgoing_u.contains_key(&edge.from.var) && incoming_v.contains_key(&edge.to.var) && outgoing_u[&edge.from.var] + new_edge_val + incoming_v[&edge.to.var] <= edge.val {
					trace!("Constraint {:?} - {:?} <= {} is implied", edge.from.var, edge.to.var, edge.val);
					self.close_imp_edge_forward(actions, &mut open, index);
				} else if outgoing_u.contains_key(&edge.to.var) && incoming_v.contains_key(&edge.from.var) && outgoing_u[&edge.to.var] + new_edge_val + incoming_v[&edge.from.var] <= -edge.val - 1 { // todo slight double work for reified constraints
					trace!("Constraint {:?} - {:?} <= {} is falsified since inverse is implied", edge.from.var, edge.to.var, edge.val);
					fail_indices.push(index);
					self.close_imp_edge_forward(actions, &mut open, index);
				}
			}
			let mut rev_open = node.open_reverse_edges.iter(actions);
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if outgoing_u.contains_key(&edge.from.var) && incoming_v.contains_key(&edge.to.var) && outgoing_u[&edge.from.var] + new_edge_val + incoming_v[&edge.to.var] <= edge.val {
					trace!("Constraint {:?} - {:?} <= {} is implied", edge.from.var, edge.to.var, edge.val);
					self.close_imp_edge_backward(actions, &mut rev_open, index);
				} else if outgoing_u.contains_key(&edge.to.var) && incoming_v.contains_key(&edge.from.var) && outgoing_u[&edge.to.var] + new_edge_val + incoming_v[&edge.from.var] <= -edge.val - 1 { // todo slight double work for reified constraints
					trace!("Constraint {:?} - {:?} <= {} is falsified since inverse is implied", edge.from.var, edge.to.var, edge.val);
					fail_indices.push(index);
					self.close_imp_edge_backward(actions, &mut rev_open, index);
				}
			}
		}
		for index in fail_indices {  // todo check if we want this here?
			let _ = self.inc_sat(actions, index)?;
		}

		Ok(())
	}

	/// Perform incremental updates of lower bounds.
	fn inc_lb<P: PropagationActions>(&mut self, actions: &mut P, v_l: &Vec<VarNodeRef>, lb_updates: &mut Vec<VarNodeRef>) -> Result<(), Conflict> {

		trace!("Running inc_lb on {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|n| actions.get_int_lower_bound(n.var) + n.node.borrow().pi).max().unwrap();
		let mut queue = PriorityQueue::new();
		for n in v_l.iter() {
			// Min value indicates that successors still need to be considered.
			self.update_lb(n.clone(), IntVal::MIN, lb_updates);
			let _ = queue.push(n.clone(), Reverse(pi0 - actions.get_int_lower_bound(n.var) - n.node.borrow().pi));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s.clone());
			let bound = pi0 - gamma_s - s.node.borrow().pi;
			if bound > self.get_cur_lower_bound(actions, s.clone()) {
				self.update_lb(s.clone(), bound, lb_updates);
				let node_s = s.node.borrow();
				if bound > actions.get_int_lower_bound(s.var) {
					trace!("Updating lower bound for {:?} to {bound}", s.var);
					let (prev, b) = node_s.clone().backtrace.unwrap();
					actions.set_int_lower_bound(s.var, bound, |a: &mut P| vec![b, a.get_int_lit(prev.var, IntLitMeaning::GreaterEq(self.get_cur_lower_bound(a, prev.clone())))])?;
				}
				for index in node_s.edges.iter(actions) {
					let edge = &self.edges[*index];
					let mut node_t = edge.to.node.borrow_mut();
					if !node_t.visited {
						let path = gamma_s + node_s.pi + edge.val - node_t.pi;
						let old = queue.push_increase(edge.to.clone(), Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							node_t.backtrace = Some((s.clone(), edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Perform incremental updates of upper bounds.
	fn inc_ub<P: PropagationActions>(&mut self, actions: &mut P, v_u: &Vec<VarNodeRef>, ub_updates: &mut Vec<VarNodeRef>) -> Result<(), Conflict> {

		trace!("Running inc_ub on {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|n| actions.get_int_upper_bound(n.var) + n.node.borrow().pi).min().unwrap();
		let mut queue = PriorityQueue::new();
		for n in v_u.iter() {
			// Max value indicates that predecessors still need to be considered.
			self.update_ub(n.clone(), IntVal::MAX, ub_updates);
			let _ = queue.push(n.clone(), Reverse(n.node.borrow().pi + actions.get_int_upper_bound(n.var) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s.clone());
			let bound = pi0 + gamma_s - s.node.borrow().pi;
			if bound < self.get_cur_upper_bound(actions, s.clone()) {
				self.update_ub(s.clone(), bound, ub_updates);
				let node_s = s.node.borrow();
				if bound < actions.get_int_upper_bound(s.var) {
					trace!("Updating upper bound for {:?} to {bound}", s.var);
					let (prev, b) = node_s.clone().backtrace.unwrap();
					actions.set_int_upper_bound(s.var, bound, |a: &mut P| vec![b, a.get_int_lit(prev.var, IntLitMeaning::Less(self.get_cur_upper_bound(a, prev.clone()) + 1))])?;

				}
				for index in node_s.reverse_edges.iter(actions) {
					let edge = &self.edges[*index];
					let mut node_t = edge.from.node.borrow_mut();
					if !node_t.visited {
						let path = gamma_s + node_t.pi + edge.val - node_s.pi;
						let old = queue.push_increase(edge.from.clone(), Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							node_t.backtrace = Some((s.clone(), edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}


	/// Propagate new bounds and fixed booleans.
	fn propagate<P: PropagationActions>(&mut self, actions: &mut P, state: &mut DifferenceLogicState) -> Result<(), Conflict> {

		trace!("Propagating bounds on lb changes {:?}, ub changes {:?}, fixed booleans {:?}.", state.lower_bound_changes, state.upper_bound_changes, state.fixed_bools);

		// Lower bound updates
		if !state.lower_bound_changes.is_empty() {
			let lb_changes_vec = state.lower_bound_changes.iter().map(|v| self.nodes[v].clone()).collect();
			self.inc_lb(actions, &lb_changes_vec, &mut state.lb_updates)?;
		}

		// Upper bound updates
		if !state.upper_bound_changes.is_empty() {
			let ub_changes_vec = state.upper_bound_changes.iter().map(|v| self.nodes[v].clone()).collect();
			self.inc_ub(actions, &ub_changes_vec, &mut state.ub_updates)?;
		}

		// Consequences of lower bound updates on open implied constraints
		for n in state.lb_updates.iter() {

			let mut node = n.node.borrow_mut();
			let lb = node.lower_bound.unwrap();

			let mut open = node.open_edges.iter(actions);
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				let target_ub = self.get_cur_upper_bound(actions, edge.to.clone());
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is falsified by bounds.", edge.bool_var, n.var, edge.to.var, edge.val);
					actions.set_bool(!edge.bool_var, |a: &mut P| vec![a.get_int_lit(n.var, IntLitMeaning::GreaterEq(lb)),
																	  a.get_int_lit(edge.to.var, IntLitMeaning::Less(target_ub + 1))])?;
					//let _ = fixed_bools.insert(!edge.bool_var.clone());
					self.close_imp_edge_forward(actions, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(actions);
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if self.get_cur_upper_bound(actions, edge.from.clone()) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is implied by bounds.", edge.bool_var, edge.from.var, n.var, edge.val);
					self.close_imp_edge_backward(actions, &mut rev_open, index);
				}
			}

		}

		// Consequences of upper bound updates on open implied constraints
		for n in state.ub_updates.iter() {

			let mut node = n.node.borrow_mut();
			let ub = node.upper_bound.unwrap();

			let mut open = node.open_edges.iter(actions);
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if ub - self.get_cur_lower_bound(actions, edge.to.clone()) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is implied by bounds.", edge.bool_var, n.var, edge.to.var, edge.val);
					self.close_imp_edge_forward(actions, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(actions);
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				let source_lb = self.get_cur_lower_bound(actions, edge.from.clone());
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is falsified by bounds.", edge.bool_var, edge.from.var, n.var, edge.val);
					actions.set_bool(!edge.bool_var, |a: &mut P| vec![a.get_int_lit(edge.from.var, IntLitMeaning::GreaterEq(source_lb)),
																	  a.get_int_lit(n.var, IntLitMeaning::Less(ub + 1))])?;
					//let _ = fixed_bools.insert(!edge.bool_var.clone());
					self.close_imp_edge_backward(actions, &mut rev_open, index);
				}
			}

		}

		// Handle fixed booleans
		for b in state.fixed_bools.iter() {
			if actions.get_bool_val(*b).is_none() {
				trace!("Boolean {b:?} is actually not fixed.");  // todo could implement advisor on backtrack and just clear collections
				continue;
			}
			trace!("Boolean {b:?} fixed to true.");
			if let Some(edges) = state.bool_map.get(b) {
				// Consequences of setting the boolean to true -> add all implied edges.
				for &index in edges.iter() {
					let closed_now = self.close_imp_edge(actions, index);
					trace!("Processing adding edge {:?} - {:?} <= {:?} (open: {closed_now})", self.edges[index].from.var, self.edges[index].to.var, self.edges[index].val);
					// Only continue if the edge was not already closed.
					if closed_now {
						// If the edge can't be added, a conflict will be generated
						if self.inc_sat(actions, index)? {
							self.activate_imp_edge(actions, index);
							// If the edge was added, check the status of open edges.
							self.inc_imp(actions, index)?;
							let edge = &self.edges[index];
							let lb_y = -edge.val + self.get_cur_lower_bound(actions, edge.from.clone());
							if lb_y > self.get_cur_lower_bound(actions, edge.to.clone()) {
								// New edge caused lower bound change.
								actions.set_int_lower_bound(edge.to.var, lb_y, |a: &mut P| vec![*b, a.get_int_lit(edge.from.var, IntLitMeaning::GreaterEq(self.get_cur_lower_bound(a, edge.from.clone())))])?;
								self.update_lb(edge.to.clone(), lb_y, &mut state.lb_updates);
							}
							let ub_x = edge.val + self.get_cur_upper_bound(actions, edge.to.clone());
							if ub_x < self.get_cur_upper_bound(actions, edge.from.clone()) {
								// New edge caused upper bound change.
								actions.set_int_upper_bound(edge.from.var, ub_x, |a: &mut P| vec![*b, a.get_int_lit(edge.to.var, IntLitMeaning::Less(self.get_cur_upper_bound(a, edge.to.clone()) + 1))])?;
								self.update_ub(edge.from.clone(), ub_x, &mut state.ub_updates);
							}
						}
					}
				}
			}
			let negation = !*b;
			if let Some(edges) = state.bool_map.get(&negation) {
				// Consequences of setting the negation of the boolean to false -> close all implied edges.
				for &index in edges.iter() {
					let edge_closed = self.close_imp_edge(actions, index);
					trace!("Closing edge {:?} - {:?} <= {:?} (open: {edge_closed})", self.edges[index].from.var, self.edges[index].to.var, self.edges[index].val);
				}
			}
		}

		//trace!("Current graph after implied checks: {}", self.graph.to_dot(actions));

		// All state changes are done, new ones as a consequence will be propagated
		state.reset_var_changes();
		Ok(())

	}


	/// Generate a dot presentation of the active graph.
	fn to_dot<I: InspectionActions>(&self, actions: &mut I) -> String {
		let mut out = "digraph {\n".to_owned();
		for (&var, v) in self.nodes.iter() {
			let node = v.node.borrow();
			out.push_str(format!("\"{var:?}\" [label=\"{var:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 self.get_cur_lower_bound(actions, v.clone()),
								 self.get_cur_upper_bound(actions, v.clone()),
								 node.pi).as_str());
			for index in node.edges.iter(actions) {
				let edge = &self.edges[*index];
				out.push_str(format!("\"{var:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n", edge.to.var, edge.val, edge.bool_var).as_str());
			}
		}
		out += "}";
		out
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Propagator state data.
pub struct DifferenceLogicState {
	/// List of variables with updated lower bounds.
	lb_updates: Vec<VarNodeRef>,
	/// List of variables with updated upper bounds.
	ub_updates: Vec<VarNodeRef>,
	/// Map from boolean variables to their implied edges.
	bool_map: HashMap<BoolView, Vec<usize>>,
	/// List of variables with reported lower bound changes.
	lower_bound_changes: IndexSet<IntView>,
	/// List of variables with reported upper bound changes.
	upper_bound_changes: IndexSet<IntView>,
	/// List of boolean variables that have recently been reported as fixed to true.
	fixed_bools: IndexSet<BoolView>,
}

impl DifferenceLogicState {
	
	fn new(int_vars: Vec<IntView>, bool_vars: Vec<BoolView>) -> Self {
		Self {
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			bool_map: bool_vars.iter().map(|&b| (b, Vec::new())).collect(),
			lower_bound_changes: int_vars.iter().map(|&v| v).collect(),
			upper_bound_changes: int_vars.iter().map(|&v| v).collect(),
			fixed_bools: IndexSet::new(),
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
	/// Constraint graph.
	graph: DifferenceLogicGraph,
	/// List of constraints. todo currently initial list, not to be modified later?
	constraints: Vec<(IntView, IntView, IntVal)>,
	/// List of implied constraints. todo currently initial list, not to be modified later?
	imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>,
	/// Propagator state data.
	state: DifferenceLogicState,
}

impl DifferenceLogicBounds {
	//todo check options for queue and hasher?

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P,
													 constraints: Vec<(IntView, IntView, IntVal)>,  // todo capture all options: int_lin_le(_imp,_reif), int_le(_imp,_reif), also equality and non-equality?
													 imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>) {

		let int_vars = constraints.iter().flat_map(|(x, y, _)| once(*x).chain(once(*y)))
			.chain(imp_constraints.iter().flat_map(|(_, x, y, _)| once(*x).chain(once(*y)))).unique().collect::<Vec<_>>();

		let bool_vars = imp_constraints.iter().map(|(b, _, _, _)| *b).unique().collect::<Vec<_>>();
		trace!("Creating DifferenceLogicBounds propagator for {} int and {} bool vars.", int_vars.len(), bool_vars.len());

		// todo init all or add dynamically?
		let graph = DifferenceLogicGraph::new(solver, int_vars.clone());
		let state = DifferenceLogicState::new(int_vars.clone(), bool_vars.clone());

		let prop = solver.add_propagator(
			Box::new(Self {
				graph,
				constraints: constraints.clone(),
				imp_constraints: imp_constraints.clone(),
				state,
			}),
			PriorityLevel::Low, // todo priority
		);
		for &v in int_vars.iter() {
			solver.advise_on_int_change(prop, v, IntPropCond::LowerBound, 0);
			solver.advise_on_int_change(prop, v, IntPropCond::UpperBound, 1);
		}
		for &v in bool_vars.iter() { // todo might run on both v and !v?
			solver.advise_on_bool_change(prop, v, 0);
		}
		solver.enqueue_now(prop); // todo might be removed
	}

}

impl<P, E> Propagator<P, E> for DifferenceLogicBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn advise_of_bool_change(&mut self, actions: &mut E, view: BoolView, _data: u64) -> bool {
		let val = actions.get_bool_val(view).unwrap();
		trace!("Boolean {view:?} fixed to {val}.");
		if val {
			let _ = self.state.fixed_bools.insert(view);
		} else {
			let _ = self.state.fixed_bools.insert(!view);
		}
		true
	}

	fn advise_of_int_change(&mut self, _actions: &mut E, view: IntView, _event: IntEvent, data: u64) -> bool {
		trace!("Integer {view:?} changed with data {data:?}.");
		if data == 0 {
			let _ = self.state.lower_bound_changes.insert(view);
		} else {
			let _ = self.state.upper_bound_changes.insert(view);
		}
		true
	}

	#[tracing::instrument(name = "difference_logic", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {

		let mut graph_change = false; //todo remove

		for (b, x, y, d) in self.imp_constraints.iter() {
			let index = self.graph.new_imp_edge(DiffEdge::new(self.graph.nodes[x].clone(), self.graph.nodes[y].clone(), *d, *b));
			self.state.bool_map.get_mut(b).unwrap().push(index);
		}
		self.imp_constraints.clear();

		for (x, y, d) in self.constraints.iter() {  // todo this should be done earlier and simplified in the process
			graph_change = true;
			let edge = DiffEdge::new(self.graph.nodes[x].clone(), self.graph.nodes[y].clone(), *d, BoolView::from(true));
			let index = self.graph.new_edge(actions, edge);
			let _ = self.graph.inc_sat(actions, index)?;
			self.graph.inc_imp(actions, index)?;
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

		if let Err(e) = self.graph.propagate(actions, &mut self.state) {
			self.state.reset_var_changes();
			return Err(e);
		}

		if graph_change {
			trace!("Initial graph: {}", self.graph.to_dot(actions));
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::DifferenceLogicBounds;
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, Model};
	use crate::reformulate::InitConfig;
	use crate::solver::IntView;
	use crate::solver::Value::Int;

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
		DifferenceLogicBounds::new_in(&mut slv, vec![(x, y, -2), (y, z, 3)], 
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
		DifferenceLogicBounds::new_in(&mut slv, vec![(x, y, -2), (y, z, 3), (z, u, -1), (u, v, 2), (x, t, 1), (t, z, -1)], 
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
	fn test_conflict() {
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
		DifferenceLogicBounds::new_in(&mut slv, vec![(x, y, 3), (y, z, -2), (z, x, -2)], vec![]);
		slv.assert_unsatisfiable();
	}

}
