//! Structure and algorithms for a global difference logic propagator.

use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher, RandomState};
use std::iter::once;
use std::ops::Deref;
use std::rc::Rc;
use itertools::Itertools;
use priority_queue::PriorityQueue;
use tracing::trace;
use crate::solver::activation_list::IntPropCond;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, IntDecision, IntVal};
use crate::actions::InspectionActions;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::{TrailedOpenList, TrailedOpenListIterator};
use crate::solver::trail::TrailedInt;


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of set of difference constraints within a model.
pub struct DifferenceLogic {
	/// todo List of triples (x,y,d) for x-y<=d and list of quadruples (b,x,y,d) for b->x-y<=d ?
	pub(crate) constraints: Vec<(IntDecision, IntDecision, IntVal)>,
	pub(crate) imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// todo can we already do graph simplification here?
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		// todo...
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
	/// Boolean for the difference constraints.
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
	/// List of outgoing edges.
	edges: TrailedList<usize>,
	/// List of incoming edges.
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

#[derive(Clone, PartialEq, Eq)]
/// A hashable reference to a node in the difference logic graph.
pub struct VarNodeRef {
	var: IntView,
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
	graph: HashMap<IntView, VarNodeRef>,
	edges: Vec<DiffEdge>,
	visited: Vec<VarNodeRef>,
}

impl DifferenceLogicGraph {

	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A, int_vars: Vec<IntView>) -> Self {
		Self {
			graph: int_vars.iter().map(|&v| (v, VarNodeRef::new(actions, v))).collect(),
			edges: Vec::new(),
			visited: Vec::new(),
		}
	}

	fn new_edge<P: PropagationActions>(&mut self, actions: &mut P, edge: DiffEdge) -> usize {
		let index = self.edges.len();
		edge.from.node.borrow_mut().edges.push(actions, index);
		edge.to.node.borrow_mut().reverse_edges.push(actions, index);
		self.edges.push(edge);
		index
	}

	fn new_imp_edge(&mut self, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		edge.out_index = edge.from.node.borrow_mut().open_edges.len();
		edge.in_index = edge.to.node.borrow_mut().open_reverse_edges.len();
		edge.from.node.borrow_mut().open_edges.push(self.edges.len());
		edge.to.node.borrow_mut().open_reverse_edges.push(self.edges.len());
		self.edges.push(edge);
		index
	}

	fn add_imp_edge<P: PropagationActions>(&mut self, actions: &mut P, index: usize) {
		let edge = &self.edges[index];
		edge.from.node.borrow_mut().edges.push(actions, index);
		edge.to.node.borrow_mut().reverse_edges.push(actions, index);
	}

	fn close_imp_edge<P: PropagationActions>(&mut self, actions: &mut P, index: usize) -> bool { //todo check this...
		let from = &self.edges[index].from.clone();
		let to = &self.edges[index].to.clone();
		let out_index = self.edges[index].out_index;
		let in_index = self.edges[index].in_index;
		from.node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i) &&
		to.node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i)
	}

	fn close_imp_edge_forward<P: PropagationActions>(&mut self, actions: &mut P, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let _ = open.close(actions, |&e, i| self.edges[e].out_index = i);
		let to = &self.edges[index].to.clone();
		let in_index = self.edges[index].in_index;
		let _ = to.node.borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
	}

	fn close_imp_edge_backward<P: PropagationActions>(&mut self, actions: &mut P, rev_open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let _ = rev_open.close(actions, |&e, i| self.edges[e].in_index = i);
		let from = &self.edges[index].from.clone();
		let out_index = self.edges[index].out_index;
		let _ = from.node.borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i);
	}

	fn visit(&mut self, node: VarNodeRef) {
		node.node.borrow_mut().visited = true;
		self.visited.push(node);
	}

	fn reset_visit(&mut self) {
		for node in self.visited.iter() {
			node.node.borrow_mut().visited = false;
		}
		self.visited.clear();
	}

	fn get_cur_lower_bound<I: InspectionActions>(&self, actions: &I, v: VarNodeRef) -> IntVal {
		let node = v.node.borrow();
		match node.lower_bound {
			Some(lb) => lb,
			None => actions.get_int_lower_bound(v.var),
		}
	}

	fn update_lb(&self, node: VarNodeRef, val: IntVal, lb_updates: &mut Vec<VarNodeRef>) {
		node.node.borrow_mut().lower_bound = Some(val);
		lb_updates.push(node);
	}

	fn reset_lb_updates(&self, lb_updates: &mut Vec<VarNodeRef>) {
		for node in lb_updates.iter() {
			node.node.borrow_mut().lower_bound = None;
		}
		lb_updates.clear();
	}

	fn get_cur_upper_bound<I: InspectionActions>(&self, actions: &I, v: VarNodeRef) -> IntVal {
		let node = v.node.borrow();
		match node.upper_bound {
			Some(ub) => ub,
			None => actions.get_int_upper_bound(v.var),
		}
	}

	fn update_ub(&mut self, node: VarNodeRef, val: IntVal, ub_updates: &mut Vec<VarNodeRef>) {
		node.node.borrow_mut().upper_bound = Some(val);
		ub_updates.push(node);
	}

	fn reset_ub_updates(&mut self, ub_updates: &mut Vec<VarNodeRef>) {
		for node in ub_updates.iter() {
			node.node.borrow_mut().upper_bound = None;
		}
		ub_updates.clear();
	}

	fn get_cycle_reason(&self, node: VarNodeRef) -> Vec<BoolView> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = &var.clone().node.borrow().backtrace {
			reason.push(*b);
			var = cur.clone();
		}
		reason
	}

	fn inc_sat<P: PropagationActions>(&mut self, actions: &mut P, new_index: usize) -> Result<bool, Conflict> {

		let new_edge = &self.edges[new_index];
		trace!("Performing inc_sat on {:?}, {:?}, {:?}", new_edge.from.var, new_edge.to.var, new_edge.val);
		let mut queue = PriorityQueue::new();
		let mut pi_new = HashMap::new(); // todo check if we can modify the potential function in place? Yes, but needs to keep track of updates!
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
				if !pi_new.contains_key(&edge.to.var) || pi_new[&edge.to.var] == node_t.pi {
					let gamma_t = pi_new[&s.var] + edge.val - node_t.pi;
					if gamma_t < 0 {  // todo check need for whole path?
						let old = queue.push_increase(edge.to.clone(), Reverse(gamma_t));
						if old.map_or(true, |Reverse(old_path)| gamma_t < old_path) { //todo check this!
							node_t.backtrace = Some((s.clone(), edge.bool_var));
						}
					}
				}
			}
		}
		if queue.get_priority(&new_edge.from).is_some() {
			trace!("Found cycle with negative length...");
			actions.set_bool(!new_edge.bool_var, self.get_cycle_reason(new_edge.from.clone()))?;
			return Ok(false);
		}
		for (var, val) in pi_new {
			self.graph[&var].node.borrow_mut().pi = val;
		}
		Ok(true)
	}

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

	fn inc_imp<P: PropagationActions>(&mut self, actions: &mut P, new_index: usize) -> Result<(), Conflict> {

		let outgoing_u = self.dijkstra(actions, self.edges[new_index].from.clone(), false);
		let incoming_v = self.dijkstra(actions, self.edges[new_index].to.clone(), true);
		let changed: HashSet<&IntView, RandomState> = HashSet::from_iter(outgoing_u.keys().chain(incoming_v.keys()));  //todo rewrite this!!!
		let new_edge_val = self.edges[new_index].val;
		let mut fail_indices = Vec::new();

		for &n in changed.iter() {
			let temp_node = self.graph[&n].clone();
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

	fn inc_lb<P: PropagationActions>(&mut self, actions: &mut P, v_l: Vec<VarNodeRef>, lb_updates: &mut Vec<VarNodeRef>) -> Result<(), Conflict> {

		trace!("Running inc_lb on {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|n| actions.get_int_lower_bound(n.var) + n.node.borrow().pi).max().unwrap();
		let mut queue = PriorityQueue::new();
		for n in v_l.iter() {
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
					trace!("Updating lower bound for {:?} to {bound}", s.var);  // todo requeue immediately for holes?
					let (prev, b) = node_s.clone().backtrace.unwrap();
					//trace!("Reason is that {prev:?} >= {} conditional on {b:?}", actions.get_trailed_int(self.graph[&prev].lower_bound));
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

	fn inc_ub<P: PropagationActions>(&mut self, actions: &mut P, v_u: Vec<VarNodeRef>, ub_updates: &mut Vec<VarNodeRef>) -> Result<(), Conflict> {

		trace!("Running inc_ub on {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|n| actions.get_int_upper_bound(n.var) + n.node.borrow().pi).min().unwrap();
		let mut queue = PriorityQueue::new();
		for n in v_u.iter() {
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
					trace!("Updating upper bound for {:?} to {bound}", s.var);  // todo requeue immediately for holes?
					let (prev, b) = node_s.clone().backtrace.unwrap();
					//trace!("Reason is that {prev:?} <= {} conditional on {b:?}", actions.get_trailed_int(self.graph[&prev].upper_bound));
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

	fn to_dot<I: InspectionActions>(&self, actions: &mut I) -> String {
		let mut out = "digraph {\n".to_owned();
		for (&var, v) in self.graph.iter() {
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

#[derive(Debug, Clone, PartialEq, Eq)]  // todo do we need Hash here?
/// Bounds consistent global different constraint propagator.
pub struct DifferenceLogicBounds {
	/// Constraint graph.
	graph: DifferenceLogicGraph,
	lb_updates: Vec<VarNodeRef>,
	ub_updates: Vec<VarNodeRef>,
	bool_map: HashMap<BoolView, Vec<usize>>,
	/// List of constraints. todo currently initial list, not to be modified later?
	constraints: Vec<(IntView, IntView, IntVal)>,
	/// List of implied constraints. todo currently initial list, not to be modified later?
	imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>,
	/// List of all integer variables. todo this should not be needed later
	int_vars: Vec<IntView>,
	/// List of all boolean variables. todo this should not be needed later
	bool_vars: Vec<BoolView>,
	lower_bounds: HashMap<IntView, TrailedInt>, // todo temporary
	upper_bounds: HashMap<IntView, TrailedInt>, // todo temporary
	fixed_bools: HashMap<BoolView, TrailedInt>, // todo temporary
}

impl DifferenceLogicBounds {
	//todo check options for queue?

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
		let bool_map = bool_vars.iter().map(|&b| (b, Vec::new())).collect();
		let lower_bounds = int_vars.iter().map(|&x| (x, solver.new_trailed_int(IntVal::MIN))).collect();
		let upper_bounds = int_vars.iter().map(|&x| (x, solver.new_trailed_int(IntVal::MAX))).collect();
		let fixed_bools = bool_vars.iter().map(|&b| (b, solver.new_trailed_int(0))).collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				graph,
				lb_updates: Vec::new(),
				ub_updates: Vec::new(),
				bool_map,
				constraints: constraints.clone(),
				imp_constraints: imp_constraints.clone(),
				int_vars: int_vars.clone(),
				bool_vars: bool_vars.clone(),
				lower_bounds,
				upper_bounds,
				fixed_bools,
			}),
			PriorityLevel::Low, // todo priority (before individual diff constraints?)
		);
		for &v in int_vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
		for &v in bool_vars.iter() {
			solver.enqueue_on_bool_change(prop, v);
		}
		solver.enqueue_now(prop);
	}

	fn propagate_bounds<P: PropagationActions>(&mut self, actions: &mut P, lb_changes: Vec<VarNodeRef>, ub_changes: Vec<VarNodeRef>, mut fixed_bools: Vec<BoolView>) -> Result<(), Conflict> {

		trace!("Propagating bounds on lb changes {lb_changes:?}, ub changes {ub_changes:?}, fixed booleans {fixed_bools:?}.");

		if !lb_changes.is_empty() {
			self.graph.inc_lb(actions, lb_changes, &mut self.lb_updates)?;
		}

		if !ub_changes.is_empty() {
			self.graph.inc_ub(actions, ub_changes, &mut self.ub_updates)?;
		}

		for n in self.lb_updates.iter() {

			let mut node = n.node.borrow_mut();
			let lb = node.lower_bound.unwrap();

			let mut open = node.open_edges.iter(actions);
			while let Some(&index) = open.next() {
				let edge = &self.graph.edges[index];
				let target_ub = self.graph.get_cur_upper_bound(actions, edge.to.clone());
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is falsified by bounds.", edge.bool_var, n.var, edge.to.var, edge.val);
					actions.set_bool(!edge.bool_var, |a: &mut P| vec![a.get_int_lit(n.var, IntLitMeaning::GreaterEq(lb)),
																	  a.get_int_lit(edge.to.var, IntLitMeaning::Less(target_ub + 1))])?;
					fixed_bools.push(!edge.bool_var.clone());
					self.graph.close_imp_edge_forward(actions, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(actions);
			while let Some(&index) = rev_open.next() {
				let edge = &self.graph.edges[index];
				if self.graph.get_cur_upper_bound(actions, edge.from.clone()) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is implied by bounds.", edge.bool_var, edge.from.var, n.var, edge.val);
					self.graph.close_imp_edge_backward(actions, &mut rev_open, index);
				}
			}

		}

		for n in self.ub_updates.iter() {

			let mut node = n.node.borrow_mut();
			let ub = node.upper_bound.unwrap();

			let mut open = node.open_edges.iter(actions);
			while let Some(&index) = open.next() {
				let edge = &self.graph.edges[index];
				if ub - self.graph.get_cur_lower_bound(actions, edge.to.clone()) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is implied by bounds.", edge.bool_var, n.var, edge.to.var, edge.val);
					self.graph.close_imp_edge_forward(actions, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(actions);
			while let Some(&index) = rev_open.next() {
				let edge = &self.graph.edges[index];
				let source_lb = self.graph.get_cur_lower_bound(actions, edge.from.clone());
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} -> {:?} - {:?} <= {:?} is falsified by bounds.", edge.bool_var, edge.from.var, n.var, edge.val);
					actions.set_bool(!edge.bool_var, |a: &mut P| vec![a.get_int_lit(edge.from.var, IntLitMeaning::GreaterEq(source_lb)),
																	  a.get_int_lit(n.var, IntLitMeaning::Less(ub + 1))])?;
					fixed_bools.push(!edge.bool_var.clone());
					self.graph.close_imp_edge_backward(actions, &mut rev_open, index);
				}
			}

		}

		let mut lb_new_changes = Vec::new();
		let mut ub_new_changes = Vec::new();
		for b in fixed_bools.iter() {
			trace!("Boolean {b:?} fixed to true.");
			if let Some(edges) = self.bool_map.get(b) {
				for &index in edges.iter() {
					let edge_closed = self.graph.close_imp_edge(actions, index);
					trace!("Processing adding edge {:?} - {:?} <= {:?} (open: {edge_closed})", self.graph.edges[index].from.var, self.graph.edges[index].to.var, self.graph.edges[index].val);
					if edge_closed {
						if self.graph.inc_sat(actions, index)? {
							self.graph.add_imp_edge(actions, index);
							self.graph.inc_imp(actions, index)?;
							let edge = &self.graph.edges[index];
							let lb_y = -edge.val + self.graph.get_cur_lower_bound(actions, edge.from.clone());
							if lb_y > self.graph.get_cur_lower_bound(actions, edge.to.clone()) {
								lb_new_changes.push(edge.to.clone());
							}
							let ub_x = edge.val + self.graph.get_cur_upper_bound(actions, edge.to.clone());
							if ub_x < self.graph.get_cur_upper_bound(actions, edge.from.clone()) {
								ub_new_changes.push(edge.from.clone());
							}
						}
					}
				}
			}
			let negation = !*b;
			if let Some(edges) = self.bool_map.get(&negation) {
				for &index in edges.iter() {
					let edge_closed = self.graph.close_imp_edge(actions, index);
					trace!("Closing edge {:?} - {:?} <= {:?} (open: {edge_closed})", self.graph.edges[index].from.var, self.graph.edges[index].to.var, self.graph.edges[index].val);
				}
			}
		}

		if !lb_new_changes.is_empty() || !ub_new_changes.is_empty() {
			self.propagate_bounds(actions, lb_new_changes, ub_new_changes, Vec::new())?;
		}

		//trace!("Current graph after implied checks: {}", self.graph.to_dot(actions));

		Ok(())

	}

}

impl<P, E> Propagator<P, E> for DifferenceLogicBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "difference_logic", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {

		//todo empty and reuse vs. recreate for HashMaps, replace with faster implementation in general?
		let mut graph_change = false; //todo remove

		for (b, x, y, d) in self.imp_constraints.iter() {
			let index = self.graph.new_imp_edge(DiffEdge::new(self.graph.graph[x].clone(), self.graph.graph[y].clone(), *d, *b));
			self.bool_map.get_mut(b).unwrap().push(index);
		}
		self.imp_constraints.clear();

		for (x, y, d) in self.constraints.iter() {  // todo this should be done earlier and simplified in the process
			graph_change = true;
			let edge = DiffEdge::new(self.graph.graph[x].clone(), self.graph.graph[y].clone(), *d, BoolView::from(true));
			let index = self.graph.new_edge(actions, edge);
			let _ = self.graph.inc_sat(actions, index)?;
			self.graph.inc_imp(actions, index)?;
		}
		self.constraints.clear();

		self.graph.reset_lb_updates(&mut self.lb_updates);  // todo check how this works with recursion!
		self.graph.reset_ub_updates(&mut self.ub_updates);

		// todo replace once we know what actually changed...
		let lb_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_lower_bound(*v) > actions.get_trailed_int(self.lower_bounds[v]))
			.map(|&v| self.graph.graph[&v].clone())
			.collect();

		// todo replace once we know what actually changed...
		let ub_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_upper_bound(*v) < actions.get_trailed_int(self.upper_bounds[v]))
			.map(|&v| self.graph.graph[&v].clone())
			.collect();

		// todo replace once we know what actually changed...
		let bool_changes = self.bool_vars.iter()
			.filter(|&b| actions.get_trailed_int(self.fixed_bools[b]) == 0 && actions.get_bool_val(*b).is_some())
			.map(|&b| if actions.get_bool_val(b).unwrap() { b } else { !b })
			.unique()
			.collect::<Vec<_>>();

		/*trace!("Full state before propagate bounds:");
		for (v, node) in self.graph.graph.iter() {
			trace!("{v:?}: {:?}", node.node.borrow().deref());
		}
		for edge in self.graph.edges.iter() {
			trace!("{edge:?}");
		}*/

		self.propagate_bounds(actions, lb_changes, ub_changes, bool_changes.clone())?;

		for l in self.lb_updates.iter() {
			let _ = actions.set_trailed_int(self.lower_bounds[&l.var], l.node.borrow().lower_bound.unwrap());
		}

		for u in self.ub_updates.iter() {
			let _ = actions.set_trailed_int(self.upper_bounds[&u.var], u.node.borrow().upper_bound.unwrap());
		}

		for b in bool_changes {
			if self.fixed_bools.contains_key(&b) {
				let _ = actions.set_trailed_int(self.fixed_bools[&b], 1);
			}
			let negation = !b;
			if self.fixed_bools.contains_key(&negation) {
				let _ = actions.set_trailed_int(self.fixed_bools[&negation], 1);
			}
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
