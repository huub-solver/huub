//! Structure and algorithms for a global difference logic propagator.

use std::cmp::Reverse;
use std::collections::HashMap;
use std::iter::once;
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
use crate::helpers::trailed_skip_list::TrailedSkipList;
use crate::solver::trail::TrailedInt;


fn get_cur_lower_bound<I: InspectionActions>(actions: &I, new_lbs: &mut HashMap<IntView, IntVal>, v: IntView) -> IntVal {
	new_lbs.get(&v).cloned().unwrap_or_else(|| actions.get_int_lower_bound(v))
}

fn get_cur_upper_bound<I: InspectionActions>(actions: &I, new_ubs: &mut HashMap<IntView, IntVal>, v: IntView) -> IntVal {
	new_ubs.get(&v).cloned().unwrap_or_else(|| actions.get_int_upper_bound(v))
}

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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
/// An edge in the difference logic graph.
pub struct DiffEdge {
	/// Target variable.
	node: IntView,
	/// Difference value.
	val: IntVal,
	/// Boolean for the difference constraints.
	bool_var: BoolView,
}

impl DiffEdge {

	fn new(to_node: IntView, val: IntVal, bool_var: BoolView) -> Self {
		Self {
			node: to_node,
			val,
			bool_var,
		}
	}

}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A node in the difference logic graph.
pub struct VarNode {
	/// Associated variable.
	var: IntView,
	/// List of outgoing edges.
	edges: TrailedList<DiffEdge>,
	/// List of incoming edges.
	reverse_edges: TrailedList<DiffEdge>,
	/// Potential function value.
	pi: IntVal,
}

impl VarNode {

	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A, var: IntView) -> Self {
		Self {
			var,
			edges: TrailedList::new(actions),
			reverse_edges: TrailedList::new(actions),
			pi: 0,
		}
	}

}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A graph of difference constraints.
pub struct DifferenceLogicGraph {
	graph: HashMap<IntView, VarNode>,
}

impl DifferenceLogicGraph {

	fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A, variables: Vec<IntView>) -> Self {
		Self {
			graph: variables.iter().map(|&v| (v, VarNode::new(actions, v))).collect(),
		}
	}

	fn add_edge<P: PropagationActions>(&mut self, actions: &mut P, u: IntView, v: IntView, d: IntVal, b: BoolView) {
		self.graph.get_mut(&u).unwrap().edges.push(actions, DiffEdge::new(v, d, b));
		self.graph.get_mut(&v).unwrap().reverse_edges.push(actions, DiffEdge::new(u, d, b));
	}

	fn get_cycle_reason(&mut self, node: IntView, backtrace: HashMap<IntView, (IntView, DiffEdge)>) -> Vec<BoolView> {
		let mut reason = Vec::new();
		let mut var = node;
		loop {
			let (cur, edge) = backtrace[&var];
			reason.push(edge.bool_var);
			var = cur;
			if !backtrace.contains_key(&var) {
				break reason;
			}
		}
	}

	fn inc_sat<P: PropagationActions>(&mut self, actions: &mut P, u: IntView, v: IntView, d: IntVal, b: Option<BoolView>) -> Result<bool, Conflict> {

		trace!("Performing inc_sat on {u:?}, {v:?}, {d:?}");
		let mut queue = PriorityQueue::new();
		let mut pi_new = HashMap::new(); // todo check if we can modify the potential function in place? Yes, but needs to keep track of updates!
		let mut backtrace = HashMap::new();
		let gamma_v = self.graph[&u].pi + d - self.graph[&v].pi;
		if gamma_v < 0 {
			let _ = queue.push(v, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&u).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = pi_new.insert(s, self.graph[&s].pi + gamma_s);  // todo is it worth storing self.graph[&s]?
			for &edge in self.graph[&s].edges.iter(actions) {
				if !pi_new.contains_key(&edge.node) || pi_new[&edge.node] == self.graph[&edge.node].pi {
					let gamma_t = pi_new[&s] + edge.val - self.graph[&edge.node].pi;
					if gamma_t < 0 {  // todo check need for whole path?
						let old = queue.push_increase(edge.node, Reverse(gamma_t));
						if old.map_or(true, |Reverse(old_path)| gamma_t < old_path) {
							let _ = backtrace.insert(edge.node, (s, edge));
						}
					}
				}
			}
		}
		if queue.get_priority(&u).is_some() {
			trace!("Found cycle with negative length...");
			return if let Some(b) = b {
				actions.set_bool(!b, self.get_cycle_reason(u, backtrace))?;
				Ok(false)
			} else {
				Err(Conflict::new(actions, None, self.get_cycle_reason(u, backtrace)))  // todo what if reason is empty?
			}
		}
		for (var, val) in pi_new {
			self.graph.get_mut(&var).unwrap().pi = val;  // todo is this good?
		}
		Ok(true)
	}

	fn dijkstra<P: PropagationActions>(&mut self, actions: &mut P, source: IntView, reverse: bool) -> HashMap<IntView, IntVal> {

		trace!("Starting dijkstra for {source:?} in mode reverse={reverse}");
		let mut distances = HashMap::new();
		let mut queue = PriorityQueue::new();
		let _ = distances.insert(source, 0);
		let _ = queue.push(source, Reverse(0));
		while !queue.is_empty() {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			//trace!("dijkstra on current node {s:?} with dist {dist}");
			for &edge in if reverse {self.graph[&s].edges.iter(actions)} else {self.graph[&s].reverse_edges.iter(actions)} {
				let new_dist = dist + edge.val + ((self.graph[&s].pi - self.graph[&edge.node].pi) * if reverse {-1} else {1});
				if !distances.contains_key(&edge.node) || distances[&edge.node] > new_dist {
					let _ = queue.push(edge.node, Reverse(new_dist));
					//trace!("dijkstra adding node {:?} with dist {new_dist}", edge.node);
				}
			}
		}
		distances

	}

	fn inc_imp<P: PropagationActions>(&mut self, actions: &mut P, imp_constraints: &TrailedSkipList<(BoolView, IntView, IntView, IntVal)>,
									  u: IntView, v: IntView, d: IntVal) -> Result<(), Conflict> {
		let outgoing_u = self.dijkstra(actions, u, false);
		let incoming_v = self.dijkstra(actions, v, true);
		let mut imp_iter = imp_constraints.iter::<P>();
		while let Some((b, x, y, d_i)) = imp_iter.next(actions) {
			if outgoing_u.contains_key(x) && incoming_v.contains_key(y) && outgoing_u[x] + d + incoming_v[y] <= *d_i { //todo better formulation?
				trace!("Constraint {x:?} - {y:?} <= {d} is implied");
				imp_iter.remove(actions);
			} else if outgoing_u.contains_key(y) && incoming_v.contains_key(x) && outgoing_u[y] + d + incoming_v[x] <= -*d_i - 1 { // todo slight double work for reified constraints
				trace!("Constraint {y:?} - {x:?} <= {d} is falsified since inverse is implied");
				let _ = self.inc_sat(actions, *x, *y, *d_i, Some(*b))?;
				imp_iter.remove(actions);
			}
		}
		Ok(())
	}

	fn inc_lb<P: PropagationActions>(&mut self, actions: &mut P, v_l: Vec<IntView>, new_lbs: &mut HashMap<IntView, IntVal>) -> Result<(), Conflict> {

		trace!("Running inc_lb on {v_l:?}");
		let pi0 = v_l.iter().map(|&v| actions.get_int_lower_bound(v) + self.graph[&v].pi).max().unwrap();  // todo store get_int_lower_bound directly?
		let mut queue = PriorityQueue::new();
		// todo Could we put this node-based data into the node infrastructure? And just always overwrite it there? Saves more HashMaps... could also include new_lbs
		let mut lb = HashMap::new(); // todo this is actually just a visited boolean in this case
		let mut backtrace = HashMap::new();
		for &v in v_l.iter() {
			let _ = queue.push(v, Reverse(pi0 - actions.get_int_lower_bound(v) - self.graph[&v].pi));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = lb.insert(s, gamma_s);
			let bound = pi0 - gamma_s - self.graph[&s].pi;
			if bound > get_cur_lower_bound(actions, new_lbs, s) {
				if bound > actions.get_int_lower_bound(s) {
					trace!("Updating lower bound for {s:?} to {bound}");
					let (prev, b) = backtrace[&s];
					//trace!("Reason is that {prev:?} >= {} conditional on {b:?}", actions.get_trailed_int(self.graph[&prev].lower_bound));
					actions.set_int_lower_bound(s, bound, |a: &mut P| vec![b, a.get_int_lit(prev, IntLitMeaning::GreaterEq(new_lbs[&prev]))])?;

				}
				let _ = new_lbs.insert(s, bound);  // todo requeue immediately for holes?
				for &edge in self.graph[&s].edges.iter(actions) {
					if !lb.contains_key(&edge.node) {
						let path = gamma_s + self.graph[&s].pi + edge.val - self.graph[&edge.node].pi;
						let old = queue.push_increase(edge.node, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							let _ = backtrace.insert(edge.node, (s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	fn inc_ub<P: PropagationActions>(&mut self, actions: &mut P, v_u: Vec<IntView>, new_ubs: &mut HashMap<IntView, IntVal>) -> Result<(), Conflict> {

		trace!("Running inc_ub on {v_u:?}");
		let pi0 = v_u.iter().map(|&v| actions.get_int_upper_bound(v) + self.graph[&v].pi).min().unwrap();
		let mut queue = PriorityQueue::new();
		let mut ub = HashMap::new();
		let mut backtrace = HashMap::new();
		for &v in v_u.iter() {
			let _ = queue.push(v, Reverse(self.graph[&v].pi + actions.get_int_upper_bound(v) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = ub.insert(s, gamma_s);
			let bound = pi0 + gamma_s - self.graph[&s].pi;
			if bound < get_cur_upper_bound(actions, new_ubs, s) {
				if bound < actions.get_int_upper_bound(s) {
					trace!("Updating upper bound for {s:?} to {bound}");
					let (prev, b) = backtrace[&s];
					//trace!("Reason is that {prev:?} <= {} conditional on {b:?}", actions.get_trailed_int(self.graph[&prev].upper_bound));
					actions.set_int_upper_bound(s, bound, |a: &mut P| vec![b, a.get_int_lit(prev, IntLitMeaning::Less(new_ubs[&prev] + 1))])?;

				}
				let _ = new_ubs.insert(s, bound);  // todo requeue immediately for holes?
				for &edge in self.graph[&s].reverse_edges.iter(actions) {
					if !ub.contains_key(&edge.node) {
						let path = gamma_s + self.graph[&edge.node].pi + edge.val - self.graph[&s].pi;
						let old = queue.push_increase(edge.node, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							let _ = backtrace.insert(edge.node, (s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	fn to_dot<I: InspectionActions>(&self, actions: &mut I, new_lbs: &mut HashMap<IntView, IntVal>, new_ubs: &mut HashMap<IntView, IntVal>) -> String {
		let mut out = "digraph {\n".to_owned();
		for (&var, node) in self.graph.iter() {
			out.push_str(format!("\"{var:?}\" [label=\"{var:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 get_cur_lower_bound(actions, new_lbs, var),
								 get_cur_upper_bound(actions, new_ubs, var),
								 node.pi).as_str());
			for &edge in node.edges.iter(actions) {
				out.push_str(format!("\"{var:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n", edge.node, edge.val, edge.bool_var).as_str());
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
	/// List of constraints. todo currently initial list, not to be modified later?
	constraints: Vec<(IntView, IntView, IntVal)>,
	/// List of implied constraints. todo current trailing infrastructure requires known length?
	imp_constraints: TrailedSkipList<(BoolView, IntView, IntView, IntVal)>,
	/// List of all integer variables. todo this should not be needed later
	int_vars: Vec<IntView>,
	/// List of all boolean variables. todo this should not be needed later
	bool_vars: Vec<BoolView>,
	lower_bounds: HashMap<IntView, TrailedInt>, // todo temporary
	upper_bounds: HashMap<IntView, TrailedInt>, // todo temporary
}

impl DifferenceLogicBounds {
	//todo check options for queue?

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P,
													 constraints: Vec<(IntView, IntView, IntVal)>,  // todo capture all options: int_lin_le(_imp,_reif), int_le(_imp,_reif), also equality and non-equality?
													 imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>) {

		let mut int_vars = constraints.iter().flat_map(|(x, y, _)| once(*x).chain(once(*y))).collect::<Vec<_>>();
		int_vars.extend(imp_constraints.iter().flat_map(|(_, x, y, _)| once(*x).chain(once(*y))).collect::<Vec<_>>());
		int_vars.sort();
		int_vars.dedup();

		let bool_vars = imp_constraints.iter().map(|(b, _, _, _)| *b).collect::<Vec<_>>();

		// todo init all or add dynamically?
		let graph = DifferenceLogicGraph::new(solver, int_vars.clone());
		let trailed_imp_constraints = TrailedSkipList::from(imp_constraints, solver);
		let lower_bounds = int_vars.iter().map(|&x| (x, solver.new_trailed_int(IntVal::MIN))).collect();
		let upper_bounds = int_vars.iter().map(|&x| (x, solver.new_trailed_int(IntVal::MAX))).collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				graph,
				constraints: constraints.clone(),
				imp_constraints: trailed_imp_constraints,
				int_vars: int_vars.clone(),
				bool_vars: bool_vars.clone(),
				lower_bounds,
				upper_bounds,
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

	fn propagate_bounds<P: PropagationActions>(&mut self, actions: &mut P, lb_changes: Vec<IntView>, ub_changes: Vec<IntView>,
											   new_lbs: &mut HashMap<IntView, IntVal>, new_ubs: &mut HashMap<IntView, IntVal>) -> Result<(), Conflict> {

		trace!("Propagating bounds on {lb_changes:?} and {ub_changes:?}");

		if !lb_changes.is_empty() {
			self.graph.inc_lb(actions, lb_changes, new_lbs)?;
		}

		if !ub_changes.is_empty() {
			self.graph.inc_ub(actions, ub_changes, new_ubs)?;
		}

		let mut lb_new_changes = Vec::new();
		let mut ub_new_changes = Vec::new();

		// todo only iterate relevant constraints
		let mut imp_iter = self.imp_constraints.iter::<P>();
		while let Some((b, x, y, d)) = imp_iter.next(actions) {
			let (b, x, y, d) = (*b, *x, *y, *d);
			if get_cur_upper_bound(actions, new_ubs, x) - get_cur_lower_bound(actions, new_lbs, y) <= d {
				// Constraint is implied by bounds.
				trace!("Constraint {b:?} -> {x:?} - {y:?} <= {d:?} is implied by bounds.");
				imp_iter.remove(actions);
			} else if get_cur_lower_bound(actions, new_lbs, x) - get_cur_upper_bound(actions, new_ubs, y) > d {
				// Constraint is falsified by bounds.
				trace!("Constraint {b:?} -> {x:?} - {y:?} <= {d:?} is falsified by bounds.");
				actions.set_bool(!b, |a: &mut P| vec![a.get_int_lit(x, IntLitMeaning::GreaterEq(get_cur_lower_bound(a, new_lbs, x))),
													  a.get_int_lit(y, IntLitMeaning::Less(get_cur_upper_bound(a, new_ubs, y) + 1))])?;
				imp_iter.remove(actions);
			} else if let Some(val) = actions.get_bool_val(b) { //todo extract bool propagations from this method. Also check if we want to do manual bool updates for our own propagations?
				trace!("Constraint {b:?} -> {x:?} - {y:?} <= {d:?} has fixed boolean value {val:?}.");
				imp_iter.remove(actions);
				if val {
					trace!("Adding {x:?} - {y:?} <= {d:?}");
					if self.graph.inc_sat(actions, x, y, d, Some(b))? {
						self.graph.add_edge(actions, x, y, d, b); // todo what if constraint is implied?
						self.graph.inc_imp(actions, &self.imp_constraints, x, y, d)?;
						let lb_y = -d + get_cur_lower_bound(actions, new_lbs, x);  //todo loop to updates immediately or at the end?
						if lb_y > get_cur_lower_bound(actions, new_lbs, y) {
							lb_new_changes.push(y);
						}
						let ub_x = d + get_cur_upper_bound(actions, new_ubs, y);
						if ub_x < get_cur_upper_bound(actions, new_ubs, x) {
							ub_new_changes.push(x);
						}
					}
				}
			}
		}

		if !lb_new_changes.is_empty() || !ub_new_changes.is_empty() {
			self.propagate_bounds(actions, lb_new_changes, ub_new_changes, new_lbs, new_ubs)?;
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

		for (x, y, d) in self.constraints.iter() {
			graph_change = true;
			let _ = self.graph.inc_sat(actions, *x, *y, *d, None)?;  // todo do we want to remove edges that are not necessary? At least in the beginning?
			self.graph.add_edge(actions, *x, *y, *d, BoolView::from(true)); // todo what if constraint is implied?
			self.graph.inc_imp(actions, &self.imp_constraints, *x, *y, *d)?;
		}
		self.constraints.clear();

		// todo replace once we know what actually changed...
		let lb_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_lower_bound(*v) > actions.get_trailed_int(self.lower_bounds[v]))
			.map(|&v| v)
			.collect();
		let mut new_lbs = lb_changes.iter().map(|&v| (v, IntVal::MIN)).collect(); //todo check type
		
		// todo replace once we know what actually changed...
		let ub_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_upper_bound(*v) < actions.get_trailed_int(self.upper_bounds[v]))
			.map(|&v| v)
			.collect();
		let mut new_ubs = ub_changes.iter().map(|&v| (v, IntVal::MAX)).collect();
		
		self.propagate_bounds(actions, lb_changes, ub_changes, &mut new_lbs, &mut new_ubs)?;
		
		if graph_change {
			trace!("Initial graph: {}", self.graph.to_dot(actions, &mut new_lbs, &mut new_ubs));
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
			trace!("Checking x = {}, y = {}, z = {}, b = {}", x, y, z, b);
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
