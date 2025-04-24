//! Structure and algorithms for a global difference logic propagator.

use std::cmp::Reverse;
use petgraph::graphmap::DiGraphMap;
use std::collections::HashMap;
use std::hash::RandomState;
use std::iter::once;
use petgraph::Direction;
use petgraph::dot::{Config, Dot};
use priority_queue::PriorityQueue;
use tracing::trace;
use crate::solver::activation_list::IntPropCond;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, IntDecision, IntVal};
use crate::solver::trail::TrailedInt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of set of difference constraints within a model.
pub struct DifferenceLogic {
	/// todo List of triples (x,y,d) for x-y<=d and list of quadruples (b,x,y,d) for b->x-y<=d ?
	pub(crate) constraints: Vec<(IntDecision, IntDecision, IntVal)>,
	pub(crate) imp_constraints: Vec<(BoolDecision, IntDecision, IntDecision, IntVal)>,
}

#[derive(Debug, Clone)]  // todo do we need PartialEq, Eq, Hash here?
/// Bounds consistent global different constraint propagator.
pub struct DifferenceLogicBounds {
	graph: DiGraphMap<IntView, IntVal, RandomState>,
	pi: HashMap<IntView, IntVal>,
	constraints: Vec<(IntView, IntView, IntVal)>,
	imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>,
	int_vars: Vec<IntView>,
	lower_bounds: HashMap<IntView, TrailedInt>,
	upper_bounds: HashMap<IntView, TrailedInt>,
	bool_vars: Vec<BoolView>,
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// todo...
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		// todo...
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

impl DifferenceLogicBounds {
	//todo check options for queue?

	fn inc_sat<P: PropagationActions>(&mut self, actions: &mut P, u: IntView, v: IntView, d: IntVal) -> Result<(), Conflict> {

		trace!("Performing inc_sat on {u:?}, {v:?}, {d:?}");
		let mut queue = PriorityQueue::new();
		let mut pi_new = HashMap::new(); // todo check if we can modify the potential function in place?
		let gamma_v = self.pi[&u] + d - self.pi[&v];
		if gamma_v < 0 {
			let _ = queue.push(v, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&u).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = pi_new.insert(s, self.pi[&s] + gamma_s);
			for (_, t, &d_e) in self.graph.edges(s) {
				if !pi_new.contains_key(&t) || pi_new[&t] == self.pi[&t] {
					let gamma_t = pi_new[&s] + d_e - self.pi[&t];
					if gamma_t < 0 {
						let _ = queue.push_increase(t, Reverse(gamma_t));
					}
				}
			}
		}
		if queue.get_priority(&u).is_some() {
			trace!("Found cycle with negative length...");
			return Err(Conflict::new(actions, None, actions.deferred_reason(0)));  // todo...
		}
		let _ = self.graph.add_edge(u, v, d); // todo what if edge was already there? What is constraint is implied?
		for (var, val) in pi_new {
			let _ = self.pi.insert(var, val);
		}
		Ok(())
	}

	fn dijkstra(&mut self, source: IntView, reverse: bool) -> HashMap<IntView, IntVal> {

		trace!("Starting dijkstra for {source:?} in mode reverse={reverse}");
		let mut distances = HashMap::new();
		let mut queue = PriorityQueue::new();
		let _ = distances.insert(source, 0);
		let _ = queue.push(source, Reverse(0));
		while !queue.is_empty() {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			trace!("dijkstra on current node {s:?} with dist {dist}");
			for (n1, n2, &d) in self.graph.edges_directed(s, if reverse {Direction::Incoming} else {Direction::Outgoing}) {
				let new_dist = dist + self.pi[&n1] + d - self.pi[&n2];  // todo store rc directly?
				let t = if reverse { n1 } else { n2 };
				if !distances.contains_key(&t) || distances[&t] > new_dist {
					let _ = queue.push(t, Reverse(new_dist));
					trace!("dijkstra adding node {t:?} with dist {new_dist}");
				}
			}
		}
		distances

	}

	fn inc_imp<P: PropagationActions>(&mut self, actions: &mut P, u: IntView, v: IntView, d: IntVal) -> Result<(), Conflict> {
		let outgoing_u = self.dijkstra(u, false);
		let incoming_v = self.dijkstra(v, true);
		for (b, x, y, d_i) in self.imp_constraints.iter() {
			if outgoing_u.contains_key(x) && incoming_v.contains_key(y) && outgoing_u[x] + d + incoming_v[y] <= *d_i { //todo better formulation?
				trace!("Constraint {x:?} - {y:?} <= {d} is implied");
				//actions.set_bool(*b, actions.deferred_reason(0))? // todo explain!
			}
		}
		Ok(())
	}

	fn inc_lb<P: PropagationActions>(&mut self, actions: &mut P, v_l: Vec<IntView>) -> Result<(), Conflict> {
		
		trace!("Running inc_lb on {v_l:?}");
		//trace!("pi is {:?}", self.pi);
		let pi0 = v_l.iter().map(|&v| actions.get_int_lower_bound(v) + self.pi[&v]).max().unwrap();  // todo store get_int_lower_bound directly?
		let mut queue = PriorityQueue::new();
		let mut lb = HashMap::new();  //todo empty and reuse vs. recreate?
		let mut backtrace = HashMap::new();
		for &v in v_l.iter() {
			let _ = queue.push(v, Reverse(pi0 - actions.get_int_lower_bound(v) - self.pi[&v]));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = lb.insert(s, gamma_s);
			let bound = pi0 - gamma_s - self.pi[&s];
			if bound > actions.get_trailed_int(self.lower_bounds[&s]) {
				if bound > actions.get_int_lower_bound(s) {
					trace!("Updating lower bound for {s:?} to {bound}");
					let prev = backtrace[&s];
					trace!("Reason is that {prev:?} >= {}", actions.get_trailed_int(self.lower_bounds[&prev]));
					actions.set_int_lower_bound(s, bound, |a: &mut P| vec![a.get_int_lit(prev, IntLitMeaning::GreaterEq(a.get_trailed_int(self.lower_bounds[&prev])))])?;

				}
				let _ = actions.set_trailed_int(self.lower_bounds[&s], bound);  // todo requeue immediately for holes?
				for (_, t, &d_e) in self.graph.edges(s) {
					if !lb.contains_key(&t) {
						let path = gamma_s + self.pi[&s] + d_e - self.pi[&t];
						let old = queue.push_increase(t, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							let _ = backtrace.insert(t, s);
						}
					}
				}
			}
		}
		Ok(())
	}

	fn inc_ub<P: PropagationActions>(&mut self, actions: &mut P, v_u: Vec<IntView>) -> Result<(), Conflict> {

		trace!("Running inc_ub on {v_u:?}");
		let pi0 = v_u.iter().map(|&v| actions.get_int_upper_bound(v) + self.pi[&v]).min().unwrap(); //todo recalculate or store?
		let mut queue = PriorityQueue::new();
		let mut ub = HashMap::new();
		let mut backtrace = HashMap::new();
		for &v in v_u.iter() {
			let _ = queue.push(v, Reverse(self.pi[&v] + actions.get_int_upper_bound(v) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = ub.insert(s, gamma_s);
			let bound = pi0 + gamma_s - self.pi[&s];
			if bound < actions.get_trailed_int(self.upper_bounds[&s]) {
				if bound < actions.get_int_upper_bound(s) {
					trace!("Updating upper bound for {s:?} to {bound}");
					let prev = backtrace[&s];
					trace!("Reason is that {prev:?} <= {}", actions.get_trailed_int(self.upper_bounds[&prev]));
					actions.set_int_upper_bound(s, bound, |a: &mut P| vec![a.get_int_lit(prev, IntLitMeaning::Less(a.get_trailed_int(self.upper_bounds[&prev]) + 1))])?;

				}
				let _ = actions.set_trailed_int(self.upper_bounds[&s], bound);  // todo requeue immediately for holes?
				for (t, _, &d_e) in self.graph.edges_directed(s, Direction::Incoming) {
					if !ub.contains_key(&t) {
						let path = gamma_s + self.pi[&t] + d_e - self.pi[&s];
						let old = queue.push_increase(t, Reverse(path));
						if old.map_or(true, |Reverse(old_path)| path < old_path) {
							let _ = backtrace.insert(t, s);
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P,
													 constraints: Vec<(IntView, IntView, IntVal)>,
													 imp_constraints: Vec<(BoolView, IntView, IntView, IntVal)>) {

		let mut int_vars = constraints.iter().flat_map(|(x, y, _)| once(*x).chain(once(*y))).collect::<Vec<_>>();
		int_vars.extend(imp_constraints.iter().flat_map(|(_, x, y, _)| once(*x).chain(once(*y))).collect::<Vec<_>>());
		int_vars.sort();
		int_vars.dedup();
		let lower_bounds = int_vars.iter().map(|&v| (v, solver.new_trailed_int(IntVal::MIN))).collect();
		let upper_bounds = int_vars.iter().map(|&v| (v, solver.new_trailed_int(IntVal::MAX))).collect();

		let bool_vars = imp_constraints.iter().map(|(b, _, _, _)| *b).collect::<Vec<_>>();

		let graph = DiGraphMap::new();
		// todo init all or add dynamically?
		let pi = int_vars.iter().map(|&v| (v, 0)).collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				graph,
				pi,
				constraints: constraints.clone(),
				imp_constraints: imp_constraints.clone(),
				int_vars: int_vars.clone(),
				lower_bounds,
				upper_bounds,
				bool_vars: bool_vars.clone(),
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

}

impl<P, E> Propagator<P, E> for DifferenceLogicBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "difference_logic", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {

		// todo look for changes of booleans, include implied constraints...
		for (x, y, d) in self.constraints.clone().iter() { //todo prevent clone
			self.inc_sat(actions, *x, *y, *d)?;
			self.inc_imp(actions, *x, *y, *d)?;  // todo do we want to remove edges that are not necessary? At least in the beginning?
			trace!("Current graph: {:?}", Dot::with_attr_getters(&self.graph,
				&[Config::NodeNoLabel, Config::EdgeNoLabel],
				&|_, edge| format!("label = \"{:?}\"", edge.2),
				&|_, node| format!("label = \"{:?}: {:?}\"", node.0, self.pi[&node.0])));
		}
		self.constraints.clear();

		// todo replace once we know what actually changed...
		let lb_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_lower_bound(*v) > actions.get_trailed_int(self.lower_bounds[v]))
			.map(|&v| v)
			.collect();
		if !lb_changes.is_empty() {
			self.inc_lb(actions, lb_changes)?;
		}

		// todo replace once we know what actually changed...
		let ub_changes: Vec<_> = self.int_vars.iter()
			.filter(|&v| actions.get_int_upper_bound(*v) < actions.get_trailed_int(self.upper_bounds[v]))
			.map(|&v| v)
			.collect();
		if !ub_changes.is_empty() {
			self.inc_ub(actions, ub_changes)?;
		}

		//panic!("Not further at the moment...");
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::DifferenceLogicBounds;
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, Model};
	use crate::reformulate::InitConfig;
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
		DifferenceLogicBounds::new_in(&mut slv, vec![(x, y, -2), (y, z, 3)], vec![(b, y, z, 4)]);
		slv.assert_all_solutions(&[x, y, z], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			x - y <= -2 && y - z <= 3
		});
	}

	#[test]
	#[traced_test]
	fn test_paper_medium() {
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
		let u = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let v = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let t = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		DifferenceLogicBounds::new_in(&mut slv, vec![(x, y, -2), (y, z, 3), (z, u, -1), (u, v, 2), (x, t, 1), (t, z, -1)], vec![(b, y, z, 4)]);
		slv.assert_all_solutions(&[x, y, z, u, v, t], move |sol| {
			let Int(x) = sol[0] else { return false };
			let Int(y) = sol[1] else { return false };
			let Int(z) = sol[2] else { return false };
			let Int(u) = sol[3] else { return false };
			let Int(v) = sol[4] else { return false };
			let Int(t) = sol[5] else { return false };
			x - y <= -2 && y - z <= 3 && z - u <= -1 && u - v <= 2 && x - t <= 1 && t - z <= -1
		});
	}

}
