//! Structure and algorithms for a global difference logic propagator.

use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Reverse;
use std::fmt::Debug;
use std::hash::Hash;
use std::mem;
use std::ops::DerefMut;
use std::rc::Rc;
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rustc_hash::FxBuildHasher;
use tracing::trace;
use crate::solver::activation_list::IntPropCond;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, BoolFormula, IntDecision, IntVal, Model};
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
	/// Initial difference logic graph for simplification stage
	initial_graph: Option<DifferenceLogicInitial>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// The initial difference logic structure for model simplification.
struct DifferenceLogicInitial {
	/// Initial trail.
	initial_trail: InitialTrail,
	/// Constraint graph.
	graph: DifferenceLogicGraph,
	/// Propagator state data.
	state: DifferenceLogicState,
	/// Integer decision variables.
	int_vars: Vec<IntDecision>,
	/// Boolean decision variables.
	bool_vars: Vec<BoolDecision>,
}

/// Transform an implied not equals constraint to implied difference constraints by introducing 2 new boolean decision variables.
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
			initial_graph: None,
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

/// Add the given var to the index map if not present and return the new index, or return the 
/// existing index if already present.
fn var_to_index<V: Hash + Eq>(map: &mut IndexMap<V, usize>, var: V) -> usize {
	if let Some(i) = map.get(&var) {
		return *i;
	}
	let index = map.len();
	let _ = map.insert(var, index);
	index
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {

		let mut int_var_map = IndexMap::default();
		let mut trimmed_constraints = Vec::new();
		let mut bool_var_map = IndexMap::default();
		let mut trimmed_imp_constraints = Vec::new();

		// TODO some variables could already be fixed?
		for &(x, y, d) in self.global_constraints.iter() {
			if x == y {
				trace!("Decisions {x:?} and {y:?} (<= {d:?}) are equal");
				if d < 0 {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else {
					continue;
				}
			}
			trimmed_constraints.push((var_to_index(&mut int_var_map, x),
									  var_to_index(&mut int_var_map, y), d));
		}

		// TODO check for fixed variables as well?
		for &(b, x, y, d) in self.imp_constraints.iter() {
			if x == y {
				trace!("Decisions {x:?} and {y:?} (implied by {b:?}, <= {d:?}) are equal");
				if d < 0 {
					actions.set_bool(!b)?;
				}
				continue;
			}
			if let Some(val) = actions.get_bool_val(b) {
				// Boolean is already fixed: Global constraint if true, skipped if false.
				trace!("Fixed boolean {b:?} ({val}) for {x:?} - {y:?} <= {d:?}");
				if val {
					trimmed_constraints.push((var_to_index(&mut int_var_map, x),
											  var_to_index(&mut int_var_map, y), d));
				}
			} else {
				trimmed_imp_constraints.push((var_to_index(&mut bool_var_map, b),
											  var_to_index(&mut int_var_map, x),
											  var_to_index(&mut int_var_map, y), d));
			}
		}

		trace!("Creating DifferenceLogicGraph for {} int and {} bool vars, {} global and {} implied edges.", int_var_map.len(), bool_var_map.len(), trimmed_constraints.len(), trimmed_imp_constraints.len());
		let mut initial_trail = InitialTrail::new();
		let mut graph = DifferenceLogicGraph::new(&mut initial_trail, int_var_map.len(), bool_var_map.len());
		let int_vars = int_var_map.iter().map(|(&v, _)| v).collect_vec();
		let bool_vars = bool_var_map.iter().map(|(&v, _)| v).collect_vec();
		let mut model_adapter = SimplificationModelAdapter::new(actions, &mut initial_trail, &int_vars, &bool_vars);
		let mut state = DifferenceLogicState::new(int_vars.len());

		// Add global constraints
		for (x, y, d) in trimmed_constraints.into_iter() {
			let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(x, y, d, None));
		}

		// Add implied constraints
		for (b, x, y, d) in trimmed_imp_constraints.into_iter() {
			let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(x, y, d, Some(b)));
		}
		
		trace!("Starting initial propagation with graph: {}", graph.to_dot(&mut model_adapter));
		graph.bellman_ford_init_pi(&mut model_adapter)?;
		graph.propagate_bounds(&mut model_adapter, &mut state)?;
		graph.check_remove_fixed_nodes(&mut model_adapter);  //TODO position here? Or just at the end?
		graph.propagate_booleans(&mut model_adapter, &mut state, false)?;
		graph.johnson_full(&mut model_adapter)?;
		graph.check_remove_isolated_nodes(&mut model_adapter);
		graph.check_remove_isolated_booleans(&mut model_adapter);

		trace!("Initial graph: {}", graph.to_dot(&mut model_adapter));
		/*trace!("Implied edges:");
		for node in graph.nodes.iter() {
			let mut node_ref = node.node.borrow_mut();
			let mut open = node_ref.open_edges.iter(model_adapter.get_trailing_actions());
			while let Some(&edge) = open.next() {
				trace!("{:?}", graph.edges[edge]);
			}
		}*/

		self.initial_graph = Some(DifferenceLogicInitial { initial_trail, graph, state, int_vars, bool_vars });
		// TODO if all vars are fixed return subsumed
		// TODO requeue for more simplification?

		Ok(SimplificationStatus::Fixpoint)

	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		trace!("Transforming DifferenceLogicGraph to solver");
		let mut initial_graph = mem::replace(&mut self.initial_graph, None).unwrap();
		initial_graph.initial_trail.init_trail(slv);
		initial_graph.graph.init_trail(&mut initial_graph.initial_trail);
		// TODO some variables are not relevant any more (fixed), do not set advisors for them (also for bools)
		let int_vars = initial_graph.int_vars.iter().map(|&v| slv.get_solver_int(v)).collect_vec();  // TODO variables might be unified here but not known before, need to check!
		/*trace!("Transformed int vars:");
		for &v in int_vars.iter() {
			trace!("{v:?}: lb {:?}, ub: {:?}", slv.get_int_lower_bound(v), slv.get_int_upper_bound(v));
		}*/
		let bool_vars = initial_graph.bool_vars.iter().map(|&v| slv.get_solver_bool(v)).collect_vec();
		DifferenceLogicBounds::new_in(slv, self.priority_level, int_vars, bool_vars,
									  initial_graph.graph,
									  initial_graph.state);
		Ok(())
	}
}

#[derive(Debug, PartialEq, Eq)]
/// A model adapter using [SimplificationActions], [IntDecision], and [BoolDecision] for use during simplification.
struct SimplificationModelAdapter<'a, S> {
	actions: &'a mut S,
	initial_trail: &'a mut InitialTrail,
	int_vars: &'a Vec<IntDecision>,
	bool_vars: &'a Vec<BoolDecision>,
}

impl<'a, S: SimplificationActions> SimplificationModelAdapter<'a, S> {

	fn new(actions: &'a mut S, initial_trail: &'a mut InitialTrail, int_vars: &'a Vec<IntDecision>, bool_vars: &'a Vec<BoolDecision>) -> Self {
		Self {
			actions,
			initial_trail,
			int_vars,
			bool_vars,
		}
	}

}

impl<S: SimplificationActions> ModelAdapter<ReformulationError> for SimplificationModelAdapter<'_, S> {

	fn get_int_lower_bound(&self, v: usize) -> IntVal {
		self.actions.get_int_lower_bound(self.int_vars[v])
	}

	fn set_int_lower_bound(&mut self, v: usize, value: IntVal, _bool_var: Option<usize>, _lb_var: usize, _lb_val: IntVal) -> Result<(), ReformulationError> {
		self.actions.set_int_lower_bound(self.int_vars[v], value)?;
		Ok(())
	}

	fn get_int_upper_bound(&self, v: usize) -> IntVal {
		self.actions.get_int_upper_bound(self.int_vars[v])
	}

	fn set_int_upper_bound(&mut self, v: usize, value: IntVal, _bool_var: Option<usize>, _ub_var: usize, _ub_val: IntVal) -> Result<(), ReformulationError> {
		self.actions.set_int_upper_bound(self.int_vars[v], value)?;
		Ok(())
	}

	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions {
		self.initial_trail
	}

	fn get_bool_val(&self, v: usize) -> Option<bool> {
		self.actions.get_bool_val(self.bool_vars[v])
	}

	fn process_negative_cycle(&mut self, var: Option<usize>, _reason: Vec<usize>) -> Result<(), ReformulationError> {
		let var = var.map_or(BoolDecision::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var)?;
		Ok(())
	}

	fn set_bool_false(&mut self, bool_var: Option<usize>, _lb_var: usize, _lb_val: IntVal, _ub_var: usize, _ub_val: IntVal) -> Result<(), ReformulationError> {
		let var = bool_var.map_or(BoolDecision::from(true), |i| self.bool_vars[i]);
		self.actions.set_bool(!var)?;
		Ok(())
	}

	fn trail_remove_node(&mut self, v: &mut VarNode) {
		v.edges.remove_trail(self.initial_trail);
		v.reverse_edges.remove_trail(self.initial_trail);
		v.open_edges.remove_trail(self.initial_trail);
		v.open_reverse_edges.remove_trail(self.initial_trail);
	}

	fn trail_remove_open_list<T>(&mut self, l: &mut TrailedOpenList<T>) {
		l.remove_trail(self.initial_trail);
	}


	fn add_implied_bound(&mut self, bool_var: usize, int_var: usize, lt: bool, value: IntVal) {
		let bound = if lt {
			Box::new(BoolFormula::Atom(self.int_vars[int_var].leq(value)))
		} else {
			Box::new(BoolFormula::Atom(self.int_vars[int_var].geq(value)))
		};
		self.actions.add_constraint(BoolFormula::Implies(
			Box::new(BoolFormula::Atom(self.bool_vars[bool_var])),
			bound,
		))
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

#[derive(Debug, Clone, PartialEq, Eq)]
/// A graph of difference constraints.
pub struct DifferenceLogicGraph {
	/// List of all nodes in the graph.
	nodes: Vec<Option<Rc<RefCell<VarNode>>>>,
	/// Number of nodes that are active.
	open_nodes: usize,
	/// List of all edges in the graph. todo could make this a trailed list for dynamic addition
	edges: Vec<DiffEdge>,
	/// Map from boolean indices to their implied edges (in RefCell to decouple from self).
	bool_implications: Vec<Option<Rc<RefCell<TrailedOpenList<usize>>>>>,
	/// Storage for the visited state.
	visited: Vec<usize>, // TODO move to state?
	/// Number of open implication edges.
	open_imp_edges: TrailedInt,
}

impl DifferenceLogicGraph {

	fn new(initial_trail: &mut InitialTrail, int_vars: usize, bool_vars: usize) -> Self {
		Self {
			nodes: (0..int_vars).into_iter().map(|_| Some(Rc::new(RefCell::new(VarNode::new(initial_trail))))).collect(),
			open_nodes: int_vars,
			edges: Vec::new(),
			bool_implications: (0..bool_vars).into_iter().map(|_| Some(Rc::new(RefCell::new(TrailedOpenList::new(initial_trail))))).collect(),
			visited: Vec::new(),
			open_imp_edges: initial_trail.new_trailed_int(0),
		}
	}

	/// Borrow an immutable reference to the node identified by index.
	fn borrow_node(&self, v: usize) -> Ref<VarNode> {
		self.nodes[v].as_ref().unwrap().borrow()
	}

	/// Borrow a mutable reference to the node identified by index.
	fn borrow_node_mut(&self, v: usize) -> RefMut<VarNode> {
		self.nodes[v].as_ref().unwrap().borrow_mut()
	}

	/// Return a clone of the reference to the node identified by index.
	fn get_node_clone(&self, v: usize) -> Rc<RefCell<VarNode>> {
		self.nodes[v].as_ref().unwrap().clone()
	}
	
	/// Iterate existing nodes.
	fn iter_nodes(&self) -> impl Iterator<Item = (usize, &Rc<RefCell<VarNode>>)> {
		self.nodes.iter().enumerate().filter_map(|(i, opt)| {
			match (i, opt) {
				(i, Some(opt)) => Some((i, opt)),
				(_, None) => None,
			}
		})
	}

	/// Borrow a mutable reference to the list of implications identified by the boolean variable
	/// index.
	fn borrow_implications_mut(&self, b: usize) -> RefMut<TrailedOpenList<usize>> {
		self.bool_implications[b].as_ref().unwrap().borrow_mut()
	}

	/// Return a clone of the reference to the list of implications identified by the boolean 
	/// variable index.
	fn get_implications_clone(&self, b: usize) -> Rc<RefCell<TrailedOpenList<usize>>> {
		self.bool_implications[b].as_ref().unwrap().clone()
	}

	/// Initialize the trailed infrastructure for this graph.
	fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		for node in self.nodes.iter() {
			if let Some(node) = node {
				node.borrow_mut().init_trail(initial_trail);
			}
		}
		for implications in self.bool_implications.iter() {
			if let Some(implications) = implications {
				implications.borrow_mut().init_trail(initial_trail);
			}
		}
		self.open_imp_edges = initial_trail.map_to_trail(self.open_imp_edges);
	}

	/// Add a new edge to the graph, return the index. Depending on the boolean, the edge is added 
	/// globally (boolean is None) or as an implied edge.
	fn new_edge<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, mut edge: DiffEdge) -> usize {
		let index = self.edges.len();
		if let Some(b) = edge.bool_var {
			let mut implications = self.borrow_implications_mut(b);
			edge.bool_index = implications.len();
			implications.push(index);
			let mut from = self.borrow_node_mut(edge.from);
			edge.out_index = from.open_edges.len();
			from.open_edges.push(self.edges.len());
			let mut to = self.borrow_node_mut(edge.to);
			edge.in_index = to.open_reverse_edges.len();
			to.open_reverse_edges.push(self.edges.len());
			let actions = adapter.get_trailing_actions();
			let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) + 1);
		} else {
			self.borrow_node_mut(edge.from).edges.push(adapter.get_trailing_actions(), index);
			self.borrow_node_mut(edge.to).reverse_edges.push(adapter.get_trailing_actions(), index);
		}
		self.edges.push(edge);
		index
	}

	/// Activate the implied edge given by the index.
	fn activate_imp_edge<E, A: ModelAdapter<E>>(&self, adapter: &mut A, index: usize) {
		let edge = &self.edges[index];
		self.borrow_node_mut(edge.from).edges.push(adapter.get_trailing_actions(), index);
		self.borrow_node_mut(edge.to).reverse_edges.push(adapter.get_trailing_actions(), index);
	}

	/// Close the implied edge given by the index while iterating implied edges via the boolean.
	fn close_imp_edge_boolean<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = open.close(actions, |&e, i| self.edges[e].bool_index = i);
		let &to = &self.edges[index].to;
		let &from = &self.edges[index].from;
		let out_index = self.edges[index].out_index;
		let in_index = self.edges[index].in_index;
		let was_open = self.get_node_clone(from).borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i) &&
			self.get_node_clone(to).borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert!(was_open);
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
	}

	/// Close the implied edge given by the index while iterating open edges in forward direction.
	fn close_imp_edge_forward<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = open.close(actions, |&e, i| self.edges[e].out_index = i);
		let &b = &self.edges[index].bool_var.unwrap();
		let &to = &self.edges[index].to;
		let bool_index = self.edges[index].bool_index;
		let in_index = self.edges[index].in_index;
		let was_open = self.get_implications_clone(b).borrow_mut().close(actions, bool_index, |&e, i| self.edges[e].bool_index = i) &&
			self.get_node_clone(to).borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert!(was_open);
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
	}

	/// Close the implied edge given by the index while iterating open edges in backward direction.
	fn close_imp_edge_backward<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, rev_open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = rev_open.close(actions, |&e, i| self.edges[e].in_index = i);
		let &b = &self.edges[index].bool_var.unwrap();
		let &from = &self.edges[index].from;
		let bool_index = self.edges[index].bool_index;
		let out_index = self.edges[index].out_index;
		let was_open = self.get_implications_clone(b).borrow_mut().close(actions, bool_index, |&e, i| self.edges[e].bool_index = i) && 
			self.get_node_clone(from).borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i);
		debug_assert!(was_open);
		let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
	}

	/// Mark the given node as visited.
	fn visit(&mut self, node: usize) {
		self.borrow_node_mut(node).visited = true;
		self.visited.push(node);
	}

	/// Reset the visited state of all nodes.
	fn reset_visit(&mut self) {
		for &node in self.visited.iter() {
			if let Some(node) = &self.nodes[node] {
				node.borrow_mut().visited = false;
			}
		}
		self.visited.clear();
	}

	/// Get the current lower bound for the node, either stored or from the search.
	fn get_cur_lower_bound<E, A: ModelAdapter<E>>(&self, adapter: &A, v: usize) -> IntVal {
		match self.borrow_node(v).lower_bound {
			Some(lb) => lb,
			None => adapter.get_int_lower_bound(v),
		}
	}

	/// Update the stored lower bound for the node.
	fn update_lb(&self, node: usize, val: IntVal, lb_updates: &mut Vec<usize>) {
		self.borrow_node_mut(node).lower_bound = Some(val);
		lb_updates.push(node);
	}

	/// Reset stored lower bounds of all nodes.
	fn reset_lb_updates(&self, lb_updates: &mut Vec<usize>) {
		for &node in lb_updates.iter() {
			if let Some(node) = &self.nodes[node] {
				node.borrow_mut().lower_bound = None;
			}
		}
		lb_updates.clear();
	}

	/// Get the current upper bound for the node, either stored or from the search.
	fn get_cur_upper_bound<E, A: ModelAdapter<E>>(&self, adapter: &A, v: usize) -> IntVal {
		match self.borrow_node(v).upper_bound {
			Some(ub) => ub,
			None => adapter.get_int_upper_bound(v),
		}
	}

	/// Update the stored upper bound for the node.
	fn update_ub(&self, node: usize, val: IntVal, ub_updates: &mut Vec<usize>) {
		self.borrow_node_mut(node).upper_bound = Some(val);
		ub_updates.push(node);
	}

	/// Reset stored upper bounds of all nodes.
	fn reset_ub_updates(&mut self, ub_updates: &mut Vec<usize>) {
		for &node in ub_updates.iter() {
			if let Some(node) = &self.nodes[node] {
				node.borrow_mut().upper_bound = None;
			}
		}
		ub_updates.clear();
	}

	/// Compute initial pi values by assuming an additional vertex with a 0-cost path to every other
	/// vertex and applying Bellman-Ford. Fail if a negative cycle is detected.
	fn bellman_ford_init_pi<A: ModelAdapter<ReformulationError>>(&mut self, adapter: &mut A) -> Result<(), ReformulationError> {
		trace!("Calculating initial pi values.");
		let mut distance = vec![0; self.nodes.len() + 1];
		//let mut predecessor = vec![self.nodes.len(); self.nodes.len() + 1];
		let mut changed = false;
		for _ in 0..self.open_nodes {  // TODO fail faster in case of negative cycle?
			for (_, node) in self.iter_nodes() {
				for &edge in node.borrow().edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[edge];
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
			for (_, node) in self.iter_nodes() {
				for &edge in node.borrow().edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[edge];
					if distance[edge.from] + edge.val < distance[edge.to] {
						trace!("Found negative cycle!");
						return Err(ReformulationError::TrivialUnsatisfiable);  // TODO output cycle?
					}
				}
			}
		}
		for (n, node) in self.iter_nodes() {
			node.borrow_mut().pi = distance[n];
		}
		Ok(())
	}

	/// Use Johnson's algorithm to get all pairs of shortest paths. Remove edges not used in any 
	/// shortest path, close implied edges if possible.
	fn johnson_full<A: ModelAdapter<ReformulationError>>(&mut self, adapter: &mut A) -> Result<(), ReformulationError> {

		trace!("Starting full dijkstra");
		let mut distances = vec![vec![IntVal::MAX; self.nodes.len()]; self.nodes.len()];
		let mut queue = PriorityQueue::default();
		
		for i in 0..self.nodes.len() {
			if self.nodes[i].is_none() {  //TODO?
				continue;
			}
			self.reset_visit();
			let pi_i = self.borrow_node(i).pi;
			let _ = queue.push(i, Reverse(0));
			while !queue.is_empty() {
				let (s, Reverse(dist)) = queue.pop().unwrap();
				self.visit(s);
				let node_s = self.borrow_node(s);
				//trace!("dijkstra on current node {s:?} with dist {dist}");
				for &index in node_s.edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[index];
					let node_t = self.borrow_node(edge.to);
					let new_dist = dist + edge.val + node_s.pi - node_t.pi;
					if !node_t.visited {
						let prev = queue.push_increase(edge.to, Reverse(new_dist));
						if prev.map_or(true, |Reverse(old_dist)| new_dist < old_dist) {
							distances[i][edge.to] = new_dist - pi_i + node_t.pi;
						}
						//trace!("dijkstra adding node {:?} with dist {new_dist}", target.var);
					}
				}
			}
		}
		
		trace!("Distances:");
		for (i, row) in distances.iter().enumerate() {
			trace!("{i}: {:?}", row.iter().enumerate().filter(|(_, &val)| val < IntVal::MAX).collect_vec());
		}
		trace!("Checking impact on edges");  // TODO can / should we eliminate different paths with the same length? There might even be duplicate edges between the same nodes!
		for i in 0..self.nodes.len() {  // TODO cycles of length 0!
			if self.nodes[i].is_none() {  // TODO?
				continue;
			}
			let temp_node = self.get_node_clone(i);
			let mut node_ref = temp_node.borrow_mut();
			
			let mut j = 0;
			while j < node_ref.edges.len(adapter.get_trailing_actions()) {
				let edge = &self.edges[*node_ref.edges.index(adapter.get_trailing_actions(), j)];
				if distances[edge.from][edge.to] < edge.val {
					trace!("Global edge {edge:?} is redundant, shortest path of length {} found", distances[edge.from][edge.to]);
					let _ = node_ref.edges.swap_remove(adapter.get_trailing_actions(), j);
				} else {
					j += 1;
				}
			}

			let mut j = 0;
			while j < node_ref.reverse_edges.len(adapter.get_trailing_actions()) {
				let edge = &self.edges[*node_ref.reverse_edges.index(adapter.get_trailing_actions(), j)];
				if distances[edge.from][edge.to] < edge.val {
					let _ = node_ref.reverse_edges.swap_remove(adapter.get_trailing_actions(), j);
				} else { 
					j += 1;
				}
			}
			
			let mut open = node_ref.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if distances[edge.from][edge.to] < edge.val {
					trace!("Implied edge {edge:?} is redundant, shortest path of length {} found", distances[edge.from][edge.to]);
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node_ref.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if distances[edge.to][edge.from] < -edge.val {
					trace!("Implied edge {edge:?} is falsified, opposite shortest path of length {} found", distances[edge.to][edge.from]);
					adapter.set_bool_false(edge.bool_var, edge.from, 0, edge.to, 0)?;  // TODO invalid reason, but also not needed at this point -> different method?
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}
		}
		
		Ok(())

	}

	/// Check if nodes with fixed domain exist, if yes remove them from the graph.
	fn check_remove_fixed_nodes<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A) {

		for n in 0..self.nodes.len() {
			if self.nodes[n].is_none() {  // TODO?
				continue;
			}
			if adapter.get_int_lower_bound(n) == adapter.get_int_upper_bound(n) {
				trace!("Var {n} has a fixed value - removing from graph");
				let val = adapter.get_int_lower_bound(n);
				let temp_node = self.get_node_clone(n);
				let mut node_ref = temp_node.borrow_mut();
				for &edge in node_ref.edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[edge];
					trace!("Removing outgoing edge {edge:?}");
					let mut to = self.borrow_node_mut(edge.to);
					let _ = to.reverse_edges.swap_remove(adapter.get_trailing_actions(), edge.in_index);
				}
				for &edge in node_ref.reverse_edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[edge];
					trace!("Removing incoming edge {edge:?}");
					let mut from = self.borrow_node_mut(edge.from);
					let _ = from.edges.swap_remove(adapter.get_trailing_actions(), edge.out_index);
				}
				let mut open = node_ref.open_edges.iter(adapter.get_trailing_actions());
				while let Some(&e) = open.next() {
					let edge = &self.edges[e];
					trace!("Reemitting implied outgoing edge {edge:?}");
					adapter.add_implied_bound(edge.bool_var.unwrap(), edge.to, false, val - edge.val);
					self.close_imp_edge_forward(adapter, &mut open, e);
				}
				let mut rev_open = node_ref.open_reverse_edges.iter(adapter.get_trailing_actions());
				while let Some(&e) = rev_open.next() {
					let edge = &self.edges[e];
					trace!("Reemitting implied incoming edge {edge:?}");
					adapter.add_implied_bound(edge.bool_var.unwrap(), edge.from, true, val + edge.val);
					self.close_imp_edge_backward(adapter, &mut rev_open, e);
				}
				adapter.trail_remove_node(node_ref.deref_mut());
				self.nodes[n] = None;
				self.open_nodes -= 1;
			}
		}

	}

	/// Check if nodes with no edges exist, if yes remove them from the graph.
	fn check_remove_isolated_nodes<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A) {

		for n in 0..self.nodes.len() {
			if self.nodes[n].is_none() {  // TODO?
				continue;
			}
			let temp_node = self.get_node_clone(n);
			let mut node_ref = temp_node.borrow_mut();
			if node_ref.edges.len(adapter.get_trailing_actions()) == 0 &&
				node_ref.reverse_edges.len(adapter.get_trailing_actions()) == 0 &&
				node_ref.open_edges.open_len(adapter.get_trailing_actions()) == 0 &&
				node_ref.open_reverse_edges.open_len(adapter.get_trailing_actions()) == 0 {
				trace!("Var {n} has no edges - removing from graph");
				adapter.trail_remove_node(node_ref.deref_mut());
				self.nodes[n] = None;
				self.open_nodes -= 1;
			}
		}

	}

	fn check_remove_isolated_booleans<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A) {
		for b in 0..self.bool_implications.len() {
			let temp_implications = self.get_implications_clone(b);
			let mut imp_ref = temp_implications.borrow_mut();
			if imp_ref.open_len(adapter.get_trailing_actions()) == 0 {
				trace!("Boolean {b} has no edges - removing from graph");
				adapter.trail_remove_open_list(imp_ref.deref_mut());
				self.bool_implications[b] = None;
			}
		}
	}

	/// Get the reason for a cycle of negative lengths (all booleans along the cycle).
	fn get_cycle_reason(&self, node: usize) -> Vec<usize> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = self.borrow_node(var).backtrace {
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
		self.borrow_node_mut(new_edge.to).backtrace = None;
		let gamma_v = self.borrow_node(new_edge.from).pi + new_edge.val - self.borrow_node(new_edge.to).pi;
		if gamma_v < 0 {
			let _ = queue.push(new_edge.to, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&new_edge.from).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let node_s = self.borrow_node(s);
			let _ = pi_new.insert(s, node_s.pi + gamma_s);
			for &index in node_s.edges.iter(adapter.get_trailing_actions()) {
				let edge = &self.edges[index];
				let mut node_t = self.borrow_node_mut(edge.to);
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
			self.borrow_node_mut(var).pi = val;
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
		let pi_origin = self.borrow_node(origin).pi;
		let relevant_target = if reverse {new_edge.from} else {new_edge.to};
		let mut distances = IndexMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = PriorityQueue::default();
		let _ = queue.push(origin, Reverse(0));
		let pi_relevant = self.borrow_node(relevant_target).pi;
		let _ = queue.push(relevant_target, Reverse(new_edge.val + if reverse { pi_relevant - pi_origin } else { pi_origin - pi_relevant }));
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse(dist)) = queue.pop().unwrap();
			self.visit(s);
			let node_s = self.borrow_node(s);
			let s_relevant = distances.contains_key(&s);
			//trace!("dijkstra on current node {s:?} with dist {dist}");
			for &index in if reverse {node_s.reverse_edges.iter(adapter.get_trailing_actions())} else {node_s.edges.iter(adapter.get_trailing_actions())} {
				let edge = &self.edges[index];
				let target = if reverse {edge.from} else {edge.to};
				let node_t = self.borrow_node(target);
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
	fn inc_imp<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, new_index: usize) -> Result<(), E> {
		
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
		let indegree_u: usize = incoming_u.iter().map(|(&v, _)| self.borrow_node(v).open_reverse_edges.open_len(adapter.get_trailing_actions())).sum();
		let outdegree_v: usize = outgoing_v.iter().map(|(&v, _)| self.borrow_node(v).open_edges.open_len(adapter.get_trailing_actions())).sum();
		trace!("indegree: {indegree_u:?}, outdegree: {outdegree_v:?}");
		
		let new_edge_val = self.edges[new_index].val;
		let mut fail_indices = Vec::new();
		
		if indegree_u < outdegree_v {
			for &var in incoming_u.keys() {
				let temp_node = self.get_node_clone(var);
				let mut node = temp_node.borrow_mut();
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
				let temp_node = self.get_node_clone(var);
				let mut node = temp_node.borrow_mut();
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
	fn inc_lb<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, v_l: &IndexSet<usize>, lb_updates: &mut Vec<usize>) -> Result<(), E> {  // TODO unit tests

		trace!("Running inc_lb on int vars {v_l:?}");
		self.reset_visit();
		let pi0 = v_l.iter().map(|&n| {
			adapter.get_int_lower_bound(n) + self.borrow_node(n).pi
		}).max().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_l.iter() {
			// Min value indicates that successors still need to be considered.
			self.update_lb(n, IntVal::MIN, lb_updates);
			let _ = queue.push(n, Reverse(pi0 - adapter.get_int_lower_bound(n) - self.borrow_node(n).pi));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 - gamma_s - self.borrow_node(s).pi;
			if bound > self.get_cur_lower_bound(adapter, s) {
				self.update_lb(s, bound, lb_updates);
				let node_s = self.borrow_node(s);
				if bound > adapter.get_int_lower_bound(s) {
					trace!("Updating lower bound for i{:?} to {bound}", s);
					let (prev, b) = node_s.backtrace.unwrap();
					adapter.set_int_lower_bound(s, bound, b, prev, self.get_cur_lower_bound(adapter, prev))?;
				}
				for &index in node_s.edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[index];
					let mut node_t = self.borrow_node_mut(edge.to);
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
	fn inc_ub<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, v_u: &IndexSet<usize>, ub_updates: &mut Vec<usize>) -> Result<(), E> {  // TODO unit tests

		trace!("Running inc_ub on int vars {v_u:?}");
		self.reset_visit();
		let pi0 = v_u.iter().map(|&n| {
			adapter.get_int_upper_bound(n) + self.borrow_node(n).pi
		}).min().unwrap();
		let mut queue = PriorityQueue::default();
		for &n in v_u.iter() {
			// Max value indicates that predecessors still need to be considered.
			self.update_ub(n, IntVal::MAX, ub_updates);
			let _ = queue.push(n, Reverse(self.borrow_node(n).pi + adapter.get_int_upper_bound(n) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 + gamma_s - self.borrow_node(s).pi;
			if bound < self.get_cur_upper_bound(adapter, s) {
				self.update_ub(s, bound, ub_updates);
				let node_s = self.borrow_node(s);
				if bound < adapter.get_int_upper_bound(s) {
					trace!("Updating upper bound for i{:?} to {bound}", s);
					let (prev, b) = node_s.backtrace.unwrap();
					adapter.set_int_upper_bound(s, bound, b, prev, self.get_cur_upper_bound(adapter, prev))?;

				}
				for &index in node_s.reverse_edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[index];
					let mut node_t = self.borrow_node_mut(edge.from);
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


	/// Propagate new bounds.
	fn propagate_bounds<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, state: &mut DifferenceLogicState) -> Result<(), E> {
		
		trace!("Propagating bounds on lb changes {:?}, ub changes {:?}.", state.lower_bound_changes, state.upper_bound_changes);
		self.reset_lb_updates(&mut state.lb_updates);
		self.reset_ub_updates(&mut state.ub_updates);

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
			let node_ref = self.get_node_clone(n);
			let mut node = node_ref.borrow_mut();
			let lb = node.lower_bound.unwrap();

			let mut open = node.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				let target_ub = self.get_cur_upper_bound(adapter, edge.to);
				if lb - target_ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is falsified by bounds.", edge.bool_var, n, edge.to, edge.val);
					adapter.set_bool_false(edge.bool_var, n, lb, edge.to, target_ub)?;  // TODO directly reenqueue these?
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if self.get_cur_upper_bound(adapter, edge.from) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is implied by bounds.", edge.bool_var, edge.from, n, edge.val);
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}
		}

		// Consequences of upper bound updates on open implied constraints
		for &n in state.ub_updates.iter() {
			let node_ref = self.get_node_clone(n);
			let mut node = node_ref.borrow_mut();
			let ub = node.upper_bound.unwrap();

			let mut open = node.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if ub - self.get_cur_lower_bound(adapter, edge.to) <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is implied by bounds.", edge.bool_var, n, edge.to, edge.val);
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				let source_lb = self.get_cur_lower_bound(adapter, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint b{:?} -> i{:?} - i{:?} <= {:?} is falsified by bounds.", edge.bool_var, edge.from, n, edge.val);
					adapter.set_bool_false(edge.bool_var, edge.from, source_lb, n, ub)?;
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}
		}

		state.reset_bound_changes();
		Ok(())
		
	}

	/// Propagate fixed booleans.
	fn propagate_booleans<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, state: &mut DifferenceLogicState, check_implied: bool) -> Result<(), E> {
		
		trace!("Propagating fixed booleans {:?}.", state.fixed_bools);
		// Handle fixed booleans
		for &b in state.fixed_bools.iter() {
			let val = adapter.get_bool_val(b).unwrap();
			trace!("Boolean b{b:?} fixed to {val}");
			if val {
				// Consequences of setting the boolean to true -> add all implied edges.
				let list_ref = self.get_implications_clone(b);
				let mut mut_list = list_ref.borrow_mut();
				let mut open = mut_list.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					trace!("Processing adding edge {:?}", self.edges[index]);
					self.close_imp_edge_boolean(adapter, &mut open, index);
					// If the edge can't be added, a conflict will be generated
					if self.inc_sat(adapter, index)? {
						self.activate_imp_edge(adapter, index);
						if check_implied {
							// If the edge was added, check the status of open edges.
							self.inc_imp(adapter, index)?;
						}
						let edge = &self.edges[index];
						let lb_y = -edge.val + self.get_cur_lower_bound(adapter, edge.from);
						if lb_y > self.get_cur_lower_bound(adapter, edge.to) {
							// New edge caused lower bound change.
							adapter.set_int_lower_bound(edge.to, lb_y, Some(b), edge.from, self.get_cur_lower_bound(adapter, edge.from))?;
							self.update_lb(edge.to, lb_y, &mut state.lb_updates);
						}
						let ub_x = edge.val + self.get_cur_upper_bound(adapter, edge.to);
						if ub_x < self.get_cur_upper_bound(adapter, edge.from) {
							// New edge caused upper bound change.
							adapter.set_int_upper_bound(edge.from, ub_x, Some(b), edge.to, self.get_cur_upper_bound(adapter, edge.to))?;
							self.update_ub(edge.from, ub_x, &mut state.ub_updates);
						}
					}
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				let list_ref = self.get_implications_clone(b);
				let mut mut_list = list_ref.borrow_mut();
				let mut open = mut_list.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					trace!("Closing edge {:?})", self.edges[index]);
					self.close_imp_edge_boolean(adapter, &mut open, index);
				}
			}
		}

		state.reset_bool_changes();
		Ok(())

	}
	
	/// Generate a dot presentation of the active graph.
	fn to_dot<E, A: ModelAdapter<E>>(&self, adapter: &mut A) -> String {
		let mut out = "digraph {\n".to_owned();
		for (n, v) in self.iter_nodes() {
			let node = v.borrow();
			out.push_str(format!("\"{:?}\" [label=\"{:?} (lb: {:?}, ub: {:?}, pi: {:?})\"]\n",
								 n,
								 n,
								 self.get_cur_lower_bound(adapter, n),
								 self.get_cur_upper_bound(adapter, n),
								 node.pi).as_str());
			for &index in node.edges.iter(adapter.get_trailing_actions()) {
				let edge = &self.edges[index];
				out.push_str(format!("\"{:?}\" -> \"{:?}\" [label=\"{:?} ({:?})\"]\n", n, edge.to, edge.val, edge.bool_var).as_str());
			}
		}
		out += "}";
		out
	}

}

/// Provides access to the current state of the model independent of representation.
trait ModelAdapter<E> {
	
	/// Return the lower bound for the variable identified by index.
	fn get_int_lower_bound(&self, v: usize) -> IntVal;

	/// Set the lower bound for the variable identified by index as a consequence of the boolean and 
	/// the given lower bound.
	fn set_int_lower_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal) -> Result<(), E>;

	/// Return the upper bound for the variable identified by index.
	fn get_int_upper_bound(&self, v: usize) -> IntVal;

	/// Set the upper bound for the variable identified by index as a consequence of the boolean and 
	/// the given upper bound.
	fn set_int_upper_bound(&mut self, v: usize, value: IntVal, bool_var: Option<usize>, ub_var: usize, ub_val: IntVal) -> Result<(), E>;
	
	/// Return the infrastructure to deal with trailed integers.
	fn get_trailing_actions(&mut self) -> &mut dyn TrailingActions;
	
	/// Get the value of the boolean variable identified by index if it is set.
	fn get_bool_val(&self, v: usize) -> Option<bool>;

	/// Enforce the negation of the boolean variable identified by index with the reason given as an
	/// array of boolean variables. Fail if var is None.
	fn process_negative_cycle(&mut self, var: Option<usize>, reason: Vec<usize>) -> Result<(), E>;

	/// Enforce the negation of the boolean variable identified by index with a reason given by a 
	/// lower and upper bound.
	fn set_bool_false(&mut self, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal, ub_var: usize, ub_val: IntVal) -> Result<(), E>;

	/// Remove the trailing infrastructure for the given node. Note that the default is to fail.
	fn trail_remove_node(&mut self, _v: &mut VarNode) {
		panic!("Trail removal operations are not supported by this adapter!");
	}

	/// Remove the trailing infrastructure for the given node. Note that the default is to fail.
	fn trail_remove_open_list<T>(&mut self, _l: &mut TrailedOpenList<T>) {
		panic!("Trail removal operations are not supported by this adapter!");
	}

	/// Add an implied bound constraint to the model. Note that the default is to fail.
	fn add_implied_bound(&mut self, _bool_var: usize, _int_var: usize, _lt: bool, _value: IntVal) {
		panic!("Adding constraints is not supported by this adapter!");
	}
	
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

	fn set_bool_false(&mut self, bool_var: Option<usize>, lb_var: usize, lb_val: IntVal, ub_var: usize, ub_val: IntVal) -> Result<(), Conflict> {
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
	/// List of integer variable indices with reported lower bound changes.
	lower_bound_changes: IndexSet<usize>,
	/// List of integer variable indices with reported upper bound changes.
	upper_bound_changes: IndexSet<usize>,
	/// List of boolean variable indices that have recently been reported as fixed to true.
	fixed_bools: IndexSet<usize>,
}

impl DifferenceLogicState {
	
	fn new(int_vars: usize) -> Self {
		Self {
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			lower_bound_changes: (0..int_vars).into_iter().collect(),
			upper_bound_changes: (0..int_vars).into_iter().collect(),
			fixed_bools: IndexSet::default(),
		}
	}

	fn reset_bound_changes(&mut self) {
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
	}

	fn reset_bool_changes(&mut self) {
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
	/// Propagator state data.
	state: DifferenceLogicState,
}

impl DifferenceLogicBounds {

	/// Create a new [`DifferenceLogicBounds`] propagator and post it in the solver.
	pub fn new_in<I: PropagatorInitActions + ?Sized>(solver: &mut I,
													 priority_level: PriorityLevel,
													 int_vars: Vec<IntView>,
													 bool_vars: Vec<BoolView>,
													 graph: DifferenceLogicGraph,
													 state: DifferenceLogicState) {

		let node_active = (0..graph.nodes.len()).into_iter().filter(|&i| graph.nodes[i].is_some()).collect_vec();
		let bool_active = (0..graph.bool_implications.len()).into_iter().filter(|&i| graph.bool_implications[i].is_some()).collect_vec();
		trace!("Creating propagator for {} int and {} bool vars", node_active.len(), bool_active.len());
		
		let prop = solver.add_propagator(
			Box::new(Self {
				int_vars: int_vars.clone(),
				bool_vars: bool_vars.clone(),
				graph,
				state,
			}),
			priority_level,
		);

		for i in node_active.into_iter() {
			solver.advise_on_int_change(prop, int_vars[i], IntPropCond::LowerBound, i as u64);
			solver.advise_on_int_change(prop, int_vars[i], IntPropCond::UpperBound, i as u64);
		}
		for i in bool_active.into_iter() {
			solver.advise_on_bool_change(prop, bool_vars[i], i as u64);
		}
		solver.advise_on_backtrack(prop);

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
		self.state.reset_bound_changes();
		self.state.reset_bool_changes();
		false
	}

	#[tracing::instrument(name = "difference_logic", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut model_adapter = SolverModelAdapter::new(actions, &self.int_vars, &self.bool_vars);
		if let Err(e) = self.graph.propagate_bounds(&mut model_adapter, &mut self.state) {
			self.state.reset_bound_changes();
			return Err(e);
		}
		if let Err(e) = self.graph.propagate_booleans(&mut model_adapter, &mut self.state, true) { // TODO might want to experiment with no implied checks!
			self.state.reset_bool_changes();
			return Err(e);
		}
		Ok(())
	}

}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use pindakaas::solver::propagation::PropagatingSolver;
	use pindakaas::Lit as RawLit;
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::{DiffEdge, DifferenceLogic, DifferenceLogicConstraint, DifferenceLogicGraph, SolverModelAdapter};
	use crate::{solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	}, Model};
	use crate::actions::TrailingActions;
	use crate::constraints::Constraint;
	use crate::helpers::initial_trail::InitialTrail;
	use crate::reformulate::{InitConfig, ReformulationContext};
	use crate::solver::IntView;
	use crate::solver::queue::PriorityLevel;
	use crate::solver::solving_context::SolvingContext;
	use crate::solver::Value::Int;

	#[test]
	#[traced_test]
	fn test_relevant_dijkstra() {  // TODO test other methods like this
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
		let new_index = graph.new_edge(&mut model_adapter, DiffEdge::new(4, 5, 1, Some(0)));

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
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut model_adapter, DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(2, 1, 2, Some(2)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap(),
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert_eq!(graph.borrow_node(2).open_edges.open_len(&ctx), 1);
		assert_eq!(graph.borrow_node(2).open_reverse_edges.open_len(&ctx), 0);
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
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(&mut model_adapter, DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_edge(&mut model_adapter, DiffEdge::new(0, 3, 2, Some(3)));
		let _ = graph.inc_imp(&mut model_adapter, new_index);
		assert_eq!(ctx.state.propagation_queue.pop_front().unwrap(),
				   RawLit::from_raw(-bool_vars[0].reverse_map_info().unwrap()));
		assert!(ctx.get_bool_val(bool_vars[1]).is_none());
		assert!(ctx.get_bool_val(bool_vars[2]).is_none());
		assert!(ctx.get_bool_val(bool_vars[3]).is_none());
		assert_eq!(graph.borrow_node(0).open_edges.open_len(&ctx), 2);
		assert_eq!(graph.borrow_node(0).open_reverse_edges.open_len(&ctx), 0);
	}

	#[test]
	#[traced_test]
	fn test_paper_simple() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=5]));
		let b = prb.new_bool_var();
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[1], int_vars[2], 4));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], -2));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
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
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], -2));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_err());
	}

}
