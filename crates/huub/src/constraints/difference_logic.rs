//! Structure and algorithms for a global difference logic propagator.

use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Reverse;
use std::fmt::Debug;
use std::hash::Hash;
use std::mem;
use std::ops::DerefMut;
use std::rc::Rc;
use itertools::Itertools;
use pindakaas::Lit as RawLit;
use pindakaas::propositional_logic::Formula;
use rustc_hash::FxBuildHasher;
use tracing::trace;
use crate::solver::activation_list::{IntEvent, IntPropCond};
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	queue::PriorityLevel, IntView,
}, BoolDecision, BoolFormula, IntDecision, IntVal, Model};
use crate::actions::{ConstraintInitActions, TrailingActions};
use crate::helpers::initial_trail::InitialTrail;
use crate::helpers::linear_transform::LinearTransform;
use crate::helpers::trailed_list::TrailedList;
use crate::helpers::trailed_open_list::{TrailedOpenList, TrailedOpenListIterator};
use crate::reformulate::{BoolDecisionInner, IntDecisionIndex, IntDecisionInner};
use crate::solver::trail::TrailedInt;

// Redefine hash-based types using the fast FxBuildHasher.
type HashSet<T> = std::collections::HashSet<T, FxBuildHasher>;
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
	/// Mapping of integer decision variables to their index.
	int_var_index: IndexSet<IntDecision>,
	/// Map of integer variables to their current state.
	int_var_state: Vec<IntDecisionMapping>,
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
	/// Minimum distances in the global graph.
	distances: Vec<Vec<IntVal>>,
	/// Set of nodes reachable with a direct edge of minimum distance for each node.
	direct_edge: Vec<HashSet<usize>>,

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
			int_var_index: IndexSet::default(),
			int_var_state: Vec::new(),
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

/// Check if the underlying variables are different, if not reemit the potentially implied difference constraint.
fn check_vars_different<S: SimplificationActions>(actions: &mut S, x: IntDecision, y: IntDecision, d: IntVal, b: Option<BoolDecision>) -> Result<bool, ReformulationError> {
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
/// A mapping that contains the decision variable, the underlying variable index, and the current bounds.
struct IntDecisionMapping {
	var: IntDecision,
	lower_bound: IntVal,
	upper_bound: IntVal,
}

impl IntDecisionMapping {
	fn new(var: IntDecision) -> Self {
		Self {
			var,
			lower_bound: IntVal::MIN,
			upper_bound: IntVal::MAX,
		}
	}
}

/// Store the current bounds for all integer decisions in the vector.
fn update_bounds<E, A: ModelAdapter<E>>(int_var_state: &mut Vec<IntDecisionMapping>, model_adapter: &mut A) {
	for (i, state) in int_var_state.iter_mut().enumerate() {
		trace!("{:?}: lb {:?}, ub: {:?}", state.var, model_adapter.get_int_lower_bound(i), model_adapter.get_int_upper_bound(i));
		state.lower_bound = model_adapter.get_int_lower_bound(i);
		state.upper_bound = model_adapter.get_int_upper_bound(i);
	}
}

impl<S: SimplificationActions> Constraint<S> for DifferenceLogic {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		
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
		
		for x in int_vars.into_iter() {
			actions.simplify_on_change_int(x);
		}
		for b in bool_vars.into_iter() {
			actions.simplify_on_change_bool(b);
		}
		
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {

		// In the initial run, the graph needs to be built
		if self.initial_graph.is_none() {
			self.int_var_index = IndexSet::default();
			let mut trimmed_constraints = Vec::new();
			let mut bool_var_index = IndexSet::default();
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
						trimmed_imp_constraints.push((bool_var_index.insert_full(b).0,
													  self.int_var_index.insert_full(x_trans).0,
													  self.int_var_index.insert_full(y_trans).0,
													  d - xd + yd));
					}
				}
			}

			trace!("Creating DifferenceLogicGraph for {} int and {} bool vars, {} global and {} implied edges.", self.int_var_index.len(), bool_var_index.len(), trimmed_constraints.len(), trimmed_imp_constraints.len());
			let mut initial_trail = InitialTrail::new();
			let mut graph = DifferenceLogicGraph::new(&mut initial_trail, self.int_var_index.len(), bool_var_index.len());
			self.int_var_state = self.int_var_index.iter().map(|&v| IntDecisionMapping::new(v)).collect_vec();
			let mut int_vars = self.int_var_index.iter().map(|&v| v).collect_vec();
			trace!("Original int vars:");
			for &v in int_vars.iter() {
				trace!("{v:?}: lb {:?}, ub: {:?}", actions.get_int_lower_bound(v), actions.get_int_upper_bound(v));
			}
			let bool_vars = bool_var_index.iter().map(|&v| v).collect_vec();
			let mut state = DifferenceLogicState::new(int_vars.len());

			// Add global constraints
			for (x, y, d) in trimmed_constraints.into_iter() {
				let _ = graph.new_edge(&mut initial_trail, DiffEdge::new(x, y, d, None));
			}

			// Add implied constraints
			for (b, x, y, d) in trimmed_imp_constraints.into_iter() {
				let _ = graph.new_edge(&mut initial_trail, DiffEdge::new(x, y, d, Some(b)));
			}

			let num_nodes = int_vars.len();
			let mut model_adapter = SimplificationModelAdapter::new(actions, &mut initial_trail, &mut int_vars, &bool_vars);
			trace!("Starting initial propagation with graph: {}", graph.to_dot(&mut model_adapter));
			/*trace!("Implied edges:");
            for node in graph.nodes.iter() {
                if let Some(node) = node {
                    let mut node_ref = node.borrow_mut();
                    let mut open = node_ref.open_edges.iter(model_adapter.get_trailing_actions());
                    while let Some(&edge) = open.next() {
                        trace!("Outgoing: {:?}", graph.edges[edge]);
                    }
                    let mut rev_open = node_ref.open_reverse_edges.iter(model_adapter.get_trailing_actions());
                    while let Some(&edge) = rev_open.next() {
                        trace!("Incoming: {:?}", graph.edges[edge]);
                    }
                }
            }*/

			graph.bellman_ford_init_pi(model_adapter.get_trailing_actions())?;
			graph.propagate_bounds(&mut model_adapter, &mut state)?;
			update_bounds(&mut self.int_var_state, &mut model_adapter);
			for i in 0..bool_vars.len() {
				if model_adapter.get_bool_val(i).is_some() && graph.bool_implications[i].is_some() {
					let _ = state.fixed_bools.insert(i);
				}
			}
			graph.propagate_booleans(&mut model_adapter, &mut state, false)?;
			// Already do removals before Johnson's to reduce complexity of the graph
			graph.check_remove_fixed_nodes(&mut model_adapter);
			graph.check_remove_isolated_nodes(&mut model_adapter);
			if graph.open_nodes == 0 {
				// If no nodes are left, there is nothing more to do
				return Ok(SimplificationStatus::Subsumed);
			}

			let mut distances = vec![vec![IntVal::MAX; num_nodes]; num_nodes];
			let mut direct_edge = vec![HashSet::default(); num_nodes];
			graph.johnson_full(&mut model_adapter, &mut distances, &mut direct_edge)?;
			self.initial_graph = Some(DifferenceLogicInitial { initial_trail, graph, state, int_vars, bool_vars, distances, direct_edge });
			
		} else {
			
			let initial_graph = self.initial_graph.as_mut().unwrap();
			
			trace!("Repeated call to simplify");
			initial_graph.state.reset_bound_changes();
			initial_graph.state.reset_bool_changes();
			let mut model_adapter = SimplificationModelAdapter::new(actions, &mut initial_graph.initial_trail, &mut initial_graph.int_vars, &initial_graph.bool_vars);
			let mut has_change = false;
			for (i, state) in self.int_var_state.iter_mut().enumerate() {
				if initial_graph.graph.nodes[i].is_some() {
					let alias = model_adapter.get_simplification_actions().resolve_alias(state.var);
					if state.var != alias {
						trace!("Var alias is different (was {:?}, is {:?})", state.var, alias);
						let (v_trans, vd) = update_transform(alias);
						if let Some(new) = self.int_var_index.get_index_of(&v_trans) {
							initial_graph.graph.unify_nodes(&mut model_adapter, &mut initial_graph.state, i, new, vd, &mut initial_graph.distances, &mut initial_graph.direct_edge)?;
						} else if !matches!(alias.0, IntDecisionInner::Const(_)) {
							state.var = v_trans;
							state.lower_bound -= vd;
							state.upper_bound -= vd;
							initial_graph.graph.update_node_offset(&mut model_adapter, i, vd)?;
							model_adapter.get_int_vars()[i] = v_trans;
						}
						has_change = true;
					}
				}
			}
			for (i, state) in self.int_var_state.iter_mut().enumerate() {
				if initial_graph.graph.nodes[i].is_none() {
					continue;
				}
				if state.lower_bound != model_adapter.get_int_lower_bound(i) {
					let _ = initial_graph.state.lower_bound_changes.insert(i);
					has_change = true;
				}
				if state.upper_bound != model_adapter.get_int_upper_bound(i) {
					let _ = initial_graph.state.upper_bound_changes.insert(i);
					has_change = true;
				}
			}
			for i in 0..initial_graph.bool_vars.len() {
				if model_adapter.get_bool_val(i).is_some() && initial_graph.graph.bool_implications[i].is_some() {
					let _ = initial_graph.state.fixed_bools.insert(i);
					has_change = true;
				}
			}
			if !has_change {
				trace!("No more changes for now, exit");
				return Ok(SimplificationStatus::Fixpoint);
			}
			initial_graph.graph.propagate_bounds(&mut model_adapter, &mut initial_graph.state)?;
			update_bounds(&mut self.int_var_state, &mut model_adapter);
			initial_graph.graph.propagate_booleans(&mut model_adapter, &mut initial_graph.state, true)?;
		}

		// Common postprocessing: Reduce graph
		let initial_graph = self.initial_graph.as_mut().unwrap();
		let mut model_adapter = SimplificationModelAdapter::new(actions, &mut initial_graph.initial_trail, &mut initial_graph.int_vars, &initial_graph.bool_vars);
		initial_graph.graph.check_remove_fixed_nodes(&mut model_adapter);
		initial_graph.graph.check_remove_isolated_nodes(&mut model_adapter);
		if initial_graph.graph.open_nodes == 0 {
			// If no nodes are left, there is nothing more to do
			trace!("No more nodes left, return subsumed");
			return Ok(SimplificationStatus::Subsumed);
		}
		initial_graph.graph.check_remove_isolated_booleans(&mut model_adapter);
		trace!("Graph at the end of simplify: {}", initial_graph.graph.to_dot(&mut model_adapter));
		// Repeat simplification until fixpoint
		self.simplify(actions)

	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		trace!("Transforming DifferenceLogicGraph to solver");
		let mut initial_graph = mem::replace(&mut self.initial_graph, None).unwrap();
		initial_graph.initial_trail.init_trail(slv);
		initial_graph.graph.init_trail(&mut initial_graph.initial_trail);
		trace!("Immediately before transformation:");
		for (i, &v) in initial_graph.int_vars.iter().enumerate() {
			if initial_graph.graph.nodes[i].is_some() {
				trace!("{v:?}");
			}
		}
		let int_vars = initial_graph.int_vars.iter().map(|&v| slv.get_solver_int(v)).collect_vec();
		trace!("Transformed int vars:");
		for (i, &v) in int_vars.iter().enumerate() {
			if initial_graph.graph.nodes[i].is_some() {
				trace!("{v:?}: lb {:?}, ub: {:?}", slv.get_int_lower_bound(v), slv.get_int_upper_bound(v));
			}
		}
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

	/// Provide direct access to the [SimplificationActions].
	fn get_simplification_actions(&mut self) -> &mut S {
		self.actions
	}

	/// Provide direct access to the [IntDecision] vector.
	fn get_int_vars(&mut self) -> &mut Vec<IntDecision> {
		self.int_vars
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

	fn check_vars_different(&mut self, v1: usize, v2: usize, d: IntVal, b: Option<usize>) -> Result<bool, ReformulationError> {
		check_vars_different(self.actions, self.int_vars[v1], self.int_vars[v2], d, b.map(|b| self.bool_vars[b]))
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

	fn unify_variables(&mut self, x: usize, y: usize, d: IntVal) -> Result<(), ReformulationError> {
		let y_trans = IntDecision(match self.int_vars[y].0 {
			IntDecisionInner::Var(i) => IntDecisionInner::Linear(LinearTransform::offset(d), i),
			IntDecisionInner::Const(c) => IntDecisionInner::Const(c + d),
			IntDecisionInner::Linear(transform, i) => IntDecisionInner::Linear(transform + d, i),
			IntDecisionInner::Bool(transform, b) => IntDecisionInner::Bool(transform + d, b),
		});
		self.actions.unify_int(self.int_vars[x], y_trans)
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
	fn new_edge<T: TrailingActions + ?Sized>(&mut self, actions: &mut T, mut edge: DiffEdge) -> usize {
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
			let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) + 1);
		} else {
			self.borrow_node_mut(edge.from).edges.push(actions, index);
			self.borrow_node_mut(edge.to).reverse_edges.push(actions, index);
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
	/// Might already be closed from a different side, in which case false is returned.
	fn close_imp_edge_boolean<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, open: &mut TrailedOpenListIterator<usize>, index: usize) -> bool {
		let actions = adapter.get_trailing_actions();
		let _ = open.close(actions, |&e, i| self.edges[e].bool_index = i);
		let &to = &self.edges[index].to;
		let &from = &self.edges[index].from;
		let out_index = self.edges[index].out_index;
		let in_index = self.edges[index].in_index;
		let was_open1 = self.get_node_clone(from).borrow_mut().open_edges.close(actions, out_index, |&e, i| self.edges[e].out_index = i);
		let was_open2 = self.get_node_clone(to).borrow_mut().open_reverse_edges.close(actions, in_index, |&e, i| self.edges[e].in_index = i);
		debug_assert_eq!(was_open1, was_open2);
		let was_open = was_open1 | was_open2;
		if !was_open  {
			let _ = actions.set_trailed_int(self.open_imp_edges, actions.get_trailed_int(self.open_imp_edges) - 1);
		}
		was_open
	}
	
	/// Try to close the edge on the boolean side, return None if not possible.
	fn try_close_imp_edge_boolean<T: TrailingActions + ?Sized>(&mut self, actions: &mut T, b: usize, bool_index: usize) -> Option<bool> {
		if let Ok(mut bool_mut) = self.get_implications_clone(b).try_borrow_mut() {
			return Some(bool_mut.close(actions, bool_index, |&e, i| self.edges[e].bool_index = i));
		}
		None
	}

	/// Close the implied edge given by the index while iterating open edges in forward direction.
	fn close_imp_edge_forward<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, open: &mut TrailedOpenListIterator<usize>, index: usize) {
		let actions = adapter.get_trailing_actions();
		let _ = open.close(actions, |&e, i| self.edges[e].out_index = i);
		let &b = &self.edges[index].bool_var.unwrap();
		let &to = &self.edges[index].to;
		let bool_index = self.edges[index].bool_index;
		let in_index = self.edges[index].in_index;
		let was_open = self.try_close_imp_edge_boolean(actions, b, bool_index).unwrap_or(true) &
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
		let was_open = self.try_close_imp_edge_boolean(actions, b, bool_index).unwrap_or(true) &
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
	fn bellman_ford_init_pi<T: TrailingActions + ?Sized>(&mut self, actions: &mut T) -> Result<(), ReformulationError> {
		trace!("Calculating initial pi values.");
		let mut distance = vec![0; self.nodes.len() + 1];
		//let mut predecessor = vec![self.nodes.len(); self.nodes.len() + 1];
		let mut changed = false;
		for _ in 0..self.open_nodes {  // TODO fail faster in case of negative cycle?
			for (_, node) in self.iter_nodes() {
				for &edge in node.borrow().edges.iter(actions) {
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
				for &edge in node.borrow().edges.iter(actions) {
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
	fn johnson_full<A: ModelAdapter<ReformulationError>>(&mut self, adapter: &mut A, distances: &mut Vec<Vec<IntVal>>, direct_edge: &mut Vec<HashSet<usize>>) -> Result<(), ReformulationError> {

		trace!("Starting Johnson's");
		let mut pred = vec![vec![usize::MAX; self.nodes.len()]; self.nodes.len()];
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
							pred[i][edge.to] = s;
						}
						//trace!("dijkstra adding node {:?} with dist {new_dist}", target.var);
					} else if edge.to == i && new_dist < distances[i][i] {
						// Loop back to origin - store distance, but don't enqueue again
						distances[i][i] = new_dist;
						pred[i][i] = s;
					}
				}
			}
		}
		
		trace!("Distances:");
		for (i, row) in distances.iter().enumerate() {
			trace!("{i}: {:?}", row.iter().enumerate().filter(|(_, &val)| val < IntVal::MAX).collect_vec());
		}
		trace!("Checking impact on edges");
		for i in 0..self.nodes.len() {
			if self.nodes[i].is_none() {  // TODO?
				continue;
			}
			let temp_node = self.get_node_clone(i);
			let mut node_ref = temp_node.borrow_mut();

			let reached = direct_edge.get_mut(i).unwrap();
			let mut j = 0;
			while j < node_ref.edges.len(adapter.get_trailing_actions()) {
				let e = *node_ref.edges.index(adapter.get_trailing_actions(), j);
				let edge = &self.edges[e];
				if distances[i][edge.to] < edge.val || (distances[i][edge.to] == edge.val && reached.contains(&edge.to)) {
					trace!("Global edge {edge:?} is redundant, shortest path of length {} found", distances[i][edge.to]);
					let _ = node_ref.edges.swap_remove(adapter.get_trailing_actions(), j);
					let _ = self.borrow_node_mut(edge.to).reverse_edges.swap_remove_element(adapter.get_trailing_actions(), &e);
				} else {
					let _ = reached.insert(edge.to);
					j += 1;
				}
			}
			
			let mut open = node_ref.open_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = open.next() {
				let edge = &self.edges[index];
				if distances[i][edge.to] <= edge.val {
					trace!("Implied edge {edge:?} is redundant, shortest path of length {} found", distances[i][edge.to]);
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node_ref.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if distances[i][edge.from] < -edge.val {
					trace!("Implied edge {edge:?} is falsified, opposite shortest path of length {} found", distances[i][edge.from]);
					adapter.set_bool_false(edge.bool_var, edge.from, 0, i, 0)?;  // TODO invalid reason, but also not needed at this point -> different method?
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}
		}

		for i in 0..self.nodes.len() {
			if self.nodes[i].is_none() {
				continue;
			}

			if distances[i][i] == 0 {// TODO count offset and always unify with start of loop to prevent long unification chains?
				trace!("Found cycle of length 0");
				let mut cur = i;
				loop {
					let prev = pred[i][cur];
					if prev == i {
						break;
					}
					trace!("Unifying {prev} and {cur} with offset {:?}", distances[prev][cur]);
					adapter.unify_variables(prev, cur, distances[prev][cur])?;
					cur = prev;
					distances[cur][cur] = IntVal::MAX;
				}
			}
		}
		
		Ok(())

	}

	/// Update the offset of a node, including the value of all edges.
	fn update_node_offset<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, v: usize, offset: IntVal) -> Result<(), E> {

		trace!("Updating the offset of node {v} by {offset}");
		let temp_node = self.get_node_clone(v);
		let mut node_ref = temp_node.borrow_mut();
		node_ref.pi += offset;
		let mut i = 0;
		while i < node_ref.edges.len(adapter.get_trailing_actions()) {
			let e = *node_ref.edges.index(adapter.get_trailing_actions(), i);
            let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(v, edge.to, edge.val, None)? {
				edge.val -= offset;
				i += 1;
			} else {
				let _ = node_ref.edges.swap_remove(adapter.get_trailing_actions(), i);
				let _ = self.borrow_node_mut(self.edges[e].to).reverse_edges.swap_remove_element(adapter.get_trailing_actions(), &e);
			}
		}
		i = 0;
		while i < node_ref.reverse_edges.len(adapter.get_trailing_actions()) {
			let e = *node_ref.reverse_edges.index(adapter.get_trailing_actions(), i);
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(edge.from, v, edge.val, None)? {
				edge.val += offset;
				i += 1;
			} else {
				let _ = self.borrow_node_mut(self.edges[e].from).edges.swap_remove_element(adapter.get_trailing_actions(), &e);
				let _ = node_ref.reverse_edges.swap_remove(adapter.get_trailing_actions(), i);
			}
		}
		let mut open = node_ref.open_edges.iter(adapter.get_trailing_actions());
		while let Some(&e) = open.next() {
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(v, edge.to, edge.val, edge.bool_var)? {
				edge.val -= offset;
			} else {
				self.close_imp_edge_forward(adapter, &mut open, e);
			}
		}
		let mut rev_open = node_ref.open_reverse_edges.iter(adapter.get_trailing_actions());
		while let Some(&e) = rev_open.next() {
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(edge.from, edge.to, edge.val, edge.bool_var)? {
				edge.val += offset;
			} else {
				self.close_imp_edge_forward(adapter, &mut rev_open, e);
			}
		}
		Ok(())

	}

	/// Moves all edges from the old node to the new node, adapted by the given offset.
	fn unify_nodes<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, state: &mut DifferenceLogicState, old: usize, new: usize, offset: IntVal, distances: &mut Vec<Vec<IntVal>>, direct_edge: &mut Vec<HashSet<usize>>) -> Result<(), E> {

		trace!("Moving all edges from node {old} to node {new} with offset {offset}");
		let temp_node_old = self.get_node_clone(old);
		let mut node_ref_old = temp_node_old.borrow_mut();
		let temp_node_new = self.get_node_clone(new);
		let mut mod_edges = Vec::new();
		let reached = direct_edge.get_mut(new).unwrap();
		for &e in node_ref_old.edges.iter(adapter.get_trailing_actions()) {
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(new, edge.to, edge.val - offset, None)? && (distances[new][edge.to] > edge.val - offset || (distances[new][edge.to] == edge.val - offset && !reached.contains(&edge.to))) {
				edge.from = new;
				edge.val -= offset;
				temp_node_new.borrow_mut().edges.push(adapter.get_trailing_actions(), e);
				let _ = reached.insert(edge.to);
				mod_edges.push(e);
			} else {
				let _ = self.borrow_node_mut(self.edges[e].to).reverse_edges.swap_remove_element(adapter.get_trailing_actions(), &e);
			}
		}
		for &e in node_ref_old.reverse_edges.iter(adapter.get_trailing_actions()) {
			let edge = self.edges.get_mut(e).unwrap();
			let reached = direct_edge.get_mut(edge.from).unwrap();
			if adapter.check_vars_different(edge.from, new, edge.val + offset, None)? && (distances[edge.from][new] > edge.val + offset || (distances[edge.from][new] == edge.val + offset && !reached.contains(&new))) {
				edge.to = new;
				edge.val += offset;
				temp_node_new.borrow_mut().reverse_edges.push(adapter.get_trailing_actions(), e);
				let _ = reached.insert(new);
				mod_edges.push(e);
			} else {
				let _ = self.borrow_node_mut(self.edges[e].from).edges.swap_remove_element(adapter.get_trailing_actions(), &e);
			}
		}
		let mut open = node_ref_old.open_edges.iter(adapter.get_trailing_actions());
		while let Some(&e) = open.next() {
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(new, edge.to, edge.val - offset, edge.bool_var)? {
				edge.from = new;
				edge.val -= offset;
				let mut node_ref_new = temp_node_new.borrow_mut();
				edge.out_index = node_ref_new.open_edges.len();
				node_ref_new.open_edges.push(e);
			} else {
				self.close_imp_edge_forward(adapter, &mut open, e);
			}

		}
		let mut rev_open = node_ref_old.open_reverse_edges.iter(adapter.get_trailing_actions());
		while let Some(&e) = rev_open.next() {
			let edge = self.edges.get_mut(e).unwrap();
			if adapter.check_vars_different(edge.from, new, edge.val + offset, edge.bool_var)? {
				edge.to = new;
				edge.val += offset;
				let mut node_ref_new = temp_node_new.borrow_mut();
				edge.in_index = node_ref_new.open_reverse_edges.len();
				node_ref_new.open_reverse_edges.push(e);
			} else {
				self.close_imp_edge_backward(adapter, &mut rev_open, e);
			}
		}
		adapter.trail_remove_node(node_ref_old.deref_mut());
		self.nodes[old] = None;
		self.open_nodes -= 1;
		// Check consequences of all modified active edges
		for e in mod_edges {
			let addition_success = self.propagate_edge_addition(adapter, &mut state.lb_updates, &mut state.ub_updates, e, true)?;
			debug_assert!(addition_success, "Failures should trigger a reformulation error");
		}
		Ok(())

	}

	/// Check if nodes with fixed domain exist, if yes remove them from the graph.
	fn check_remove_fixed_nodes<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A) {

		for n in 0..self.nodes.len() {
			if self.nodes[n].is_none() {
				continue;
			}
			if adapter.get_int_lower_bound(n) == adapter.get_int_upper_bound(n) {
				trace!("Var {n} has a fixed value - removing from graph");
				let val = adapter.get_int_lower_bound(n);
				let temp_node = self.get_node_clone(n);
				let mut node_ref = temp_node.borrow_mut();
				for &e in node_ref.edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[e];
					trace!("Removing outgoing edge {edge:?}");
					let _ = self.borrow_node_mut(edge.to).reverse_edges.swap_remove_element(adapter.get_trailing_actions(), &e);
				}
				for &e in node_ref.reverse_edges.iter(adapter.get_trailing_actions()) {
					let edge = &self.edges[e];
					trace!("Removing incoming edge {edge:?}");
					let _ = self.borrow_node_mut(edge.from).edges.swap_remove_element(adapter.get_trailing_actions(), &e);
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
			if self.nodes[n].is_none() {
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
			if self.bool_implications[b].is_none() {
				continue;
			}
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
						trace!("Constraint {edge:?} is implied");
						self.close_imp_edge_backward(adapter, &mut rev_open, index);
					}
				}
				let mut open = node.open_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (outgoing from {temp_node:?}, reverse)");
					if outgoing_v.contains_key(&edge.to) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 { // todo slight double work for reified constraints
						trace!("Constraint {edge:?} is falsified since inverse is implied");
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
						trace!("Constraint {:?} is implied", edge);
						self.close_imp_edge_forward(adapter, &mut open, index);
					}
				}
				let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
				while let Some(&index) = rev_open.next() {
					let edge = &self.edges[index];
					//trace!("Dealing with {edge:?} (incoming to {temp_node:?}, reverse)");
					if incoming_u.contains_key(&edge.from) && outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val <= -edge.val - 1 { // todo slight double work for reified constraints
						trace!("Constraint {:?} is falsified since inverse is implied", edge);
						fail_indices.push(index);
						self.close_imp_edge_backward(adapter, &mut rev_open, index);
					}
				}
			}
		}

		for index in fail_indices {  // todo check if we want this here or immediately inside the loops?
			let _ = self.inc_sat(adapter, index)?;  // TODO could also try these ones lazy?
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
					trace!("Constraint {:?} is falsified by bounds.", edge);
					adapter.set_bool_false(edge.bool_var, n, lb, edge.to, target_ub)?;  // TODO directly reenqueue these?
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				if self.get_cur_upper_bound(adapter, edge.from) - lb <= edge.val {
					// Constraint is implied by bounds.
					trace!("Constraint {:?} is implied by bounds.", edge);
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
					trace!("Constraint {:?} is implied by bounds.", edge);
					self.close_imp_edge_forward(adapter, &mut open, index);
				}
			}

			let mut rev_open = node.open_reverse_edges.iter(adapter.get_trailing_actions());
			while let Some(&index) = rev_open.next() {
				let edge = &self.edges[index];
				let source_lb = self.get_cur_lower_bound(adapter, edge.from);
				if source_lb - ub > edge.val {
					// Constraint is falsified by bounds.
					trace!("Constraint {:?} is falsified by bounds.", edge);
					adapter.set_bool_false(edge.bool_var, edge.from, source_lb, n, ub)?;
					self.close_imp_edge_backward(adapter, &mut rev_open, index);
				}
			}
		}

		state.reset_bound_changes();
		Ok(())
		
	}

	/// Propagate the addition of an edge, checking for conflicts and implications.
	fn propagate_edge_addition<E, A: ModelAdapter<E>>(&mut self, adapter: &mut A, lb_updates: &mut Vec<usize>, ub_updates: &mut Vec<usize>, index: usize, check_implied: bool) -> Result<bool, E> {
		// If the edge can't be added, a conflict will be generated
		if self.inc_sat(adapter, index)? {
			if check_implied {
				// If the edge was added, check the status of open edges.
				self.inc_imp(adapter, index)?;
			}
			let edge = &self.edges[index];
			let lb_y = -edge.val + self.get_cur_lower_bound(adapter, edge.from);
			if lb_y > self.get_cur_lower_bound(adapter, edge.to) {
				// New edge caused lower bound change.
				adapter.set_int_lower_bound(edge.to, lb_y, edge.bool_var, edge.from, self.get_cur_lower_bound(adapter, edge.from))?;
				self.update_lb(edge.to, lb_y, lb_updates);
			}
			let ub_x = edge.val + self.get_cur_upper_bound(adapter, edge.to);
			if ub_x < self.get_cur_upper_bound(adapter, edge.from) {
				// New edge caused upper bound change.
				adapter.set_int_upper_bound(edge.from, ub_x, edge.bool_var, edge.to, self.get_cur_upper_bound(adapter, edge.to))?;
				self.update_ub(edge.from, ub_x, ub_updates);
			}
			return Ok(true);
		}
		Ok(false)
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
					if !self.close_imp_edge_boolean(adapter, &mut open, index) {
						// Indicates that the edge was already closed via inc_imp before.
						continue;
					}
					self.activate_imp_edge(adapter, index);
					let addition_success = self.propagate_edge_addition(adapter, &mut state.lb_updates, &mut state.ub_updates, index, check_implied)?;  // TODO can we combine adding multiple edges?
					debug_assert!(addition_success, "Failure should have propagated earlier!");
				}
			} else {
				// Consequences of setting the boolean to false -> close all implied edges.
				let list_ref = self.get_implications_clone(b);
				let mut mut_list = list_ref.borrow_mut();
				let mut open = mut_list.iter(adapter.get_trailing_actions());
				while let Some(&index) = open.next() {
					trace!("Closing edge {:?})", self.edges[index]);
					let _ = self.close_imp_edge_boolean(adapter, &mut open, index);
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

	/// Check if the integer variables v1 and v2 are based on different underlying variables,
	/// if not reemit them as separate constraints.
	fn check_vars_different(&mut self, _v1: usize, _v2: usize, _d: IntVal, _b: Option<usize>) -> Result<bool, E> {
		panic!("Variables with the same definition can't be resolved by this adapter!");
	}

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

	/// Unify the given variables with the given offset (x - y = d). Note that the default is to fail.
	fn unify_variables(&mut self, _x: usize, _y: usize, _d: IntVal) -> Result<(), E> {
		panic!("Unifying variables is not supported by this adapter!");
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

	fn advise_of_backtrack(&mut self, _actions: &mut E) {
		trace!("Backtrack advise");
		self.state.reset_bound_changes();
		self.state.reset_bool_changes();
	}

	fn advise_of_bool_change(&mut self, _actions: &mut E, _view: BoolView, data: u64) -> bool {
		trace!("Boolean b{data} fixed.");
		self.state.fixed_bools.insert(data as usize)
	}

	fn advise_of_int_change(&mut self, _actions: &mut E, _view: IntView, event: IntEvent, data: u64) -> bool {
		trace!("Integer i{data} changed on event {event:?}.");
		match event {
			IntEvent::LowerBound => self.state.lower_bound_changes.insert(data as usize),
			IntEvent::UpperBound => self.state.upper_bound_changes.insert(data as usize),
			IntEvent::Fixed => {  // TODO can we find out which one changed?
				self.state.lower_bound_changes.insert(data as usize) |
				self.state.upper_bound_changes.insert(data as usize)
			},
			_ => unreachable!("Event was never enqueued."),
		}
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
	use std::num::NonZero;
	use itertools::Itertools;
	use pindakaas::solver::propagation::PropagatingSolver;
	use pindakaas::Lit as RawLit;
	use rangelist::RangeList;
	use tracing::trace;
	use tracing_test::traced_test;

	use crate::constraints::difference_logic::{DiffEdge, DifferenceLogic, DifferenceLogicConstraint, DifferenceLogicGraph, ModelAdapter, SolverModelAdapter};
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
		let (solver, engine) = slv.oracle.access_solving();
		let mut ctx = SolvingContext::new(solver, &mut engine.state);
		let mut model_adapter = SolverModelAdapter::new(&mut ctx, &int_vars, &bool_vars);
		let _  = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 0, 1, None));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(1, 2, -4, Some(0)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 1, 3, Some(1)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 1, 2, Some(2)));
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
		let _  = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 1, 2, None));
		let new_index = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(1, 2, 1, None));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(2, 0, -4, Some(0)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 2, 3, Some(1)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 2, 2, Some(2)));
		let _ = graph.new_edge(model_adapter.get_trailing_actions(), DiffEdge::new(0, 3, 2, Some(3)));
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

	#[test]
	#[traced_test]
	fn test_equal() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], -1));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[1], int_vars[0], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[2], int_vars[0], -1));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[3].0 else {
			panic!("Should not happen");
		};
		assert!(prb.unify_int(int_vars[0], IntDecision(IntDecisionInner::Linear(LinearTransform {scale: NonZero::new(2).unwrap(), offset: 1}, var_index))).is_ok());
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
			x - y <= -2 && z - x <= 3 && (b < 1 || x - z <= 2) && (b < 1 || x - y <= -2) && (c < 1 || y - x <= 2) && (c < 1 || z - x <= -1) && 2*t+1 == x
		});
	}

	#[test]
	#[traced_test]
	fn test_unification() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let b = prb.new_bool_var();
		let c = prb.new_bool_var();
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 3));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[2], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(b, int_vars[0], int_vars[1], -2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[1], int_vars[0], 2));
		diff_logic.add(DifferenceLogicConstraint::Implied(c, int_vars[2], int_vars[0], -1));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());
		let IntDecisionInner::Var(var_index) = int_vars[2].0 else {
			panic!("Should not happen");
		};
		assert!(prb.unify_int(int_vars[0], IntDecision(IntDecisionInner::Linear(LinearTransform::offset(1), var_index))).is_ok());
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
			x - y <= -2 && z - x <= 3 && (b < 1 || x - z <= 2) && (b < 1 || x - y <= -2) && (c < 1 || y - x <= 2) && (c < 1 || z - x <= -1) && z+1 == x
		});
	}

	#[test]
	#[traced_test]
	fn test_constants() {
		let mut prb = Model::default();
		let int_vars = prb.new_int_vars(3, RangeList::from_iter([1..=10]));
		let mut diff_logic = DifferenceLogic::new(PriorityLevel::Low);
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[0], int_vars[1], 3));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[1], int_vars[2], -2));
		diff_logic.add(DifferenceLogicConstraint::Global(int_vars[2], int_vars[0], 5));
		let _ = diff_logic.process(&mut prb, 2);  //TODO adapt level when definition changes
		assert!(diff_logic.simplify(&mut prb).is_ok());
		assert!(prb.unify_int(int_vars[0], IntDecision::from(5)).is_ok());
		assert!(prb.unify_int(int_vars[2], IntDecision::from(5)).is_ok());
		assert!(diff_logic.simplify(&mut prb).is_ok());

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let mut actions = ReformulationContext {
			slv: &mut slv,
			map: &map,
		};
		assert!(<DifferenceLogic as Constraint<Model>>::to_solver(&mut diff_logic, &mut actions).is_ok());
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
