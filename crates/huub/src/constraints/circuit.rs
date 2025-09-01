//! Structures and algorithms for constraints related to Hamiltonian cycles. These constraints
//! enforce that each integer decision variable in an array contains the index of the next node in
//! the cycle.

use itertools::Itertools;

use crate::{
	actions::{
		ConstraintInitActions, ExplanationActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions,
	},
	constraints::{
		int_all_different::IntAllDifferentBounds, Conflict, Constraint, PropagationActions,
		Propagator, SimplificationStatus,
	},
	reformulate::ReformulationError,
	solver::{
		activation_list::{IntEvent, IntPropCond},
		queue::PriorityLevel,
		trail::TrailedInt,
		IntView, IntViewInner,
	},
	IntDecision,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `circuit` constraint within a model.
///
/// This constraint enforces that an array of integer decision variables defines a single
/// Hamiltonian cycle. Each variable indexed in the array stores the index of the next node.
pub struct Circuit {
	/// Variables defining the immediate successor of each node in the cycle
	pub(crate) next: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Checking propagator for the `circuit` constraint.
pub struct CircuitChecking {
	/// Array of decision variables defining the immediate successor node of every node
	next: Vec<IntView>,
	/// The first node in the chain that includes each node indexed in the array
	first: Vec<TrailedInt>,
	/// The last node in the chain that includes each node indexed in the array
	last: Vec<TrailedInt>,
	/// The length of the chain that includes each node indexed in the array
	length: Vec<TrailedInt>,
	/// List of (indexes of) variable signaled to be fixed
	action_list: Vec<usize>,
}

impl<S: SimplificationActions> Constraint<S> for Circuit {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		// Register all successor variables for simplification when their domains are updated.
		for v in &self.next {
			actions.simplify_on_change_int(*v);
		}
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let num_nodes = self.next.len();
		let ub = num_nodes as i64 - 1;
		for (i, &var) in self.next.iter().enumerate() {
			// The domain of every variable is bounded by the size of the array.
			actions.set_int_lower_bound(var, 0)?;
			actions.set_int_upper_bound(var, ub)?;
			// The Hamiltonian cycle spans all nodes and therefore disallow nodes from forming a
			// self-loop. A self-loop is indicated by next[i] == i.
			actions.set_int_not_eq(var, i as i64)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		// Reformulate the model-level circuit constraint into a solver-level propagator and
		// register it.
		let next: Vec<_> = self.next.iter().map(|v| slv.get_solver_int(*v)).collect();
		IntAllDifferentBounds::new_in(slv, next.clone());
		CircuitChecking::new_in(slv, next);
		Ok(())
	}
}

impl CircuitChecking {
	/// Create a new [`CircuitChecking`] propagator and post it in the solver.
	pub fn new_in<P>(solver: &mut P, next: Vec<IntView>)
	where
		P: PropagatorInitActions + ?Sized,
	{
		// Create a list of indices of decisions that are already fixed.
		let action_list: Vec<usize> = next
			.iter()
			.enumerate()
			.flat_map(|(i, v)| {
				if let IntView(IntViewInner::Const(_)) = v {
					Some(i)
				} else {
					None
				}
			})
			.collect();
		// If the list is not empty, then the propagator should be enqueued at the root level.
		let enqueue = !action_list.is_empty();
		// Create the trailed data structures and post the propagator to the solver.
		let num_nodes = next.len() as i64;
		let first = (0..num_nodes).map(|i| solver.new_trailed_int(i)).collect();
		let last = (0..num_nodes).map(|i| solver.new_trailed_int(i)).collect();
		let length = (0..num_nodes).map(|_| solver.new_trailed_int(0)).collect();
		let prop = solver.add_propagator(
			Box::new(Self {
				next: next.clone(),
				first: first,
				last: last,
				length: length,
				action_list,
			}),
			PriorityLevel::Lowest,
		);
		// Let the propagator be advised when each specific decision is fixed to a value, with the
		// index of the decision.
		for (i, &var) in next.iter().enumerate() {
			solver.advise_on_int_change(prop, var, IntPropCond::Fixed, i as u64);
		}
		// Advise the propagator of backtracking to clear the list of fixed decision (indices).
		solver.advise_on_backtrack(prop);
		if enqueue {
			solver.enqueue_now(prop);
		}
	}
}

impl<P, E> Propagator<P, E> for CircuitChecking
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn advise_of_backtrack(&mut self, _actions: &mut E) {
		// We forget any previously remembered fixed decisions.
		self.action_list.clear();
	}

	fn advise_of_int_change(
		&mut self,
		_actions: &mut E,
		_view: IntView,
		event: IntEvent,
		data: u64,
	) -> bool {
		// Record that the decision at index `data` has been fixed to a value.
		debug_assert_eq!(event, IntEvent::Fixed);
		self.action_list.push(data as usize);
		true
	}

	#[tracing::instrument(name = "circuit", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		debug_assert!(!self.action_list.is_empty() && self.action_list.iter().all_unique());
		for &i in &self.action_list {
			// Get the value that next[i] is fixed to.
			let j = actions.get_int_val(self.next[i]).unwrap();
			// Find the start and end of the new chain.
			let first = actions.get_trailed_int(self.first[i]);
			let last = actions.get_trailed_int(self.last[j as usize]);
			// Compute the length of the new chain.
			let length = actions.get_trailed_int(self.length[first as usize])
				+ actions.get_trailed_int(self.length[j as usize])
				+ 1;
			// Form the new chain by connecting the two existing chains together.
			let _ = actions.set_trailed_int(self.first[last as usize], first);
			let _ = actions.set_trailed_int(self.last[first as usize], last);
			let _ = actions.set_trailed_int(self.length[first as usize], length);
			// Disallow the end of the chain from connecting to the start of the chain unless it
			// connects to the start of the chain, in which case the chain forms a valid
			// Hamiltonian cycle through all nodes.
			let num_nodes = self.next.len() as i64;
			if length < num_nodes - 1 {
				let mut reason = Vec::new();
				let mut i = first;
				loop {
					let next_i = self.next[i as usize];
					reason.push(actions.get_int_val_lit(next_i).unwrap());
					i = actions.get_int_val(next_i).unwrap();
					if i == last {
						break;
					}
				}
				debug_assert!(!reason.is_empty(), "Reason is empty");
				actions.set_int_not_eq(self.next[last as usize], first, reason)?
			}
		}
		self.action_list.clear();
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{circuit, reformulate::InitConfig, Decision, Model};

	#[test]
	#[traced_test]
	fn test_circuit_sat_1() {
		let mut prb = Model::default();
		let a = prb.new_int_var((0..=6).into());
		let b = prb.new_int_var((0..=0).into());
		let c = prb.new_int_var((0..=6).into());
		let d = prb.new_int_var((0..=6).into());

		prb += circuit(vec![a, b, c, d]);
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, d]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
        2, 0, 3, 1
        3, 0, 1, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_circuit_sat_2() {
		let mut prb = Model::default();
		let a = prb.new_int_var((0..=5).into());
		let b = prb.new_int_var((0..=4).into());
		let c = prb.new_int_var((0..=9).into());
		let d = prb.new_int_var((0..=7).into());

		prb += circuit(vec![a, b, c, d]);
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, d]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
        1, 2, 3, 0
        1, 3, 0, 2
        2, 0, 3, 1
        2, 3, 1, 0
        3, 0, 1, 2
        3, 2, 0, 1"#]],
		);
	}

	// #[test]
	// #[traced_test]
	// fn test_circuit_disconnected_1() {
	//     let mut prb = Model::default();
	//     let a = prb.new_int_var((0..=1).into());
	//     let b = prb.new_int_var((0..=1).into());
	//     let c = prb.new_int_var((2..=3).into());
	//     let d = prb.new_int_var((2..=3).into());

	//     prb += circuit(vec![a, b, c, d]);
	//     prb.assert_unsatisfiable();
	// }

	#[test]
	#[traced_test]
	fn test_circuit_disconnected_2() {
		let mut prb = Model::default();
		let a = prb.new_int_var((0..=1).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((0..=2).into());
		let d = prb.new_int_var((3..=3).into());

		prb += circuit(vec![a, b, c, d]);
		prb.assert_unsatisfiable();
	}
}
