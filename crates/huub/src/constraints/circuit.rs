//! Structures and algorithms for the `circuit` and `subcircuit` global
//! constraints, which enforce that the successor variables form a single
//! cycle through all nodes (or a single cycle through a subset of the nodes,
//! in the `subcircuit` variant).

mod check;
mod graph;
mod prevent;
mod scc;

use itertools::Itertools;

pub use crate::constraints::circuit::{
	check::CircuitCheck, prevent::CircuitPrevent, scc::CircuitScc,
};
use crate::{
	actions::{
		IntAnalyzeActions, IntEvent, IntPropagationActions, IntSimplificationActions,
		ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	IntSet, IntVal,
};

/// Representation of the `circuit` / `subcircuit` constraint within a model.
///
/// Enforces that the successor variables form a single cycle through all nodes
/// (or, for `subcircuit`, through a subset, with the rest self-looping).
/// Three propagation algorithms (`check` / `prevent` / `scc`) are implemented.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Circuit {
	/// The `check` propagator instance (also holds the canonical successor
	/// graph).
	pub(crate) check_prop: CircuitCheck<View<IntVal>>,
	/// The `prevent` propagator instance.
	prevent_prop: CircuitPrevent<View<IntVal>>,
	/// The `scc` propagator instance.
	scc_prop: CircuitScc<View<IntVal>>,
	/// Whether to enable the `check` algorithm (`None` ⇒ default).
	check: Option<bool>,
	/// Whether to enable the `prevent` algorithm (`None` ⇒ default).
	prevent: Option<bool>,
	/// Whether to enable the `scc` algorithm (`None` ⇒ default).
	scc: Option<bool>,
}

impl Circuit {
	/// Resolve which algorithms to run/post, defaulting each unset flag to
	/// enabled. `prevent` is never sound on its own — it leaves closed
	/// sub-tours unrejected — so `check` is forced on whenever neither `check`
	/// nor `scc` was requested.
	fn flags(&self) -> (bool, bool, bool) {
		let mut check = self.check.unwrap_or(true);
		let prevent = self.prevent.unwrap_or(true);
		let scc = self.scc.unwrap_or(true);
		if !check && !scc {
			check = true;
		}
		(check, prevent, scc)
	}

	/// Create a new `circuit` (or `subcircuit`) constraint over the given
	/// successor variables, where `vars[i] == offset + j` means node `i`'s
	/// successor is node `j`. A `None` flag defers to the default algorithm
	/// set.
	pub(crate) fn new(
		vars: Vec<View<IntVal>>,
		offset: IntVal,
		subcircuit: bool,
		check: Option<bool>,
		prevent: Option<bool>,
		scc: Option<bool>,
	) -> Self {
		Self {
			check_prop: CircuitCheck::new(vars.clone(), offset, subcircuit),
			prevent_prop: CircuitPrevent::new(vars.clone(), offset, subcircuit),
			scc_prop: CircuitScc::new(vars, offset, subcircuit),
			check,
			prevent,
			scc,
		}
	}
}

impl<E> Constraint<E> for Circuit
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		for dcn in &self.check_prop.graph.vars {
			dcn.request_direct_eager(ctx);
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		let graph = &self.check_prop.graph;
		let offset = graph.offset;
		let max_node = offset + graph.vars.len() as IntVal - 1;
		// Tighten every successor to the node range (offset..=max_node).
		for v in &graph.vars {
			v.tighten_min(ctx, offset, [])?;
			v.tighten_max(ctx, max_node, [])?;
		}
		// Every node lies on the cycle, so none is its own successor.
		if !graph.subcircuit {
			for (i, v) in graph.vars.iter().enumerate() {
				let self_val = offset + i as IntVal;
				v.exclude(ctx, &IntSet::from_iter([self_val..=self_val]), [])?;
			}
		}
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let (check, prevent, scc) = self.flags();
		let graph = &self.check_prop.graph;
		let (offset, subcircuit) = (graph.offset, graph.subcircuit);
		let vars = graph
			.vars
			.iter()
			.map(|&var| slv.solver_view(var))
			.collect_vec();
		if check {
			CircuitCheck::post(slv, vars.clone(), offset, subcircuit);
		}
		if prevent {
			CircuitPrevent::post(slv, vars.clone(), offset, subcircuit);
		}
		if scc {
			CircuitScc::post(slv, vars, offset, subcircuit);
		}
		Ok(())
	}
}

impl<E> Propagator<E> for Circuit
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
{
	fn advise_of_int_change(
		&mut self,
		_: &mut E::NotificationContext<'_>,
		_data: u64,
		_event: IntEvent,
	) -> bool {
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// Delegate to each enabled propagator so it subscribes to its own events
		// (`check`/`prevent` to `Fixed`, `scc` to `Domain`).
		let (check, prevent, scc) = self.flags();
		if check {
			self.check_prop.initialize(ctx);
		}
		if prevent {
			self.prevent_prop.initialize(ctx);
		}
		if scc {
			self.scc_prop.initialize(ctx);
		}
	}

	#[tracing::instrument(name = "circuit", target = "solver", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let (check, prevent, scc) = self.flags();
		// Cheapest-first: stop as soon as an algorithm reports a conflict.
		if check {
			self.check_prop.propagate(ctx)?;
		}
		if prevent {
			self.prevent_prop.propagate(ctx)?;
		}
		if scc {
			self.scc_prop.propagate(ctx)?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	// Single-round, per-algorithm tests: post one propagator (no `alldifferent`),
	// run one `Solver::propagate_next`, assert the exact inference.
	use crate::{
		actions::{IntDecisionActions, IntInspectionActions},
		constraints::circuit::{CircuitCheck, CircuitPrevent, CircuitScc},
		solver::{
			branchers::WarmStartBrancher, IntLitMeaning, LiteralStrategy, View as SolverView,
		},
		IntSet,
	};
	use crate::{
		model::{Model, View},
		solver::{Solver, Status},
		IntVal,
	};

	/// Collect every solution of the model as a sorted list of successor-value
	/// vectors.
	fn collect(mut prb: Model, model_vars: &[View<IntVal>]) -> Vec<Vec<IntVal>> {
		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let vars = model_vars
			.iter()
			.map(|&x| map.get(&mut slv, x))
			.collect_vec();
		let mut solns: Vec<Vec<IntVal>> = Vec::new();
		let status = slv
			.solve()
			.all_solutions(vars.iter().map(|&v| crate::solver::AnyView::from(v)))
			.collect_solutions_in(vars.clone(), &mut solns)
			.satisfy();
		assert_eq!(status, Status::Complete);
		solns.sort();
		solns
	}

	/// Whether `sol` (1-based successor values) forms a single Hamiltonian
	/// cycle.
	fn is_circuit(sol: &[IntVal]) -> bool {
		let n = sol.len();
		let mut visited = vec![false; n];
		let mut node = 0;
		let mut count = 0;
		while !visited[node] {
			visited[node] = true;
			count += 1;
			let next = (sol[node] - 1) as usize;
			if next >= n {
				return false;
			}
			node = next;
		}
		count == n && node == 0
	}

	/// Whether `sol` (1-based successor values) is a valid `subcircuit`: the
	/// non-self-loop nodes form a single cycle and the rest self-loop.
	fn is_subcircuit(sol: &[IntVal]) -> bool {
		let n = sol.len();
		let in_cycle = (0..n).filter(|&i| (sol[i] - 1) as usize != i).collect_vec();
		if in_cycle.is_empty() {
			return true;
		}
		let start = in_cycle[0];
		let mut visited = vec![false; n];
		let mut node = start;
		let mut count = 0;
		while !visited[node] {
			if (sol[node] - 1) as usize == node {
				return false;
			}
			visited[node] = true;
			count += 1;
			let next = (sol[node] - 1) as usize;
			if next >= n {
				return false;
			}
			node = next;
		}
		node == start && count == in_cycle.len()
	}

	/// Build `n` successor decisions (1-based values) with eager literals so
	/// the exact propagated literals are observable.
	fn succ_vars(
		slv: &mut Solver,
		doms: &[std::ops::RangeInclusive<IntVal>],
	) -> Vec<SolverView<IntVal>> {
		doms.iter()
			.map(|d| {
				slv.new_int_decision(d.clone())
					.order_literals(LiteralStrategy::Eager)
					.direct_literals(LiteralStrategy::Eager)
					.view()
			})
			.collect()
	}

	#[test]
	#[traced_test]
	fn test_check_detects_subtour() {
		// `check` alone: a fixed 2-cycle 0->1->0 over 3 nodes is a closed sub-tour
		// of length < n, so one round must report a conflict.
		let mut slv = Solver::default();
		let vars = succ_vars(&mut slv, &[2..=2, 1..=1, 1..=3]); // 0->1, 1->0, 2 free
		CircuitCheck::post(&mut slv, vars, 1, false);
		assert!(
			slv.propagate_next().is_err(),
			"check should fail on the 0<->1 sub-tour"
		);
	}

	#[test]
	#[traced_test]
	fn test_circuit_all_solutions_are_cycles() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, 1..=4);
		prb.circuit(vars.iter().copied()).post().unwrap();
		let solns = collect(prb, &vars);
		// There are (n-1)! = 6 Hamiltonian cycles on 4 nodes.
		assert_eq!(solns.len(), 6);
		assert!(solns.iter().all(|s| is_circuit(s)));
	}

	#[test]
	#[traced_test]
	fn test_circuit_basic() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 1..=3);
		prb.circuit(vars.iter().copied()).post().unwrap();
		let (mut slv, map) = prb.lower().to_solver().unwrap();
		let vars = vars.into_iter().map(|x| map.get(&mut slv, x)).collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		2, 3, 1
		3, 1, 2"#]],
		);
	}

	/// Every propagator configuration must yield the same set of solutions.
	#[test]
	#[traced_test]
	fn test_circuit_configs_agree() {
		// `check` stays on in every config (it rejects fully-fixed sub-tours at
		// leaves); the configs' agreement is the soundness gate.
		let configs = [
			(true, false, false),
			(true, true, false),
			(true, false, true),
			(true, true, true),
		];
		let mut reference: Option<Vec<Vec<IntVal>>> = None;
		for (check, prevent, scc) in configs {
			let mut prb = Model::default();
			let vars = prb.new_int_decisions(6, 1..=6);
			prb.circuit(vars.iter().copied())
				.check_propagation(check)
				.prevent_propagation(prevent)
				.scc_propagation(scc)
				.post()
				.unwrap();
			let solns = collect(prb, &vars);
			assert!(solns.iter().all(|s| is_circuit(s)));
			assert_eq!(solns.len(), 120); // (6-1)! = 120
			match &reference {
				None => reference = Some(solns),
				Some(r) => assert_eq!(r, &solns, "config {check},{prevent},{scc} disagrees"),
			}
		}
	}

	#[test]
	#[traced_test]
	fn test_circuit_enumerates_all_cycles() {
		// A 6-node circuit must enumerate exactly the (6-1)! = 120 Hamiltonian
		// cycles, and every solution must be a single valid cycle.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(6, 1..=6);
		prb.circuit(vars.iter().copied()).post().unwrap();
		let solns = collect(prb, &vars);
		assert_eq!(solns.len(), 120);
		assert!(solns.iter().all(|s| is_circuit(s)));
	}

	/// A disconnected graph (two size-3 groups that never point at each other)
	/// is unsatisfiable but only `scc` can see it — there is no fixed sub-tour
	/// for `check`. Size-3 groups keep every domain > 1 so self-loop exclusion
	/// does not collapse them into a sub-tour `check` would catch.
	#[test]
	#[traced_test]
	fn test_circuit_scc_disconnection() {
		for scc in [false, true] {
			let mut prb = Model::default();
			// Nodes 0,1,2 may only point within {0,1,2}; nodes 3,4,5 within {3,4,5}.
			let g0 = prb.new_int_decision(1..=3);
			let g1 = prb.new_int_decision(1..=3);
			let g2 = prb.new_int_decision(1..=3);
			let g3 = prb.new_int_decision(4..=6);
			let g4 = prb.new_int_decision(4..=6);
			let g5 = prb.new_int_decision(4..=6);
			let posted = prb
				.circuit([g0, g1, g2, g3, g4, g5])
				.scc_propagation(scc)
				.post();
			if scc {
				// The connectivity rule rejects the instance at the root.
				assert!(posted.is_err(), "scc must detect the disconnection");
				continue;
			}
			// Without scc the instance is still unsatisfiable, but only found
			// during search; either way the solution set is empty.
			posted.unwrap();
			let (mut slv, _): (Solver, _) = prb.lower().to_solver().unwrap();
			assert_eq!(slv.solve().satisfy(), Status::Unsatisfiable);
		}
	}

	#[test]
	#[traced_test]
	fn test_circuit_unsat_subtour() {
		// Force the 2-cycle 0 <-> 1, which cannot extend to a circuit over 3 nodes.
		let mut prb = Model::default();
		let a = prb.new_int_decision(2..=2); // node 0 -> node 1
		let b = prb.new_int_decision(1..=1); // node 1 -> node 0
		let c = prb.new_int_decision(1..=3);
		assert!(prb.circuit([a, b, c]).post().is_err());
	}

	#[test]
	#[traced_test]
	fn test_circuit_zero_based() {
		// Regression: a 0-based array (`offset = 0`) must yield both Hamiltonian
		// cycles, not a spurious UNSAT (the FlatZinc handler used to hardcode
		// `offset = 1`, mapping value 0 to "not a node").
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 0..=2);
		prb.circuit(vars.iter().copied()).offset(0).post().unwrap();
		let solns = collect(prb, &vars);
		// The two directed Hamiltonian cycles on {0,1,2}: 0->1->2->0 and 0->2->1->0.
		assert_eq!(solns, vec![vec![1, 2, 0], vec![2, 0, 1]]);
	}

	#[test]
	#[traced_test]
	fn test_circuit_narrows_wide_successor_domain() {
		// Regression: a successor declared wider than the index set (offset 2,
		// domain -100..100 over nodes 2..=5) must be narrowed to the node range, so
		// no out-of-range value can satisfy the circuit.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, -100..=100);
		prb.circuit(vars.iter().copied()).offset(2).post().unwrap();
		let solns = collect(prb, &vars);
		assert_eq!(solns.len(), 6, "expected 6 cycles, got {solns:?}");
		assert!(
			solns
				.iter()
				.all(|s| s.iter().all(|&v| (2..=5).contains(&v))),
			"a successor escaped the node range 2..=5: {solns:?}"
		);
	}

	#[test]
	#[traced_test]
	fn test_subcircuit_narrows_wide_successor_domain() {
		// The same range bound applies to `subcircuit`: successors are still nodes
		// (self-loops included, which lie in range), so a wide declared domain must
		// not admit out-of-range values.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, -100..=100);
		prb.subcircuit(vars.iter().copied())
			.offset(2)
			.post()
			.unwrap();
		let solns = collect(prb, &vars);
		assert_eq!(solns.len(), 21, "expected 21 subcircuits, got {solns:?}");
		assert!(
			solns
				.iter()
				.all(|s| s.iter().all(|&v| (2..=5).contains(&v))),
			"a successor escaped the node range 2..=5: {solns:?}"
		);
	}

	#[test]
	#[traced_test]
	fn test_prevent_removes_chain_closing_edge() {
		// `prevent` alone on the open fixed chain 0->1->2 (n=4): the chain must not
		// close early, so edge 2->0 (value 1) is removed from succ[2].
		let mut slv = Solver::default();
		// 0->1 (val 2), 1->2 (val 3), 2 and 3 free.
		let vars = succ_vars(&mut slv, &[2..=2, 3..=3, 1..=4, 1..=4]);
		let s2 = vars[2];
		CircuitPrevent::post(&mut slv, vars, 1, false);
		let propagated = slv
			.propagate_next()
			.expect("prevent must not conflict here");
		let forbid = s2.lit(&mut slv, IntLitMeaning::NotEq(1)); // succ[2] != node 0
		assert!(
			propagated.contains(&forbid),
			"prevent should forbid closing the chain (succ[2] != 1); got {propagated:?}"
		);
		assert!(
			!s2.in_domain(&slv, 1),
			"value 1 should be pruned from succ[2]"
		);
	}

	#[test]
	fn test_scc_deep_chain_no_stack_overflow() {
		// The `scc` DFS is iterative, so a depth-`n` fixed chain must not overflow
		// the call stack. `n` is well past any recursion limit.
		let n = 20000;
		let mut slv = Solver::default();
		let mut vars = Vec::with_capacity(n as usize);
		for i in 0..n {
			let succ = if i + 1 < n { i + 2 } else { 1 }; // node i -> node (i+1) mod n
			vars.push(slv.new_int_decision(succ..=succ).view());
		}
		CircuitScc::post(&mut slv, vars, 1, false);
		// One propagation round on the deep fixed chain: must return cleanly.
		let _ = slv.propagate_next();
	}

	#[test]
	#[traced_test]
	fn test_scc_detects_closed_subset_reachable_from_root() {
		// Node 0 reaches every node, so a root-0 DFS sees no disconnection — but
		// {1,2,3} is closed (none can point back to 0), so the cycle can never
		// return: infeasible. `scc` finds the sink component; nothing is fixed, so
		// `check`/`prevent` see nothing.
		let mut slv = Solver::default();
		// 1-based values; only node 0 points to value 1 (=node 0), so {1,2,3} has
		// no edge out.
		let vars = succ_vars(
			&mut slv,
			&[
				2..=4, // 0 -> nodes 1,2,3
				3..=4, // 1 -> nodes 2,3
				2..=2, // placeholder, overwritten below
				2..=2,
			],
		);
		// Rebuild nodes 2 and 3 with the intended (non-contiguous) domains.
		let s0 = vars[0];
		let s1 = vars[1];
		let s2 = slv
			.new_int_decision(IntSet::from_iter([2..=2, 4..=4])) // 2 -> nodes 1,3
			.view();
		let s3 = slv
			.new_int_decision(IntSet::from_iter([2..=2, 3..=3])) // 3 -> nodes 1,2
			.view();
		CircuitScc::post(&mut slv, vec![s0, s1, s2, s3], 1, false);
		assert!(
			slv.propagate_next().is_err(),
			"scc should fail: {{1,2,3}} is a closed set unreachable-back-from, even though node 0 reaches it"
		);
	}

	#[test]
	#[traced_test]
	fn test_scc_detects_disconnection_one_round() {
		// `scc` alone: {0,1} and {2,3} never point at each other, so a single round
		// detects the disconnection (no fixed sub-tour for `check` to catch).
		let mut slv = Solver::default();
		let vars = succ_vars(&mut slv, &[1..=2, 1..=2, 3..=4, 3..=4]);
		CircuitScc::post(&mut slv, vars, 1, false);
		assert!(
			slv.propagate_next().is_err(),
			"scc should fail on the disconnected successor graph"
		);
	}

	#[test]
	#[traced_test]
	fn test_subcircuit_all_solutions_valid() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, 1..=4);
		prb.subcircuit(vars.iter().copied()).post().unwrap();
		let solns = collect(prb, &vars);
		assert!(solns.iter().all(|s| is_subcircuit(s)));
		// The all-self-loop assignment is a valid subcircuit.
		assert!(solns.contains(&vec![1, 2, 3, 4]));
		// A full Hamiltonian cycle is also a valid subcircuit.
		assert!(solns.contains(&vec![2, 3, 4, 1]));
		// A 2-cycle with the other nodes self-looping is also valid.
		assert!(solns.contains(&vec![2, 1, 3, 4]));
		// Exact count of subcircuits on 4 nodes:
		//   |S|=0: 1, |S|=2: C(4,2)=6, |S|=3: C(4,3)*2!=8, |S|=4: 3!=6  => 21.
		assert_eq!(solns.len(), 21);
	}

	#[test]
	fn test_subcircuit_check_reason_current_level() {
		let doms = [
			IntSet::from_iter([3..=3, 5..=6]),        // node0
			IntSet::from_iter([1..=4]),               // node1
			IntSet::from_iter([6..=6]),               // node2
			IntSet::from_iter([1..=2, 4..=4, 6..=6]), // node3
			IntSet::from_iter([1..=1, 5..=5]),        // node4
			IntSet::from_iter([3..=3, 5..=6]),        // node5
		];
		let mut prb = Model::default();
		let vars: Vec<View<IntVal>> = doms
			.iter()
			.map(|d| prb.new_int_decision(d.clone()))
			.collect();
		prb.subcircuit(vars.iter().copied())
			.check_propagation(true)
			.prevent_propagation(false)
			.scc_propagation(false)
			.post()
			.unwrap();
		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let svars = vars.iter().map(|&x| map.get(&mut slv, x)).collect_vec();
		let mut solns: Vec<Vec<IntVal>> = Vec::new();
		let status = slv
			.solve()
			.all_solutions(svars.iter().map(|&v| crate::solver::AnyView::from(v)))
			.collect_solutions_in(svars.clone(), &mut solns)
			.satisfy();
		assert_eq!(status, Status::Complete);
		for s in &solns {
			assert!(is_subcircuit(s), "emitted a non-subcircuit: {s:?}");
		}
	}

	#[test]
	fn test_subcircuit_check_under_fixed_search() {
		let mut prb = Model::default();
		let vars: Vec<View<IntVal>> = [
			IntSet::from_iter([1..=2]), // node0: self(1) or ->1(2)
			IntSet::from_iter([1..=2]), // node1: ->0(1) or self(2)
			IntSet::from_iter([3..=4]), // node2: self(3) or ->3(4)
			IntSet::from_iter([3..=3]), // node3: ->2(3), forced selected
		]
		.into_iter()
		.map(|d| prb.new_int_decision(d))
		.collect();
		prb.subcircuit(vars.iter().copied())
			.scc_propagation(false)
			.prevent_propagation(false)
			.post()
			.unwrap();
		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let svars: Vec<SolverView<IntVal>> = vars.iter().map(|&x| map.get(&mut slv, x)).collect();
		// Warm-start the {0,1} cycle: x0 = node1 (val 2), x1 = node0 (val 1).
		let d0 = svars[0].lit(&mut slv, IntLitMeaning::Eq(2));
		let d1 = svars[1].lit(&mut slv, IntLitMeaning::Eq(1));
		WarmStartBrancher::new_in(&mut slv, vec![d0, d1]);
		let mut sols: Vec<Vec<IntVal>> = Vec::new();
		let status = slv
			.solve()
			.all_solutions(svars.iter().map(|&v| crate::solver::AnyView::from(v)))
			.collect_solutions_in(svars.clone(), &mut sols)
			.satisfy();
		assert_eq!(status, Status::Complete);
		sols.sort();
		assert_eq!(
			sols,
			vec![vec![1, 2, 4, 3]],
			"w_in witness lost: the {{2,3}} subcircuit was wrongly pruned by an unsound nogood"
		);
	}

	#[test]
	#[traced_test]
	fn test_subcircuit_configs_agree() {
		// `check` stays on in every config (it rejects fully-fixed sub-tours at
		// leaves); the configs' agreement is the soundness gate.
		let configs = [
			(true, false, false),
			(true, true, false),
			(true, false, true),
			(true, true, true),
		];
		let mut reference: Option<Vec<Vec<IntVal>>> = None;
		for (check, prevent, scc) in configs {
			let mut prb = Model::default();
			let vars = prb.new_int_decisions(6, 1..=6);
			prb.subcircuit(vars.iter().copied())
				.check_propagation(check)
				.prevent_propagation(prevent)
				.scc_propagation(scc)
				.post()
				.unwrap();
			let solns = collect(prb, &vars);
			assert!(solns.iter().all(|s| is_subcircuit(s)));
			// Subcircuits on n=6: 1 + Σ_{k=2..6} C(6,k)·(k-1)!
			//   = 1 + 15 + 40 + 90 + 144 + 120 = 410.
			assert_eq!(solns.len(), 410);
			match &reference {
				None => reference = Some(solns),
				Some(r) => assert_eq!(
					r, &solns,
					"subcircuit config {check},{prevent},{scc} disagrees"
				),
			}
		}
	}

	#[test]
	// Release-only: the per-instance `minimize` bound-proving below is
	// pathologically slow in unoptimized debug builds.
	// Correctness is identical in both profiles.
	#[cfg_attr(debug_assertions, ignore = "release-only; minimize is debug-slow")]
	fn test_subcircuit_scc_soundness_oracle() {
		// Soundness oracle: `check`-only never prunes, so it enumerates every valid
		// subcircuit (the complete reference). On random gapped-domain instances,
		// check+prevent+scc must give the identical solution set — a divergence is
		// an scc rule (or its learned clause) dropping a feasible assignment.
		fn rng(s: &mut u64, m: u64) -> u64 {
			*s = s
				.wrapping_mul(6364136223846793005)
				.wrapping_add(1442695040888963407);
			(*s >> 33) % m
		}
		let mut seed: u64 = 0x1234_5678_9ABC_DEF0;
		for _ in 0..1500 {
			let n = 4 + rng(&mut seed, 3) as usize; // 4..=6
			let mut doms: Vec<IntSet> = Vec::with_capacity(n);
			for _ in 0..n {
				let dom = loop {
					// Random (often gapped) non-empty subset of 1..=n.
					let mut vals = Vec::new();
					for v in 1..=n as IntVal {
						if rng(&mut seed, 2) == 1 {
							vals.push(v..=v);
						}
					}
					if !vals.is_empty() {
						break IntSet::from_iter(vals);
					}
				};
				doms.push(dom);
			}
			// Enumerate every solution; any unsat path (post / simplify / solve)
			// is the empty solution set, so the two configs compare uniformly.
			let build = |scc: bool, prevent: bool| -> Vec<Vec<IntVal>> {
				let mut prb = Model::default();
				let vars: Vec<View<IntVal>> = doms
					.iter()
					.map(|d| prb.new_int_decision(d.clone()))
					.collect();
				if prb
					.subcircuit(vars.iter().copied())
					.check_propagation(true)
					.prevent_propagation(prevent)
					.scc_propagation(scc)
					.post()
					.is_err()
				{
					return vec![];
				}
				let (mut slv, map): (Solver, _) = match prb.lower().to_solver() {
					Ok(s) => s,
					Err(_) => return vec![],
				};
				let svars = vars.iter().map(|&x| map.get(&mut slv, x)).collect_vec();
				let mut solns: Vec<Vec<IntVal>> = Vec::new();
				let status = slv
					.solve()
					.all_solutions(svars.iter().map(|&v| crate::solver::AnyView::from(v)))
					.collect_solutions_in(svars.clone(), &mut solns)
					.satisfy();
				assert!(
					matches!(status, Status::Complete | Status::Unsatisfiable),
					"unexpected solve status {status:?}"
				);
				solns.sort();
				solns
			};
			let reference = build(false, false); // check only — sound, complete reference
			let full = build(true, true); // check + prevent + scc
			assert_eq!(
				reference, full,
				"subcircuit scc changed the solution set; n={n}, domains={doms:?}"
			);

			// Objective-consistency under minimization: an unsound reason only bites
			// while proving a bound, invisible to pure enumeration. check-only and
			// full must agree on the minimum of `succ[0]`.
			let min_opt = |scc: bool| -> Option<IntVal> {
				let mut prb = Model::default();
				let vars: Vec<View<IntVal>> = doms
					.iter()
					.map(|d| prb.new_int_decision(d.clone()))
					.collect();
				if prb
					.subcircuit(vars.iter().copied())
					.check_propagation(true)
					.prevent_propagation(true)
					.scc_propagation(scc)
					.post()
					.is_err()
				{
					return None;
				}
				let (mut slv, map): (Solver, _) = match prb.lower().to_solver() {
					Ok(s) => s,
					Err(_) => return None,
				};
				let obj = map.get(&mut slv, vars[0]);
				slv.solve().minimize(obj).1
			};
			assert_eq!(
				min_opt(false),
				min_opt(true),
				"subcircuit scc changed the minimum of succ[0]; n={n}, domains={doms:?}"
			);
		}
	}

	#[test]
	#[traced_test]
	fn test_subcircuit_zero_based() {
		// Regression (subcircuit dual of `test_circuit_3_zero_based`): a 0-based
		// node set (`offset = 0`) must not be falsely failed.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 0..=2);
		prb.subcircuit(vars.iter().copied())
			.offset(0)
			.post()
			.unwrap();
		let solns = collect(prb, &vars);
		// All-self-loop and a full cycle are both valid 0-based subcircuits.
		assert!(solns.contains(&vec![0, 1, 2]));
		assert!(solns.contains(&vec![1, 2, 0]));
		// 1 (empty) + C(3,2)=3 (2-cycles) + (3-1)!=2 (3-cycles) = 6.
		assert_eq!(solns.len(), 6);
	}
}
