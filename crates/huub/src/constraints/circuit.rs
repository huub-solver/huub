//! Structure and algorithms for the `circuit` and `subcircuit` constraint,
//! which enforce that the successor variables form a single cycle through
//! all nodes (or a single cycle through a subset of the nodes in the
//! `subcircuit` variant).
//!
//! This module exposes the [`Circuit`] model constraint together with the two
//! propagators [`CircuitNoCycle`] and [`CircuitScc`], each living in its own
//! submodule.

mod no_cycle;
mod scc;

use itertools::Itertools;

pub use crate::constraints::circuit::{no_cycle::CircuitNoCycle, scc::CircuitScc};
use crate::{
	IntVal,
	actions::{
		IntAnalyzeActions, IntDecisionActions, IntEvent, IntInspectionActions,
		IntPropagationActions, PropagationActions, ReasoningContext, ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::IntLitMeaning,
};

/// Representation of the `circuit` / `subcircuit` constraint within a model.
///
/// Enforces that the successor variables form a single cycle through all nodes
/// (or, for `subcircuit`, through a subset, with the rest self-looping).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Circuit<const SUBCIRCUIT: bool> {
	/// Instance of the [`CircuitNoCycle`] propagator.
	no_cycle_prop: CircuitNoCycle<SUBCIRCUIT, View<IntVal>>,
	/// Instance of the [`CircuitScc`] propagator.
	scc_prop: CircuitScc<SUBCIRCUIT, View<IntVal>>,
	/// Whether to enable the `no_cycle` propagator.
	///
	/// Defaults to `true`.
	no_cycle: Option<bool>,
	/// Whether to enable the `scc` propagator.
	///
	/// Defaults to `false`.
	scc: Option<bool>,
}

/// The successor-variable graph the circuit propagators reason over: one
/// successor variable per node position `0..n`, plus the value `offset`. The
/// `SUBCIRCUIT` const generic selects the `subcircuit` variant (nodes may
/// self-loop off the cycle), so the variant checks compile away.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct CircuitGraph<const SUBCIRCUIT: bool, I> {
	/// Successor variables, indexed by node position `0..n`.
	pub(crate) vars: Vec<I>,
	/// Successor value of node `0`.
	pub(crate) offset: IntVal,
	/// Number of nodes in the graph.
	n: usize,
}

impl<const SUBCIRCUIT: bool> Circuit<SUBCIRCUIT> {
	/// Create a new `circuit` (or `subcircuit`) constraint over the given
	/// successor variables, where `vars[i] == offset + j` means node `i`'s
	/// successor is node `j`.
	pub(crate) fn new(
		vars: Vec<View<IntVal>>,
		offset: IntVal,
		no_cycle: Option<bool>,
		scc: Option<bool>,
	) -> Self {
		Self {
			no_cycle_prop: CircuitNoCycle::new(vars.clone(), offset),
			scc_prop: CircuitScc::new(vars, offset),
			no_cycle,
			scc,
		}
	}

	/// Returns whether a `no_cycle` propagator will be posted when creating a
	/// [`Solver`](crate::solver::Solver) object.
	fn no_cycle_propagation(&self) -> bool {
		// If `no_cycle` and `scc` are both `false`, upgrade to run `no_cycle`.
		self.no_cycle.unwrap_or(true) || !self.scc_propagation()
	}

	/// Returns whether a `scc` propagator will be posted when creating a
	/// [`Solver`](crate::solver::Solver) object.
	fn scc_propagation(&self) -> bool {
		self.scc.unwrap_or(false)
	}
}

impl<const SUBCIRCUIT: bool, E> Constraint<E> for Circuit<SUBCIRCUIT>
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		// Use value encoding for every successor variable.
		for dcn in &self.no_cycle_prop.graph.vars {
			dcn.request_direct_eager(ctx);
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		let graph = &self.no_cycle_prop.graph;
		let offset = graph.offset;
		let max_node = offset + graph.vars.len() as IntVal - 1;
		// Tighten every successor to the node range (offset..=max_node).
		for v in &graph.vars {
			v.tighten_min(ctx, offset, [])?;
			v.tighten_max(ctx, max_node, [])?;
		}
		// Every node lies on the cycle, so none is its own successor.
		if !SUBCIRCUIT {
			for (i, v) in graph.vars.iter().enumerate() {
				let self_val = offset + i as IntVal;
				v.remove_val(ctx, self_val, [])?;
			}
		}
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let no_cycle = self.no_cycle_propagation();
		let scc = self.scc_propagation();
		let graph = &self.no_cycle_prop.graph;
		let offset = graph.offset;
		let vars = graph
			.vars
			.iter()
			.map(|&var| slv.solver_view(var))
			.collect_vec();
		if no_cycle {
			CircuitNoCycle::<SUBCIRCUIT, _>::post(slv, vars.clone(), offset);
		}
		if scc {
			CircuitScc::<SUBCIRCUIT, _>::post(slv, vars, offset);
		}
		Ok(())
	}
}

impl<const SUBCIRCUIT: bool, E> Propagator<E> for Circuit<SUBCIRCUIT>
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, ctx: &mut E::NotificationContext<'_>) {
		self.no_cycle_prop.advise_of_backtrack(ctx);
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		// Forward advising to `no_cycle` to update its incremental successor state.
		self.no_cycle_prop.advise_of_int_change(ctx, data, event)
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// Model-level propagation always runs all propagators.
		self.no_cycle_prop.initialize(ctx);
		self.scc_prop.initialize(ctx);
	}

	#[tracing::instrument(name = "circuit", target = "solver", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// Cheapest-first: stop as soon as an algorithm reports a conflict.
		self.no_cycle_prop.propagate(ctx)?;
		self.scc_prop.propagate(ctx)?;
		Ok(())
	}
}

impl<const SUBCIRCUIT: bool, I> CircuitGraph<SUBCIRCUIT, I> {
	/// The successor value that represents node `pos` pointing at node `to`.
	#[inline]
	pub(crate) fn edge_val(&self, to: usize) -> IntVal {
		self.offset + to as IntVal
	}

	/// Fill `out` with the successor position of every fixed node (`None` for
	/// unfixed), reusing `out`'s allocation (which always has one slot per
	/// node).
	pub(crate) fn fixed_successors<C>(&self, ctx: &C, out: &mut [Option<usize>])
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
	{
		debug_assert!(out.len() == self.vars.len());
		for (slot, var) in out.iter_mut().zip(&self.vars) {
			*slot = var.val(ctx).and_then(|v| self.val_to_pos(v));
		}
	}

	/// Whether node `k` is *forced into* the cycle: it cannot take itself as
	/// successor, so every solution must route the single cycle through `k`.
	#[inline]
	pub(crate) fn forced_in<C>(&self, ctx: &C, k: usize) -> bool
	where
		C: PropagationActions,
		I: IntInspectionActions<C>,
	{
		!self.vars[k].in_domain(ctx, self.edge_val(k))
	}

	/// Create a new successor graph.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal) -> Self {
		Self {
			n: vars.len(),
			vars,
			offset,
		}
	}

	/// Push the literal witnessing that node `i` is *forced into* the cycle
	/// (`x_i != edge_val(i)`): the reason-literal counterpart of
	/// [`Self::forced_in`].
	#[inline]
	pub(crate) fn push_forced_in<C>(&self, out: &mut Vec<C::Atom>, i: usize, ctx: &mut C)
	where
		C: ReasoningContext + ?Sized,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		out.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(self.edge_val(i))));
	}

	/// Append the `x_i != j` literals for every `i` in `from`, `j` in `to`
	/// (skipping `i == j` and the optional `except` pair).
	pub(crate) fn push_no_edge<C>(
		&self,
		out: &mut Vec<C::Atom>,
		from: &[usize],
		to: &[usize],
		except: Option<(usize, usize)>,
		ctx: &mut C,
	) where
		C: ReasoningContext + ?Sized,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		for &i in from {
			// Emit each bound literal at most once, so the clause stays duplicate-free.
			for &j in to {
				if i == j || except == Some((i, j)) {
					continue;
				}
				let val = self.edge_val(j);
				out.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(val)));
			}
		}
	}

	/// Append the successor positions of `node` (skipping a self-loop for
	/// `subcircuit`) to `out`.
	pub(crate) fn scc_successors<C>(&self, ctx: &C, node: usize, out: &mut Vec<usize>)
	where
		C: PropagationActions,
		I: IntInspectionActions<C>,
	{
		for val in self.vars[node].domain(ctx).iter().flatten() {
			if let Some(p) = self.val_to_pos(val) {
				if SUBCIRCUIT && p == node {
					continue;
				}
				out.push(p);
			}
		}
	}

	/// Translate a successor value `val` into a node position, if it refers to
	/// a node of this circuit.
	#[inline]
	pub(crate) fn val_to_pos(&self, val: IntVal) -> Option<usize> {
		if val >= self.offset && val < self.offset + self.vars.len() as IntVal {
			Some((val - self.offset) as usize)
		} else {
			None
		}
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		actions::IntDecisionActions,
		model::{Model, View},
		solver::{IntLitMeaning, Solver, Status, View as SolverView, branchers::WarmStartBrancher},
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

	// -----------------------------
	// Test cases for the `circuit` constraint
	// -----------------------------

	/// Simple 3-node circuit with two Hamiltonian cycles:
	/// Tests that the default propagator enumerates all correct solutions.
	#[test]
	#[traced_test]
	fn test_circuit_basic() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 1..=3);
		prb.circuit(vars.iter().copied()).post().unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
			2, 3, 1
			3, 1, 2"#]],
		);
	}

	/// Cross-config test: three different configurations must agree on
	/// the number of solutions for a 6-node circuit.  
	#[test]
	#[traced_test]
	fn test_circuit_configs_agree() {
		let configs = [(true, false), (true, true), (false, true)];
		let mut reference: Option<Vec<Vec<IntVal>>> = None;
		for (no_cycle, scc) in configs {
			let mut prb = Model::default();
			let vars = prb.new_int_decisions(6, 1..=6);
			prb.circuit(vars.iter().copied())
				.no_cycle_propagation(no_cycle)
				.scc_propagation(scc)
				.post()
				.unwrap();
			let solns = collect(prb, &vars);
			assert!(solns.iter().all(|s| is_circuit(s)));
			assert_eq!(solns.len(), 120); // (6-1)! = 120
			match &reference {
				None => reference = Some(solns),
				Some(r) => assert_eq!(r, &solns, "config no_cycle={no_cycle},scc={scc} disagrees"),
			}
		}
	}

	/// Regression test: a successor declared wider than the index set must be
	/// narrowed to the node range, so no out-of-range value can satisfy the
	/// circuit.
	#[test]
	#[traced_test]
	fn test_circuit_narrows_wide_successor_domain() {
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

	/// A disconnected graph (two size-3 groups that never point at each other)
	/// is unsatisfiable, and the model-level `scc` propagation connectivity
	/// rule sees it without search.
	#[test]
	#[traced_test]
	fn test_circuit_scc_disconnection() {
		for scc in [false, true] {
			let mut prb = Model::default();
			// Nodes 0,1,2 may only point within {0,1,2}; nodes 3,4,5 within {3,4,5}.
			let vars = [
				prb.new_int_decision(1..=3),
				prb.new_int_decision(1..=3),
				prb.new_int_decision(1..=3),
				prb.new_int_decision(4..=6),
				prb.new_int_decision(4..=6),
				prb.new_int_decision(4..=6),
			];
			let posted = prb
				.circuit(vars.iter().copied())
				.scc_propagation(scc)
				.post();
			assert!(
				posted.is_err(),
				"model-level scc must detect the disconnection (scc={scc})"
			);
		}
	}

	/// Regression test: a circuit over fewer than two nodes is a no-op.
	#[test]
	#[traced_test]
	fn test_circuit_trivial_sizes_are_no_ops() {
		let mut prb = Model::default();
		let empty = prb.new_int_decisions(0, 1..=1);
		prb.circuit(empty.iter().copied()).post().unwrap();
		// n = 1: the single in-range node keeps its domain; the circuit is vacuous.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(1, 1..=1);
		prb.circuit(vars.iter().copied()).post().unwrap();
		assert_eq!(collect(prb, &vars), vec![vec![1]]);
	}

	/// Regression test: a 2-cycle over 3 nodes is unsatisfiable.
	#[test]
	#[traced_test]
	fn test_circuit_unsat_subtour() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(2..=2); // node 0 -> node 1
		let b = prb.new_int_decision(1..=1); // node 1 -> node 0
		let c = prb.new_int_decision(1..=3);
		assert!(prb.circuit([a, b, c]).post().is_err());
	}

	/// Regression test: a 0-based array must yield both Hamiltonian cycles.
	#[test]
	#[traced_test]
	fn test_circuit_zero_based() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 0..=2);
		prb.circuit(vars.iter().copied()).offset(0).post().unwrap();
		let solns = collect(prb, &vars);
		// The two directed Hamiltonian cycles on {0,1,2}: 0->1->2->0 and 0->2->1->0.
		assert_eq!(solns, vec![vec![1, 2, 0], vec![2, 0, 1]]);
	}

	// -----------------------------
	// Test cases for the `subcircuit` constraint
	// -----------------------------

	/// Regression test: a 4-node subcircuit must enumerate all valid
	/// subcircuits.
	#[test]
	#[traced_test]
	fn test_subcircuit_all_solutions_valid() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, 1..=4);
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();
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

	/// Regression test: three different configurations must enumerate the same
	/// valid subcircuits on 6 nodes.
	#[test]
	#[traced_test]
	fn test_subcircuit_configs_agree() {
		let configs = [(true, false), (true, true), (false, true)];
		let mut reference: Option<Vec<Vec<IntVal>>> = None;
		for (no_cycle, scc) in configs {
			let mut prb = Model::default();
			let vars = prb.new_int_decisions(6, 1..=6);
			prb.circuit(vars.iter().copied())
				.subcircuit(true)
				.no_cycle_propagation(no_cycle)
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
					"subcircuit config no_cycle={no_cycle},scc={scc} disagrees"
				),
			}
		}
	}

	/// Regression test: a subcircuit with a 2-cycle and the other nodes
	/// self-looping must be enumerated, and not pruned by an unsound nogood.
	#[test]
	fn test_subcircuit_no_cycle_reason_current_level() {
		let mut prb = Model::default();
		let vars = vec![
			prb.new_int_decision(IntSet::from_iter([3..=3, 5..=6])), // node0
			prb.new_int_decision(IntSet::from_iter([1..=4])),        // node1
			prb.new_int_decision(IntSet::from_iter([6..=6])),        // node2
			prb.new_int_decision(IntSet::from_iter([1..=2, 4..=4, 6..=6])), // node3
			prb.new_int_decision(IntSet::from_iter([1..=1, 5..=5])), // node4
			prb.new_int_decision(IntSet::from_iter([3..=3, 5..=6])), // node5
		];
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.no_cycle_propagation(true)
			.scc_propagation(false)
			.post()
			.unwrap();
		for s in collect(prb, &vars) {
			assert!(is_subcircuit(&s), "emitted a non-subcircuit: {s:?}");
		}
	}

	/// Warm-start witness not over-pruned by the `no_cycle` propagator.
	#[test]
	fn test_subcircuit_no_cycle_under_fixed_search() {
		let mut prb = Model::default();
		let vars = [
			prb.new_int_decision(IntSet::from_iter([1..=2])), // node0: self(1) or ->1(2)
			prb.new_int_decision(IntSet::from_iter([1..=2])), // node1: ->0(1) or self(2)
			prb.new_int_decision(IntSet::from_iter([3..=4])), // node2: self(3) or ->3(4)
			prb.new_int_decision(IntSet::from_iter([3..=3])), // node3: ->2(3), forced selected
		];
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.no_cycle_propagation(true)
			.scc_propagation(false)
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

	/// Regression test: a subcircuit over fewer than two nodes is a no-op.
	#[test]
	#[traced_test]
	fn test_subcircuit_trivial_sizes_are_no_ops() {
		let mut prb = Model::default();
		let empty = prb.new_int_decisions(0, 1..=1);
		prb.circuit(empty.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();
		// n = 1: the single node keeps its (in-range) domain.
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(1, 1..=1);
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();
		assert_eq!(collect(prb, &vars), vec![vec![1]]);
	}

	/// Regression test: a 0-based subcircuit must enumerate all valid
	/// subcircuits.
	#[test]
	#[traced_test]
	fn test_subcircuit_zero_based() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 0..=2);
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
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
