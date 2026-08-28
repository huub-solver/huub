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
use tracing::warn;

pub use crate::constraints::circuit::{no_cycle::CircuitNoCycle, scc::CircuitScc};
use crate::{
	DeepClone, IntVal,
	actions::{
		IntAnalyzeActions, IntDecisionActions, IntEvent, IntInspectionActions,
		IntPropagationActions, PropagationActions, ReasonActions, ReasoningContext,
		ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, NO_REASON, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::IntLitMeaning,
};

/// Representation of the `circuit` / `subcircuit` constraint within a model.
///
/// Enforces that the successor variables form a single cycle through all nodes
/// (or, for `subcircuit`, through a subset, with the rest self-looping).
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
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
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub(crate) struct CircuitGraph<const SUBCIRCUIT: bool, I> {
	/// Successor variables, indexed by node position `0..n`.
	pub(crate) vars: Vec<I>,
	/// Successor value of node `0`.
	pub(crate) offset: IntVal,
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
		self.no_cycle.unwrap_or(true)
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
		// Tighten every successor to the node range (offset..=max_node). The
		// constraint itself implies the range, so the narrowing is unconditional.
		for v in &graph.vars {
			v.tighten_min(ctx, offset, NO_REASON)?;
			v.tighten_max(ctx, max_node, NO_REASON)?;
		}
		// Every node lies on the cycle, so none is its own successor.
		if !SUBCIRCUIT {
			for (i, v) in graph.vars.iter().enumerate() {
				let self_val = offset + i as IntVal;
				v.remove_val(ctx, self_val, NO_REASON)?;
			}
		}
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let scc = self.scc_propagation();
		let mut no_cycle = self.no_cycle_propagation();
		if !no_cycle && !scc {
			warn!(
				"all propagation algorithms are disabled for `circuit` constraint, override with no_cycle propagation to ensure consistency"
			);
			no_cycle = true;
		}
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
		Self { vars, offset }
	}

	/// Push the literal witnessing that node `i` is *forced into* the cycle
	/// (`x_i != edge_val(i)`): the reason-literal counterpart of
	/// [`Self::forced_in`].
	#[inline]
	pub(crate) fn push_forced_in<C, S>(&self, ctx: &mut C, out: &mut S, i: usize)
	where
		C: ReasoningContext + ?Sized,
		S: ReasonActions<C::Atom>,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		out.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(self.edge_val(i))));
	}

	/// Append the `x_i != j` literals for every `i` in `from`, `j` in `to`
	/// (skipping `i == j` and the optional `except` pair).
	///
	/// Callers pass disjoint `from`/`to` sets, so the appended literals are
	/// pairwise distinct and the resulting clause stays duplicate-free.
	pub(crate) fn push_no_edge<C, S>(
		&self,
		ctx: &mut C,
		out: &mut S,
		from: &[usize],
		to: &[usize],
		except: Option<(usize, usize)>,
	) where
		C: ReasoningContext + ?Sized,
		S: ReasonActions<C::Atom>,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		out.reserve(from.len() * to.len());
		for &i in from {
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
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		actions::IntDecisionActions,
		model::Model,
		solver::{IntLitMeaning, Solver, View as SolverView, branchers::WarmStartBrancher},
	};

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

	/// Regression test: a successor declared wider than the index set must be
	/// narrowed to the node range, so no out-of-range value can satisfy the
	/// circuit. Every successor below stays within the node range 2..=5.
	#[test]
	#[traced_test]
	fn test_circuit_narrows_wide_successor_domain() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, -100..=100);
		prb.circuit(vars.iter().copied()).offset(2).post().unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    3, 4, 5, 2
    3, 5, 2, 4
    4, 2, 5, 3
    4, 5, 3, 2
    5, 2, 3, 4
    5, 4, 2, 3"#]],
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
			let vars =
				[1..=3, 1..=3, 1..=3, 4..=6, 4..=6, 4..=6].map(|dom| prb.new_int_decision(dom));
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

	/// Sparse-domain `circuit`, `both` configuration. The three
	/// `test_circuit_sparse_*` tests use the same sparse instance and must pin
	/// identical solutions: sparse domains are where the propagators'
	/// witness-guarded rules fire, and a rule that removes a value still on a
	/// solution shows up as a missing line.
	#[test]
	#[traced_test]
	fn test_circuit_sparse_both() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(2..=3),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from_iter([1..=1, 4..=4]),
			IntSet::from(1..=3),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.no_cycle_propagation(true)
			.scc_propagation(true)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    2, 3, 4, 1
    2, 4, 1, 3
    3, 1, 4, 2"#]],
		);
	}

	/// Sparse-domain `circuit`, `no_cycle` configuration. The three
	/// `test_circuit_sparse_*` tests use the same sparse instance and must pin
	/// identical solutions: sparse domains are where the propagators'
	/// witness-guarded rules fire, and a rule that removes a value still on a
	/// solution shows up as a missing line.
	#[test]
	#[traced_test]
	fn test_circuit_sparse_no_cycle() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(2..=3),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from_iter([1..=1, 4..=4]),
			IntSet::from(1..=3),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.no_cycle_propagation(true)
			.scc_propagation(false)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    2, 3, 4, 1
    2, 4, 1, 3
    3, 1, 4, 2"#]],
		);
	}

	/// Sparse-domain `circuit`, `scc` configuration. The three
	/// `test_circuit_sparse_*` tests use the same sparse instance and must pin
	/// identical solutions: sparse domains are where the propagators'
	/// witness-guarded rules fire, and a rule that removes a value still on a
	/// solution shows up as a missing line.
	#[test]
	#[traced_test]
	fn test_circuit_sparse_scc() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(2..=3),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from_iter([1..=1, 4..=4]),
			IntSet::from(1..=3),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.no_cycle_propagation(false)
			.scc_propagation(true)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    2, 3, 4, 1
    2, 4, 1, 3
    3, 1, 4, 2"#]],
		);
	}

	/// Regression test: an empty circuit is vacuous, and a one-node circuit is
	/// satisfied only by the self-loop, even when the node's declared domain is
	/// wider than the single-node index range.
	#[test]
	#[traced_test]
	fn test_circuit_trivial_sizes() {
		let mut prb = Model::default();
		let empty = prb.new_int_decisions(0, 1..=1);
		prb.circuit(empty.iter().copied()).post().unwrap();

		let mut prb = Model::default();
		let vars = prb.new_int_decisions(1, 1..=5);
		prb.circuit(vars.iter().copied()).post().unwrap();
		prb.expect_solutions(&vars, expect!["1"]);

		// A lone node whose domain excludes the self-loop is unsatisfiable.
		let mut prb = Model::default();
		let x = prb.new_int_decision(2..=5);
		assert!(prb.circuit([x]).post().is_err());
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

	/// Regression test: a 0-based array must yield both directed Hamiltonian
	/// cycles on {0,1,2}: 0->1->2->0 and 0->2->1->0.
	#[test]
	#[traced_test]
	fn test_circuit_zero_based() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 0..=2);
		prb.circuit(vars.iter().copied()).offset(0).post().unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    1, 2, 0
    2, 0, 1"#]],
		);
	}

	// -----------------------------
	// Test cases for the `subcircuit` constraint
	// -----------------------------

	/// Regression test: a 4-node subcircuit must enumerate every subcircuit:
	/// the all-self-loop assignment, the full Hamiltonian cycles, and the
	/// shorter cycles with the remaining nodes self-looping. That is
	/// 1 + C(4,2) + C(4,3)*2! + 3! = 1 + 6 + 8 + 6 = 21 solutions.
	#[test]
	#[traced_test]
	fn test_subcircuit_enumerates_every_subcircuit() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(4, 1..=4);
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    1, 2, 3, 4
    1, 2, 4, 3
    1, 3, 2, 4
    1, 3, 4, 2
    1, 4, 2, 3
    1, 4, 3, 2
    2, 1, 3, 4
    2, 3, 1, 4
    2, 3, 4, 1
    2, 4, 1, 3
    2, 4, 3, 1
    3, 1, 2, 4
    3, 1, 4, 2
    3, 2, 1, 4
    3, 2, 4, 1
    3, 4, 2, 1
    4, 1, 2, 3
    4, 1, 3, 2
    4, 2, 1, 3
    4, 2, 3, 1
    4, 3, 1, 2"#]],
		);
	}

	/// Regression test: a warm start that fixes the `{0,1}` cycle must still
	/// leave the `{2,3}` cycle reachable; an unsound `no_cycle` nogood would
	/// prune that witness away.
	#[test]
	fn test_subcircuit_no_cycle_under_fixed_search() {
		let mut prb = Model::default();
		let vars = [
			1..=2, // node0: self(1) or ->1(2)
			1..=2, // node1: ->0(1) or self(2)
			3..=4, // node2: self(3) or ->3(4)
			3..=3, // node3: ->2(3), forced selected
		]
		.map(|dom| prb.new_int_decision(dom));
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
		slv.expect_solutions(&svars, expect!["1, 2, 4, 3"]);
	}

	/// Sparse-domain `subcircuit`, `both` configuration. The three
	/// `test_subcircuit_sparse_*` tests use the same sparse instance and must
	/// pin identical solutions. This also covers the 2-cycle-plus-self-loop
	/// shapes that an unsound `no_cycle` nogood would prune away.
	#[test]
	#[traced_test]
	fn test_subcircuit_sparse_both() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(1..=3),
			IntSet::from_iter([1..=2, 4..=4]),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from(2..=4),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.no_cycle_propagation(true)
			.scc_propagation(true)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    1, 2, 3, 4
    1, 2, 4, 3
    1, 4, 3, 2
    2, 1, 3, 4
    2, 4, 1, 3
    3, 1, 4, 2
    3, 2, 1, 4"#]],
		);
	}

	/// Sparse-domain `subcircuit`, `no_cycle` configuration. The three
	/// `test_subcircuit_sparse_*` tests use the same sparse instance and must
	/// pin identical solutions. This also covers the 2-cycle-plus-self-loop
	/// shapes that an unsound `no_cycle` nogood would prune away.
	#[test]
	#[traced_test]
	fn test_subcircuit_sparse_no_cycle() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(1..=3),
			IntSet::from_iter([1..=2, 4..=4]),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from(2..=4),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.no_cycle_propagation(true)
			.scc_propagation(false)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    1, 2, 3, 4
    1, 2, 4, 3
    1, 4, 3, 2
    2, 1, 3, 4
    2, 4, 1, 3
    3, 1, 4, 2
    3, 2, 1, 4"#]],
		);
	}

	/// Sparse-domain `subcircuit`, `scc` configuration. The three
	/// `test_subcircuit_sparse_*` tests use the same sparse instance and must
	/// pin identical solutions. This also covers the 2-cycle-plus-self-loop
	/// shapes that an unsound `no_cycle` nogood would prune away.
	#[test]
	#[traced_test]
	fn test_subcircuit_sparse_scc() {
		let mut prb = Model::default();
		let vars = [
			IntSet::from(1..=3),
			IntSet::from_iter([1..=2, 4..=4]),
			IntSet::from_iter([1..=1, 3..=4]),
			IntSet::from(2..=4),
		]
		.map(|dom| prb.new_int_decision(dom));
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.no_cycle_propagation(false)
			.scc_propagation(true)
			.post()
			.unwrap();
		prb.expect_solutions(
			&vars,
			expect![[r#"
    1, 2, 3, 4
    1, 2, 4, 3
    1, 4, 3, 2
    2, 1, 3, 4
    2, 4, 1, 3
    3, 1, 4, 2
    3, 2, 1, 4"#]],
		);
	}

	/// Regression test: an empty subcircuit is vacuous, and a one-node
	/// subcircuit is satisfied only by the self-loop (the node is either the
	/// whole cycle or excluded from it, and both mean `x = 1`).
	#[test]
	#[traced_test]
	fn test_subcircuit_trivial_sizes() {
		let mut prb = Model::default();
		let empty = prb.new_int_decisions(0, 1..=1);
		prb.circuit(empty.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();

		let mut prb = Model::default();
		let vars = prb.new_int_decisions(1, 1..=5);
		prb.circuit(vars.iter().copied())
			.subcircuit(true)
			.post()
			.unwrap();
		prb.expect_solutions(&vars, expect!["1"]);
	}

	/// Regression test: a 0-based subcircuit must enumerate all valid
	/// subcircuits: 1 (empty) + C(3,2) (2-cycles) + (3-1)! (3-cycles) = 6.
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
		prb.expect_solutions(
			&vars,
			expect![[r#"
    0, 1, 2
    0, 2, 1
    1, 0, 2
    1, 2, 0
    2, 0, 1
    2, 1, 0"#]],
		);
	}
}
