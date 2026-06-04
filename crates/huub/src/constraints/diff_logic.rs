//! Difference-logic constraint — model-side service and engine-side propagator.
//!
//! Holds the model-stage collection (edges, subsumption cache) consumed by
//! the auto-detection paths in [`Model::linear`], the simplification slices
//! (cycle detection, bound tightening, Johnson pruning, unification) run by
//! [`DiffLogicConstraint::process_round`] inside `Constraint::simplify`,
//! the engine-side runtime graph + Johnson potentials + trailed adjacency
//! lists, and the propagation runtime registered via
//! [`DiffLogicConstraint::to_solver`]. One file, one logical module.

use std::{cmp::Reverse, collections::BTreeMap, mem};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
	IntVal,
	actions::{
		BoolInspectionActions, BoolPropagationActions, IntDecisionActions, IntEvent,
		IntInspectionActions, IntPropagationActions, IntSimplificationActions, PropagationActions,
		ReasoningContext, Trailed, TrailingActions,
	},
	constraints::{
		Conflict, Reason,
		int_linear::{LinComparator, Reification},
	},
	helpers::{
		priority_queue::LazyPriorityQueue, trailed_list::TrailedList,
		trailed_open_list::TrailedOpenList,
	},
	model::{Model, View, expressions::bool_formula::BoolFormula},
	solver::{
		IntLitMeaning, decision::Decision, engine::State, solving_context::SolvingContext,
		trail::Trail, view::View as SolverView,
	},
};

/// One difference-logic edge in the engine graph.
///
/// Represents the constraint `int_vars[from] − int_vars[to] ≤ val`,
/// either globally (`bool_var = None`) or as an implication gated by
/// the Boolean stored at `bool_vars[bool_var.unwrap()]`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct DiffEdge {
	pub(crate) from: usize,
	pub(crate) to: usize,
	pub(crate) val: IntVal,
	pub(crate) bool_var: Option<usize>,
	/// Position of this edge in `bool_implications[bool_var]`. Meaningful
	/// only when `bool_var.is_some()`.
	pub(crate) bool_index: usize,
	/// Position of this edge in `open_out[from]`. Meaningful only when
	/// this edge is dormant (gated and not yet activated).
	pub(crate) out_index: usize,
	/// Position of this edge in `open_in[to]`. Mirror of `out_index`.
	pub(crate) in_index: usize,
}

/// Model-stage diff-logic edge collection.
///
/// Lives on [`Model`] for the duration of model construction. Auto-detection
/// in [`Model::linear`] (and any other constraint's `simplify` that routes a
/// two-term linear) appends edges into [`Self::pending_edges`] and looks up
/// reified Booleans in [`Self::diff_lit_map`].
///
/// At lowering time [`crate::lower::Lowerer::into_solver_internal`]
/// constructs a fresh [`DiffLogicConstraint`] from this collection, posts it
/// via [`Model::post_constraint`], and records the resulting [`ConRef`] in
/// [`Self::con_ref`] so subsequent auto-detection paths can enqueue the
/// constraint via [`Model::enqueue_diff_logic`].
#[derive(Clone, Debug, Default)]
pub(crate) struct DiffEdgeCollection {
	/// Mailbox of edges discovered by auto-detection. Drained by
	/// [`DiffLogicConstraint::simplify`] on every queue visit.
	pub(crate) pending_edges: Vec<ModelDiffEdge>,
	/// Reified-Boolean subsumption cache: `(x, y, d) → b` where
	/// `b ↔ (x − y ≤ d)`. Stored in BOTH directions:
	/// `(x, y, d) → b` and `(y, x, −d − 1) → !b`. Populated by
	/// [`Model::add_diff_logic_reified`].
	pub(crate) diff_lit_map: FxHashMap<(View<IntVal>, View<IntVal>), BTreeMap<IntVal, View<bool>>>,
	/// `ConRef` of the posted [`DiffLogicConstraint`]. Populated by
	/// [`crate::lower::Lowerer::into_solver_internal`] just before
	/// `model.propagate()`; `None` during model construction.
	pub(crate) con_ref: Option<crate::model::ConRef>,
}

/// Posted diff-logic constraint. Owns the authoritative graph at
/// propagation time and the subsumption-cache snapshot used by
/// [`Constraint::to_solver`] for the engine-side handoff.
#[derive(Clone, Debug, Default)]
pub(crate) struct DiffLogicConstraint {
	/// Authoritative edge set after the latest `simplify` pass.
	pub(crate) edges: Vec<ModelDiffEdge>,
	/// Unique endpoints across [`Self::edges`].
	pub(crate) endpoints: Vec<View<IntVal>>,
	/// Snapshot of [`DiffEdgeCollection::diff_lit_map`] taken inside
	/// `simplify`. Read by `to_solver` to seed the engine cache.
	pub(crate) diff_lit_map: FxHashMap<(View<IntVal>, View<IntVal>), BTreeMap<IntVal, View<bool>>>,
}

/// Auto-detection level for two-term difference constraints. Ordered
/// `Off < Basic < Equals < NotEquals` — each level routes a strict
/// superset of the patterns of the previous one, so the guards in
/// [`Model::try_route_diff_logic`] compare against the smallest
/// admissible variant with `>=`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Default)]
pub enum DiffLogicLevel {
	/// Disable diff-logic routing entirely.
	Off,
	/// Route Global / Implied / Reified (default).
	#[default]
	Basic,
	/// Also route ImpliedEquals.
	Equals,
	/// Also route ReifiedEquals / NotEquals / ImpliedNotEquals.
	NotEquals,
}

/// Engine-side difference-logic propagator.
///
/// Posted via [`DiffLogicConstraint::to_solver`](
/// crate::constraints::diff_logic::DiffLogicConstraint::to_solver) like
/// any other propagator. The owning [`PropRef`](
/// crate::solver::engine::prop_ref::PropRef) is recorded on
/// [`State::diff_lit_map.owner`](
/// crate::solver::engine::state::DiffLitMap) during
/// [`crate::constraints::Propagator::initialize`], so the mid-search
/// lazy-edge drain and the CLI setters can locate the propagator slot.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DiffLogicPropagator {
	// ---- Graph identity & lookup ----
	pub(crate) int_var_to_node: FxHashMap<SolverView<IntVal>, usize>,
	pub(crate) int_vars: Vec<SolverView<IntVal>>,
	pub(crate) bool_var_to_node: FxHashMap<SolverView<bool>, usize>,
	pub(crate) bool_vars: Vec<SolverView<bool>>,
	pub(crate) edges: Vec<DiffEdge>,

	// ---- Per-node active / dormant edge adjacency ----
	pub(crate) active_out: Vec<TrailedList<usize>>,
	pub(crate) active_in: Vec<TrailedList<usize>>,
	/// Per-node dormant outgoing implication edges (gate not yet fixed).
	pub(crate) open_out: Vec<TrailedOpenList<usize>>,
	/// Per-node dormant incoming implication edges.
	pub(crate) open_in: Vec<TrailedOpenList<usize>>,
	/// Per gating-Boolean list of implication edges. Indexed by
	/// `bool_vars` index.
	pub(crate) bool_implications: Vec<TrailedOpenList<usize>>,
	/// Total number of gated edges ever registered. **Not** trailed —
	/// a registered edge is a permanent logical fact (its gate just
	/// toggles), so this count must survive backtracking past a
	/// mid-search `register_edge`.
	pub(crate) num_gated_created: usize,
	/// Trailed counter for the number of gated edges currently closed
	/// (gate fixed). `None` until the first gated edge is registered.
	pub(crate) num_closed_edges: Option<Trailed<usize>>,

	// ---- Per-node algorithm working buffers (not trailed) ----
	/// Johnson potential per node. Computed once on the first call to
	/// [`Self::propagate`] via Bellman-Ford and not refreshed afterwards.
	pub(crate) pi: Vec<IntVal>,
	pub(crate) lower_bound: Vec<Option<IntVal>>,
	pub(crate) upper_bound: Vec<Option<IntVal>>,
	/// Predecessor on the current Dijkstra pass: `(prev_node,
	/// optional_bool_idx)`. The optional Boolean index identifies the
	/// gate of the in-edge if it was a gated implication that had been
	/// activated; used by reason construction to attribute the
	/// propagation back through the gate.
	pub(crate) backtrace: Vec<Option<(usize, Option<usize>)>>,
	pub(crate) visited: Vec<bool>,

	// ---- Propagation transient scratch (not trailed; cleared each call) ----
	pub(crate) visited_updates: Vec<usize>,
	pub(crate) lower_bound_changes: FxHashSet<usize>,
	pub(crate) upper_bound_changes: FxHashSet<usize>,
	pub(crate) lb_updates: Vec<usize>,
	pub(crate) ub_updates: Vec<usize>,
	/// Set of gating Boolean indices reported by `advise_of_bool_change`
	/// as fixed since the last `propagate`.
	pub(crate) fixed_bools: FxHashSet<usize>,

	// ---- Engine integration ----
	/// Whether the Bellman-Ford potential initialization has run.
	pub(crate) pi_initialized: bool,
	/// Edges supplied by
	/// [`crate::constraints::diff_logic::DiffLogicConstraint::to_solver`]
	/// but not yet installed: at `to_solver` time the
	/// [`crate::lower::LoweringContext`] doesn't expose the [`Trail`] needed
	/// by [`Self::register_edge`], so we stash the resolved solver views here
	/// and drain them in [`crate::constraints::Propagator::initialize`].
	pub(crate) pending_install: Vec<(
		SolverView<IntVal>,
		SolverView<IntVal>,
		IntVal,
		Option<SolverView<bool>>,
	)>,
	/// Mode for reasons attached to Booleans set false by the service:
	/// `0` deferred via [`crate::actions::PropagationActions::deferred_reason`]
	/// (lifted thresholds resolved via `lit_relaxed` in [`Self::explain`]),
	/// `1` lifted via eager `.lit()` (legacy — walks `OrderStorage::Lazy`),
	/// `2` eager full reasons using `min_lit` / `max_lit`. Default `0`.
	pub(crate) bool_reasons: u8,
	/// Whether the booleans phase should run `inc_imp` (proactive check
	/// of open implication edges after each edge activation). Defaults
	/// to `true`.
	pub(crate) use_inc_imp: bool,
}

/// Difference-logic constraint variant — transient form, used during
/// expansion only. The model-side service does not persist these; they
/// are walked into [`ModelDiffEdge`]s at construction time.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DifferenceLogicConstraint {
	/// `x − y ≤ d` (always active).
	Global(View<IntVal>, View<IntVal>, IntVal),
	/// `b → (x − y ≤ d)`.
	Implied(View<bool>, View<IntVal>, View<IntVal>, IntVal),
	/// `b ↔ (x − y ≤ d)`.
	Reified(View<bool>, View<IntVal>, View<IntVal>, IntVal),
	/// `b → (x − y = d)`.
	ImpliedEquals(View<bool>, View<IntVal>, View<IntVal>, IntVal),
	/// `b ↔ (x − y = d)`.
	ReifiedEquals(View<bool>, View<IntVal>, View<IntVal>, IntVal),
	/// `x − y ≠ d` (always active).
	NotEquals(View<IntVal>, View<IntVal>, IntVal),
	/// `b → (x − y ≠ d)`.
	ImpliedNotEquals(View<bool>, View<IntVal>, View<IntVal>, IntVal),
}

/// One difference-logic edge `x − y ≤ d` in the model graph.
///
/// `gate == None` is a globally-active edge; `gate == Some(b)` is the
/// implication `b → (x − y ≤ d)`. Reified variants are split into two
/// edges at expansion time — the positive direction gated by `b` and
/// the negative direction gated by `!b`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ModelDiffEdge {
	pub(crate) x: View<IntVal>,
	pub(crate) y: View<IntVal>,
	pub(crate) d: IntVal,
	pub(crate) gate: Option<View<bool>>,
}

impl DiffLogicConstraint {
	/// Whether the constraint currently owns any edges.
	#[expect(
		dead_code,
		reason = "complete constraint accessor; not yet read by the minimal integration"
	)]
	pub(crate) fn is_empty(&self) -> bool {
		self.edges.is_empty()
	}
}

// =====================================================================
// Re-runnable slices + process_round (M.3).
//
// The slices live as free functions so they can borrow `&[ModelDiffEdge]`
// while the caller holds `&mut Model` for tightening / unification.
// The `Model::diff_logic_process_round` orchestrator takes ownership of
// `diff_logic.edges` for the duration of a round so the slice helpers
// can have a stable view of the edge set even when slice 2's
// `tighten_min`/`tighten_max` fires advisors that may push fresh
// constraints into `diff_logic.pending_edges` mid-round.
// =====================================================================

impl DiffLogicConstraint {
	/// Intern endpoints of [`Self::edges`] into stable node indices.
	fn intern_endpoints(&self) -> (FxHashMap<View<IntVal>, usize>, usize) {
		let mut node_of: FxHashMap<View<IntVal>, usize> = FxHashMap::default();
		let mut n = 0usize;
		for e in &self.edges {
			for endpoint in [e.x, e.y] {
				if let std::collections::hash_map::Entry::Vacant(entry) = node_of.entry(endpoint) {
					let _ = entry.insert(n);
					n += 1;
				}
			}
		}
		(node_of, n)
	}

	/// Johnson's all-pairs shortest paths over the gateless subgraph of
	/// [`Self::edges`], reweighted by `pi`. Returns the `n×n` matrix
	/// where `dist[u][v]` is the shortest-path distance, or
	/// [`IntVal::MAX`] if unreachable.
	fn johnson_all_pairs(
		&self,
		active_out: &[Vec<usize>],
		pi: &[IntVal],
		node_of: &FxHashMap<View<IntVal>, usize>,
		n: usize,
	) -> Vec<Vec<IntVal>> {
		let mut dist: Vec<Vec<IntVal>> = vec![vec![IntVal::MAX; n]; n];
		for src in 0..n {
			let mut dist_src: Vec<IntVal> = vec![IntVal::MAX; n];
			dist_src[src] = 0;
			let mut queue: LazyPriorityQueue<usize, Reverse<IntVal>> = LazyPriorityQueue::new();
			let _ = queue.push(src, Reverse(0));
			while let Some((u, Reverse(d_u))) = queue.pop() {
				if d_u > dist_src[u] {
					continue;
				}
				for &e_idx in &active_out[u] {
					let edge = &self.edges[e_idx];
					let v = node_of[&edge.y];
					let reduced_w = pi[u].saturating_add(edge.d).saturating_sub(pi[v]);
					let alt = d_u.saturating_add(reduced_w);
					if alt < dist_src[v] {
						dist_src[v] = alt;
						let _ = queue.push_increase(v, Reverse(alt));
					}
				}
			}
			for dst in 0..n {
				if dist_src[dst] != IntVal::MAX {
					dist[src][dst] = dist_src[dst]
						.saturating_add(pi[dst])
						.saturating_sub(pi[src]);
				}
			}
		}
		dist
	}

	/// Run one round of model-side diff-logic reasoning.
	///
	/// Drains [`Model::diff_edges::pending_edges`] into [`Self::edges`],
	/// refreshes endpoint and gate aliases, then runs slices 1–4 in
	/// order. Returns `Ok(true)` if anything changed.
	pub(crate) fn process_round(
		&mut self,
		model: &mut Model,
	) -> Result<bool, Conflict<View<bool>>> {
		let mut any_change = false;

		// Drain pending-edge mailbox from the collection into self.edges.
		if !model.diff_edges.pending_edges.is_empty() {
			let mut pending = mem::take(&mut model.diff_edges.pending_edges);
			self.edges.append(&mut pending);
			any_change = true;
		}
		if self.edges.is_empty() {
			return Ok(any_change);
		}

		self.refresh_endpoint_aliases(model);
		let _ = self.refresh_gate_aliases(model);

		self.slice1_cycle_detection()?;
		let tightened = self.slice2_bound_tightening(model)?;
		let slice3_changed = self.slice3_johnson_pruning(model)?;
		self.slice4_unify(model)?;
		self.recompute_endpoints();

		// Sync `diff_lit_map` snapshot so `to_solver` translates the
		// subsumption cache as it stood at end-of-round.
		self.diff_lit_map = model.diff_edges.diff_lit_map.clone();
		Ok(any_change || tightened || slice3_changed)
	}

	/// Rebuild the unique-endpoint list from the current edge set.
	fn recompute_endpoints(&mut self) {
		let mut seen: FxHashMap<View<IntVal>, ()> = FxHashMap::default();
		let mut endpoints = Vec::new();
		for e in &self.edges {
			for ep in [e.x, e.y] {
				if seen.insert(ep, ()).is_none() {
					endpoints.push(ep);
				}
			}
		}
		self.endpoints = endpoints;
	}

	/// Resolve any aliases on edge endpoints. Idempotent.
	fn refresh_endpoint_aliases(&mut self, model: &mut Model) {
		for i in 0..self.edges.len() {
			let edge = self.edges[i];
			let x = edge.x.resolve_alias(model).0;
			let y = edge.y.resolve_alias(model).0;
			self.edges[i].x = x;
			self.edges[i].y = y;
		}
	}

	/// Resolve any aliases on edge gates and normalize the edge set.
	/// See the original `Model::diff_logic_refresh_gate_aliases` doc
	/// for the case-by-case behaviour. Returns `(promoted, dropped)`.
	fn refresh_gate_aliases(&mut self, model: &mut Model) -> (usize, usize) {
		use crate::model::view::boolean::BoolView;
		let mut promoted = 0;
		let mut dropped = 0;
		let mut i = 0;
		while i < self.edges.len() {
			let edge = self.edges[i];
			let Some(gate) = edge.gate else {
				i += 1;
				continue;
			};
			let resolved = gate.resolve_alias(model).0;
			match resolved.0 {
				BoolView::Const(true) => {
					self.edges[i].gate = None;
					promoted += 1;
					i += 1;
				}
				BoolView::Const(false) => {
					let _ = self.edges.swap_remove(i);
					dropped += 1;
				}
				_ => {
					self.edges[i].gate = Some(resolved);
					i += 1;
				}
			}
		}
		(promoted, dropped)
	}

	/// Slice 1 — Bellman-Ford cycle detection on the globally-active
	/// subgraph. Returns `Conflict` if a negative cycle exists among
	/// the gateless edges. Gated edges are excluded.
	fn slice1_cycle_detection(&self) -> Result<(), Conflict<View<bool>>> {
		let (node_of, n) = self.intern_endpoints();
		let active: Vec<&ModelDiffEdge> = self.edges.iter().filter(|e| e.gate.is_none()).collect();

		let mut pi: Vec<IntVal> = vec![0; n];
		let mut changed = true;
		for _ in 0..n {
			changed = false;
			for edge in &active {
				let from = node_of[&edge.x];
				let to = node_of[&edge.y];
				let cand = pi[from].saturating_add(edge.d);
				if cand < pi[to] {
					pi[to] = cand;
					changed = true;
				}
			}
			if !changed {
				break;
			}
		}
		if changed {
			for edge in &active {
				let from = node_of[&edge.x];
				let to = node_of[&edge.y];
				if pi[from].saturating_add(edge.d) < pi[to] {
					return Err(Conflict {
						subject: None,
						reason: Reason::Eager(Vec::new().into_boxed_slice()),
					});
				}
			}
		}
		Ok(())
	}

	/// Slice 2 — bound tightening via Bellman-Ford fixed-point.
	///
	/// Tightens model int-var domains based on graph-implied bounds.
	/// An edge `x − y ≤ d` enforces `x ≤ y.max + d` and `y ≥ x.min − d`.
	/// Participates in tightening if `gate == None` or the gate Boolean
	/// is fixed true. Returns `Ok(true)` if any bound was tightened.
	fn slice2_bound_tightening(&self, model: &mut Model) -> Result<bool, Conflict<View<bool>>> {
		let participating: Vec<usize> = self
			.edges
			.iter()
			.enumerate()
			.filter(|(_, e)| match e.gate {
				None => true,
				Some(g) => matches!(g.val(model), Some(true)),
			})
			.map(|(i, _)| i)
			.collect();
		if participating.is_empty() {
			return Ok(false);
		}

		let mut endpoint_seen: FxHashMap<View<IntVal>, ()> = FxHashMap::default();
		for &idx in &participating {
			let _ = endpoint_seen.insert(self.edges[idx].x, ());
			let _ = endpoint_seen.insert(self.edges[idx].y, ());
		}
		let n = endpoint_seen.len();

		let mut any_tightened = false;
		for _ in 0..n {
			let mut changed = false;
			for &idx in &participating {
				let edge = self.edges[idx];
				let y_max = edge.y.max(model);
				let new_x_max = y_max.saturating_add(edge.d);
				if new_x_max < edge.x.max(model) {
					edge.x
						.tighten_max(model, new_x_max, Vec::<View<bool>>::new())?;
					changed = true;
					any_tightened = true;
				}
				let x_min = edge.x.min(model);
				let new_y_min = x_min.saturating_sub(edge.d);
				if new_y_min > edge.y.min(model) {
					edge.y
						.tighten_min(model, new_y_min, Vec::<View<bool>>::new())?;
					changed = true;
					any_tightened = true;
				}
			}
			if !changed {
				break;
			}
		}
		Ok(any_tightened)
	}

	/// Slice 3 — Johnson's all-pairs shortest paths + redundant edge pruning.
	///
	/// In addition to pruning redundant edges, fixes every implied edge's
	/// gate Boolean whose activation would form a negative cycle through
	/// the active graph. The gate `g` is fixed to `false` via
	/// `g.fix(model, false, [])` — and because `View<bool>` carries the
	/// negation flag, the same call covers BOTH polarities of a Reified
	/// pair `b ↔ (x − y ≤ d)`:
	///
	/// - When the *forward* edge (gate `b`, weight `d`) hits the negative-cycle
	///   condition, `b.fix(model, false, [])` makes `b` constant false.
	/// - When the *reverse* edge (gate `!b`, weight `−d − 1`) hits the
	///   negative-cycle condition, `(!b).fix(model, false, [])` makes `b`
	///   constant **true**.
	///
	/// Without this step the gate Boolean would remain free in the SAT
	/// pool — possibly unsound on a satisfaction problem, and definitely
	/// wasteful on the branching heuristic's decision budget. Lucas's
	/// engine-side propagator does the equivalent at search-time
	/// ([crates/huub/src/constraints/difference_logic.rs:619-623] in
	/// lucas's `feat/difference_logic_benchmark`); we do it at model
	/// simplification time.
	/// Slice 3 — Johnson's all-pairs shortest paths + redundant edge
	/// pruning + gate fixing.
	///
	/// In addition to dropping redundant edges from [`Self::edges`],
	/// fixes any implied edge's gate Boolean whose activation would form
	/// a negative cycle through the active graph. The gate `g` is fixed
	/// to `false` via `g.fix(model, false, [])` — and because `View<bool>`
	/// carries the negation flag, the same call covers both polarities of
	/// a Reified pair `b ↔ (x − y ≤ d)`. Returns `Ok(true)` if any gate
	/// was fixed.
	fn slice3_johnson_pruning(&mut self, model: &mut Model) -> Result<bool, Conflict<View<bool>>> {
		let (node_of, n) = self.intern_endpoints();
		if n == 0 {
			return Ok(false);
		}

		let mut active_out: Vec<Vec<usize>> = vec![Vec::new(); n];
		for (idx, edge) in self.edges.iter().enumerate() {
			if edge.gate.is_some() {
				continue;
			}
			let from = node_of[&edge.x];
			active_out[from].push(idx);
		}

		let mut pi: Vec<IntVal> = vec![0; n];
		let mut changed = true;
		for _ in 0..n {
			changed = false;
			for adj in &active_out {
				for &e_idx in adj {
					let edge = &self.edges[e_idx];
					let from = node_of[&edge.x];
					let to = node_of[&edge.y];
					let cand = pi[from].saturating_add(edge.d);
					if cand < pi[to] {
						pi[to] = cand;
						changed = true;
					}
				}
			}
			if !changed {
				break;
			}
		}
		if changed {
			// Negative cycle — slice 1 should have caught this.
			return Ok(false);
		}

		let dist = self.johnson_all_pairs(&active_out, &pi, &node_of, n);

		// Two-pass mutation: first compute keep/fix decisions reading
		// `self.edges` immutably (while we hand `model` to `gate.fix`),
		// then prune `self.edges` once via `retain`.
		let mut keep = vec![true; self.edges.len()];
		let mut fixed_gates: FxHashSet<View<bool>> = FxHashSet::default();
		for (i, edge) in self.edges.iter().enumerate() {
			let from = node_of[&edge.x];
			let to = node_of[&edge.y];
			keep[i] = match edge.gate {
				None => dist[from][to] >= edge.d,
				Some(gate) => {
					if dist[to][from] != IntVal::MAX && dist[to][from] < -edge.d {
						if fixed_gates.insert(gate) {
							gate.fix(model, false, Vec::<View<bool>>::new())?;
						}
						false
					} else {
						!(dist[from][to] != IntVal::MAX && dist[from][to] <= edge.d)
					}
				}
			};
		}
		let mut idx = 0;
		self.edges.retain(|_| {
			let k = keep[idx];
			idx += 1;
			k
		});
		Ok(!fixed_gates.is_empty())
	}

	/// Slice 4 — equality-cycle unification.
	///
	/// For every pair `(u, v)` with `dist[u][v] + dist[v][u] == 0`,
	/// calls `u.unify(model, v + dist[u][v])` to collapse them onto a
	/// single representative. Does not mutate [`Self::edges`].
	fn slice4_unify(&self, model: &mut Model) -> Result<(), Conflict<View<bool>>> {
		let (node_of, n) = self.intern_endpoints();
		if n < 2 {
			return Ok(());
		}

		let mut active_out: Vec<Vec<usize>> = vec![Vec::new(); n];
		for (idx, edge) in self.edges.iter().enumerate() {
			if edge.gate.is_some() {
				continue;
			}
			let from = node_of[&edge.x];
			active_out[from].push(idx);
		}

		let mut pi: Vec<IntVal> = vec![0; n];
		let mut changed = true;
		for _ in 0..n {
			changed = false;
			for adj in &active_out {
				for &e_idx in adj {
					let edge = &self.edges[e_idx];
					let from = node_of[&edge.x];
					let to = node_of[&edge.y];
					let cand = pi[from].saturating_add(edge.d);
					if cand < pi[to] {
						pi[to] = cand;
						changed = true;
					}
				}
			}
			if !changed {
				break;
			}
		}
		if changed {
			// Negative cycle (slice 1 should have caught it). Skip
			// unification — would otherwise build a bogus distance matrix.
			return Ok(());
		}

		let dist = self.johnson_all_pairs(&active_out, &pi, &node_of, n);

		let int_vars: Vec<View<IntVal>> = {
			let mut tmp = vec![View(crate::model::view::integer::IntView::Const(0)); n];
			for (&v, &idx) in &node_of {
				tmp[idx] = v;
			}
			tmp
		};

		for u in 0..n {
			for v in (u + 1)..n {
				if dist[u][v] == IntVal::MAX || dist[v][u] == IntVal::MAX {
					continue;
				}
				if dist[u][v].saturating_add(dist[v][u]) != 0 {
					continue;
				}
				let offset = dist[u][v];
				int_vars[u].unify(model, int_vars[v] + offset)?;
			}
		}
		Ok(())
	}
}

impl crate::constraints::Constraint<Model> for DiffLogicConstraint {
	fn simplify(
		&mut self,
		ctx: &mut <Model as crate::actions::ReasoningEngine>::PropagationContext<'_>,
	) -> Result<
		crate::constraints::SimplificationStatus,
		<Model as crate::actions::ReasoningEngine>::Conflict,
	> {
		// Drive the diff-logic round through the regular constraint
		// pipeline: drain the model's `diff_edges` mailbox, run slices,
		// and snapshot the subsumption cache for `to_solver`. The
		// constraint's `self.edges`/`self.diff_lit_map` carry the
		// post-round state directly — no out-of-band re-sync needed.
		let _ = self.process_round(ctx)?;
		Ok(crate::constraints::SimplificationStatus::NoFixpoint)
	}

	fn to_solver(
		&self,
		slv: &mut crate::lower::LoweringContext<'_>,
	) -> Result<(), crate::lower::LoweringError> {
		use crate::actions::PostingActions;

		// Translate every edge through the lowering map; stash on the
		// propagator's `pending_install`, to be drained in
		// `Propagator::initialize` once the engine trail is available.
		let mut prop = DiffLogicPropagator::default();
		for edge in &self.edges {
			let xv = slv.solver_view(edge.x);
			let yv = slv.solver_view(edge.y);
			let gate = edge.gate.map(|g| slv.solver_view(g));
			prop.pending_install.push((xv, yv, edge.d, gate));
		}

		// Translate the model-side `diff_lit_map` into the engine
		// `diff_lit_cache` so mid-search lazy mints honour subsumptions
		// found at simplification time. Bidirectional like the model
		// cache: `(x, y, d) → b` and `(y, x, −d − 1) → !b` are stored
		// separately, so the translation is a straight per-entry map.
		use crate::solver::view::View as SolverView;
		let mut cache_entries: Vec<(
			SolverView<IntVal>,
			SolverView<IntVal>,
			IntVal,
			SolverView<bool>,
		)> = Vec::new();
		for ((mx, my), inner) in &self.diff_lit_map {
			let xv = slv.solver_view(*mx);
			let yv = slv.solver_view(*my);
			for (d, b) in inner {
				let bv = slv.solver_view(*b);
				cache_entries.push((xv, yv, *d, bv));
			}
		}

		// Post the propagator. `LoweringActions::add_propagator` drives
		// `Propagator::initialize`, which drains `pending_install` into
		// the actual graph and subscribes the bounds / fixed advisors.
		// `initialize` also records the owning `PropRef` on
		// `state.diff_lit_map.owner` — we use that owner pointer next
		// when populating the engine cache so the cache lookups happen
		// against the same propagator's subsumption decisions.
		slv.add_propagator(Box::new(prop));

		// Seed the engine `diff_lit_cache` directly on state. The
		// initialize hook above has already set `owner`, but the cache
		// itself lives on `state.diff_lit_map`, not on the propagator.
		// We do this via a helper on `LoweringContext` so we don't
		// expose the engine internals through `LoweringActions`.
		for (xv, yv, d, b) in cache_entries {
			slv.populate_diff_lit_cache(xv, yv, d, b);
		}

		Ok(())
	}
}

// =====================================================================
// Phase-4 trait impls. `Constraint::to_solver` constructs a
// `DiffLogicPropagator` from the surviving edges and the subsumption
// cache, then registers it via `LoweringActions::add_propagator`. The
// engine-side propagator owns the trail-aware graph from then on.
//
// `DiffLogicConstraint` is owned by `Model::diff_logic` as a unique
// field. It is NOT placed in `Model::constraints`; the `simplify`
// method here is invoked manually by the model fix-point (see
// `Model::propagate`). The trait impl is provided so subsequent phases
// can flip the call site over without breaking the existing engine
// service hookup.
// =====================================================================

impl crate::constraints::Propagator<Model> for DiffLogicConstraint {
	fn initialize(
		&mut self,
		ctx: &mut <Model as crate::actions::ReasoningEngine>::InitializationContext<'_>,
	) {
		// Always enqueue at post-time. The first `simplify` drains
		// the `Model::diff_edges` mailbox into `self.edges`; if both
		// are empty `process_round` bails out cheaply.
		use crate::actions::InitActions;
		ctx.enqueue_now(true);
	}

	fn propagate(
		&mut self,
		_ctx: &mut <Model as crate::actions::ReasoningEngine>::PropagationContext<'_>,
	) -> Result<(), <Model as crate::actions::ReasoningEngine>::Conflict> {
		// `Constraint::simplify` runs all the work via `process_round`;
		// `propagate` is never reached because `simplify` always
		// returns `NoFixpoint` and the model loop re-enters `simplify`.
		Ok(())
	}
}

impl std::fmt::Display for DiffLogicLevel {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.write_str(match self {
			Self::Off => "off",
			Self::Basic => "basic",
			Self::Equals => "equals",
			Self::NotEquals => "not-equals",
		})
	}
}

impl std::str::FromStr for DiffLogicLevel {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s {
			"0" | "off" => Ok(Self::Off),
			"1" | "basic" => Ok(Self::Basic),
			"2" | "equals" => Ok(Self::Equals),
			"3" | "not-equals" | "not_equals" => Ok(Self::NotEquals),
			_ => Err(format!(
				"unknown diff-logic level `{s}` (expected 0/off, 1/basic, 2/equals, 3/not-equals)"
			)),
		}
	}
}

impl DiffLogicPropagator {
	// ---- Bounds-phase deferred-reason encoding ----
	//
	// Bounds-phase propagations register a *lazy* reason. The reason is
	// rebuilt at explain-time (after `goto_assign_lit`) when the SAT trail
	// has caught up to the moment of propagation — at which point the
	// strongest currently-true antecedent literal on the source variable
	// is available via `lit_relaxed`.
	//
	/// Used by the booleans phase to discriminate between bounds-phase
	/// and booleans-phase encodings in the shared lazy-reason path.
	/// Bounds-phase reasons are eager (built at propagation time below)
	/// and never carry this tag.
	#[expect(
		dead_code,
		reason = "booleans-phase reason tag consumed once the diff-logic brancher/reservoir are reintroduced"
	)]
	pub(crate) const BOUNDS_TAG: u64 = 1 << 63;

	// ---- Gated edge activation / closure ----

	/// Move a gated edge from the dormant lists into the active adjacency.
	fn activate_imp_edge(&mut self, ctx: &mut SolvingContext<'_>, index: usize) {
		let edge = &self.edges[index];
		let from = edge.from;
		let to = edge.to;
		self.active_out[from].push(ctx, index);
		self.active_in[to].push(ctx, index);
	}

	/// Mark a gating Boolean as fixed since the last `propagate_booleans`.
	pub(crate) fn advise_bool_fixed(&mut self, data: usize) -> bool {
		self.fixed_bools.insert(data)
	}

	pub(crate) fn advise_int_change(&mut self, ctx: &State, data: usize, event: IntEvent) -> bool {
		let mut enqueue = false;
		if event == IntEvent::LowerBound || event == IntEvent::Fixed {
			enqueue = self.notify_lb_change(ctx, data);
		}
		if event == IntEvent::UpperBound || event == IntEvent::Fixed {
			enqueue |= self.notify_ub_change(ctx, data);
		}
		enqueue
	}

	/// One Bellman-Ford pass to populate the initial Johnson potentials.
	/// Returns a conflict if a negative cycle is reachable.
	fn bellman_ford_init_pi(
		&mut self,
		ctx: &mut SolvingContext<'_>,
	) -> Result<(), Conflict<Decision<bool>>> {
		let num_nodes = self.int_vars.len();
		if self.pi.len() < num_nodes {
			self.pi.resize(num_nodes, 0);
		}
		if self.lower_bound.len() < num_nodes {
			self.lower_bound.resize(num_nodes, None);
			self.upper_bound.resize(num_nodes, None);
			self.backtrace.resize(num_nodes, None);
			self.visited.resize(num_nodes, false);
		}
		let mut changed = true;
		for _ in 0..num_nodes {
			changed = false;
			for n in 0..num_nodes {
				for &e in self.active_out[n].iter(ctx) {
					let edge = &self.edges[e];
					if self.pi[edge.from] + edge.val < self.pi[edge.to] {
						self.pi[edge.to] = self.pi[edge.from] + edge.val;
						changed = true;
					}
				}
			}
			if !changed {
				break;
			}
		}
		if changed {
			for n in 0..num_nodes {
				for &e in self.active_out[n].iter(ctx) {
					let edge = &self.edges[e];
					if self.pi[edge.from] + edge.val < self.pi[edge.to] {
						return Err(ctx.declare_conflict(Vec::<SolverView<bool>>::new()));
					}
				}
			}
		}
		Ok(())
	}

	/// Close a gated edge: remove it from the dormant lists and decrement
	/// the open-edge counter. Called when the gate is fixed (either true
	/// after activation, or false).
	fn close_imp_edge<A: TrailingActions>(&mut self, ctx: &mut A, e: usize) {
		let edge = &self.edges[e];
		let b = edge.bool_var.unwrap();
		let to = edge.to;
		let from = edge.from;
		let bool_index = edge.bool_index;
		let out_index = edge.out_index;
		let in_index = edge.in_index;
		let edges = &mut self.edges;
		let was_open = self.bool_implications[b]
			.close(ctx, bool_index, |&e, i| edges[e].bool_index = i)
			& self.open_out[from].close(ctx, out_index, |&e, i| edges[e].out_index = i)
			& self.open_in[to].close(ctx, in_index, |&e, i| edges[e].in_index = i);
		debug_assert!(was_open);
		let cnt = self.num_closed_edges.unwrap();
		let cur = ctx.trailed(cnt);
		let _ = ctx.set_trailed(cnt, cur + 1);
	}

	// ---- Dijkstra over relevant nodes for `inc_imp` ----

	fn dijkstra_relevant(
		&mut self,
		ctx: &SolvingContext<'_>,
		new_edge: usize,
		reverse: bool,
	) -> FxHashMap<usize, IntVal> {
		self.reset_visit();
		let new_edge = self.edges[new_edge];
		let origin = if reverse { new_edge.to } else { new_edge.from };
		let relevant_target = if reverse { new_edge.from } else { new_edge.to };
		let mut distances: FxHashMap<usize, IntVal> = FxHashMap::default();
		let _ = distances.insert(relevant_target, new_edge.val);
		let mut queue = LazyPriorityQueue::new();
		let _ = queue.push(origin, Reverse((0, false)));
		let _ = queue.push(
			relevant_target,
			Reverse((
				new_edge.val
					+ if reverse {
						self.pi[relevant_target] - self.pi[origin]
					} else {
						self.pi[origin] - self.pi[relevant_target]
					},
				true,
			)),
		);
		let mut relevant_count = 1;
		while !queue.is_empty() && relevant_count > 0 {
			let (s, Reverse((dist, relevant))) = queue.pop().unwrap();
			self.visit(s);
			let it = if reverse {
				self.active_in[s].iter(ctx)
			} else {
				self.active_out[s].iter(ctx)
			};
			for &e in it {
				let edge = &self.edges[e];
				let target = if reverse { edge.from } else { edge.to };
				let new_dist = dist
					+ edge.val + if reverse {
					self.pi[target] - self.pi[s]
				} else {
					self.pi[s] - self.pi[target]
				};
				if !self.visited[target] {
					let new_relevant = relevant || (s == origin && target == relevant_target);
					let new_prio = Reverse((new_dist, new_relevant));
					let prev = queue.push_increase(target, new_prio);
					if prev != Some(new_prio) {
						if new_relevant {
							if distances
								.insert(
									target,
									new_dist
										+ if reverse {
											self.pi[origin] - self.pi[target]
										} else {
											self.pi[target] - self.pi[origin]
										},
								)
								.is_none()
							{
								relevant_count += 1;
							}
						} else if distances.remove(&target).is_some() {
							relevant_count -= 1;
						}
					}
				}
			}
			if relevant {
				relevant_count -= 1;
			}
		}
		distances
	}

	/// Lazy-explain hook routed by the engine when a `set_bool_false`
	/// emitted a `Reason::Lazy` (`bool_reasons == 0`). Decodes
	/// `(edge, lb_fixed)` from `data` and rebuilds the lifted
	/// threshold reasons using `lit_relaxed`, coordinating the two
	/// sides so the produced pair forms a valid edge-violation
	/// witness even when the requested literal was relaxed. Mirrors
	/// the algorithm in the lucas branch's
	/// `DifferenceLogicBooleans::explain`.
	pub(crate) fn explain(
		&self,
		state: &State,
		_lit: SolverView<bool>,
		data: u64,
	) -> Vec<SolverView<bool>> {
		use std::cmp::{max, min};

		use crate::actions::IntExplanationActions;

		// Data layout (matches set_bool_false at diff_logic.rs:561):
		//   bits 63..1 = edge index
		//   bit 0      = lb_fixed
		let lb_fixed = data & 1 == 1;
		let edge = (data >> 1) as usize;
		let e = &self.edges[edge];
		// At explain time the trail has been rewound (goto_assign_lit)
		// to the propagation point.
		if lb_fixed {
			// `from.min` drove the falsification — request the to-side
			// upper-bound literal at the strongest threshold first, then
			// reconcile from-side with its relaxed meaning.
			let source_lb = self.int_vars[e.from].min(state);
			let (lit_ub, ub_meaning) =
				self.int_vars[e.to].lit_relaxed(state, IntLitMeaning::Less(source_lb - e.val));
			let meaning_ub = if let IntLitMeaning::Less(v) = ub_meaning {
				v
			} else {
				unreachable!("lit_relaxed of Less should return Less")
			};
			let (lit_lb, _) = self.int_vars[e.from].lit_relaxed(
				state,
				IntLitMeaning::GreaterEq(min(source_lb, meaning_ub + e.val)),
			);
			vec![lit_lb, lit_ub]
		} else {
			// `to.max` drove the falsification — symmetric of the above.
			let target_ub = self.int_vars[e.to].max(state);
			let (lit_lb, lb_meaning) = self.int_vars[e.from]
				.lit_relaxed(state, IntLitMeaning::GreaterEq(target_ub + e.val + 1));
			let meaning_lb = if let IntLitMeaning::GreaterEq(v) = lb_meaning {
				v
			} else {
				unreachable!("lit_relaxed of GreaterEq should return GreaterEq")
			};
			let (lit_ub, _) = self.int_vars[e.to].lit_relaxed(
				state,
				IntLitMeaning::Less(max(target_ub + 1, meaning_lb - e.val)),
			);
			vec![lit_lb, lit_ub]
		}
	}

	/// Eager bool-set-false reason, used by [`Self::set_bool_false`] when
	/// `bool_reasons` is 1 (lifted) or 2 (eager). Returns a closure so
	/// callers can defer construction past the `BoolPropagationActions::fix`
	/// borrow boundary.
	fn get_bool_reason<'a, 'b>(
		&'a self,
		edge: usize,
		lb_fixed: bool,
	) -> impl crate::constraints::ReasonBuilder<SolvingContext<'b>> + 'a {
		let bool_reasons = self.bool_reasons;
		move |ctx: &mut SolvingContext<'_>| {
			let e = &self.edges[edge];
			match bool_reasons {
				1 => {
					let mut lb = self.get_cur_lower_bound(ctx, e.from);
					let mut ub = self.get_cur_upper_bound(ctx, e.to);
					if lb_fixed {
						ub = lb - e.val - 1;
					} else {
						lb = ub + e.val + 1;
					}
					vec![
						self.int_vars[e.from].lit(ctx, IntLitMeaning::GreaterEq(lb)),
						self.int_vars[e.to].lit(ctx, IntLitMeaning::Less(ub + 1)),
					]
				}
				2 => {
					vec![
						self.int_vars[e.from].min_lit(ctx),
						self.int_vars[e.to].max_lit(ctx),
					]
				}
				_ => unreachable!(),
			}
		}
	}

	// ---- Bound shadow helpers ----

	fn get_cur_lower_bound<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		SolverView<IntVal>: IntInspectionActions<Ctx>,
	{
		match self.lower_bound[n] {
			Some(lb) => lb,
			None => self.int_vars[n].min(ctx),
		}
	}

	fn get_cur_upper_bound<Ctx>(&self, ctx: &Ctx, n: usize) -> IntVal
	where
		Ctx: ReasoningContext + ?Sized,
		SolverView<IntVal>: IntInspectionActions<Ctx>,
	{
		match self.upper_bound[n] {
			Some(ub) => ub,
			None => self.int_vars[n].max(ctx),
		}
	}

	/// Build the explanation for a negative cycle reaching `node` during
	/// `inc_sat`. Walks the current Dijkstra backtrace and collects the
	/// gating Booleans along the path.
	fn get_cycle_reason(&self, node: usize) -> Vec<SolverView<bool>> {
		let mut reason = Vec::new();
		let mut var = node;
		while let Some((cur, b)) = self.backtrace[var] {
			if let Some(b) = b {
				reason.push(self.bool_vars[b]);
			}
			var = cur;
		}
		reason
	}

	// ---- Implication propagation for a newly-added edge ----

	fn inc_imp(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		new_index: usize,
	) -> Result<(), Conflict<Decision<bool>>> {
		// No dormant gated edge remains when every created one is closed.
		// `None` ⇒ no gated edge was ever registered ⇒ nothing open.
		let num_closed = self.num_closed_edges.map_or(0, |c| ctx.trailed(c));
		if self.num_gated_created == num_closed {
			return Ok(());
		}

		let incoming_u = self.dijkstra_relevant(ctx, new_index, false);
		let outgoing_v = self.dijkstra_relevant(ctx, new_index, true);
		let indegree_u: usize = incoming_u
			.iter()
			.map(|(&n, _)| self.open_in[n].num_open(ctx))
			.sum();
		let outdegree_v: usize = outgoing_v
			.iter()
			.map(|(&n, _)| self.open_out[n].num_open(ctx))
			.sum();

		let new_edge_val = self.edges[new_index].val;

		if indegree_u < outdegree_v {
			let keys: Vec<usize> = incoming_u.keys().copied().collect();
			for n in keys {
				let in_pairs: Vec<usize> = self.open_in[n].open_iter(ctx).collect();
				for i in in_pairs {
					let &e = self.open_in[n].index(ctx, i);
					let edge = self.edges[e];
					if outgoing_v.contains_key(&edge.from)
						&& outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val
					{
						self.close_imp_edge(ctx, e);
					}
				}
				let out_pairs: Vec<usize> = self.open_out[n].open_iter(ctx).collect();
				for i in out_pairs {
					let &e = self.open_out[n].index(ctx, i);
					let edge = self.edges[e];
					if outgoing_v.contains_key(&edge.to)
						&& outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val < -edge.val
					{
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		} else {
			let keys: Vec<usize> = outgoing_v.keys().copied().collect();
			for n in keys {
				let out_pairs: Vec<usize> = self.open_out[n].open_iter(ctx).collect();
				for i in out_pairs {
					let &e = self.open_out[n].index(ctx, i);
					let edge = self.edges[e];
					if incoming_u.contains_key(&edge.to)
						&& outgoing_v[&edge.from] + incoming_u[&edge.to] - new_edge_val <= edge.val
					{
						self.close_imp_edge(ctx, e);
					}
				}
				let in_pairs: Vec<usize> = self.open_in[n].open_iter(ctx).collect();
				for i in in_pairs {
					let &e = self.open_in[n].index(ctx, i);
					let edge = self.edges[e];
					if incoming_u.contains_key(&edge.from)
						&& outgoing_v[&edge.to] + incoming_u[&edge.from] - new_edge_val < -edge.val
					{
						self.close_imp_edge(ctx, e);
						let result = self.inc_sat(ctx, e)?;
						debug_assert!(!result, "Adding {e} should not be possible");
					}
				}
			}
		}

		Ok(())
	}

	// ---- Incremental lower/upper bound propagation ----

	fn inc_lb(&mut self, ctx: &mut SolvingContext<'_>) -> Result<(), Conflict<Decision<bool>>> {
		self.reset_visit();
		let pi0 = self
			.lower_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].min(ctx) + self.pi[n])
			.max()
			.unwrap();
		let mut queue = LazyPriorityQueue::new();
		for &n in self.lower_bound_changes.iter() {
			let _ = queue.push(n, Reverse(pi0 - self.int_vars[n].min(ctx) - self.pi[n]));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 - gamma_s - self.pi[s];
			if bound > self.get_cur_lower_bound(ctx, s) || self.lower_bound_changes.contains(&s) {
				self.update_lb(s, bound);
				if bound > self.int_vars[s].min(ctx) {
					let (prev, b) = self.backtrace[s].unwrap();
					let lb = self.get_cur_lower_bound(ctx, prev);
					self.set_int_lower_bound(ctx, s, bound, b, prev, lb)?;
					let _ = self.lower_bound_changes.insert(s);
				}
				for &e in self.active_out[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.to] {
						let path = gamma_s + self.pi[s] + edge.val - self.pi[edge.to];
						let old = queue.push_increase(edge.to, Reverse(path));
						if old.is_none_or(|Reverse(old_path)| path < old_path) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	// ---- Incremental SAT (new-edge consistency check) ----

	/// Check whether the newly-activated edge introduces a negative
	/// cycle, and either set the gate to false (when gated) or declare a
	/// conflict (when global). Returns `Ok(true)` when the edge was
	/// installed cleanly (and `pi` updates were merged), `Ok(false)` when
	/// the cycle was detected and the gate was falsified.
	fn inc_sat(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		new_index: usize,
	) -> Result<bool, Conflict<Decision<bool>>> {
		let new_edge = self.edges[new_index];
		let mut queue = LazyPriorityQueue::new();
		let mut pi_new: FxHashMap<usize, IntVal> = FxHashMap::default();
		self.backtrace[new_edge.to] = None;
		let gamma_v = self.pi[new_edge.from] + new_edge.val - self.pi[new_edge.to];
		if gamma_v < 0 {
			let _ = queue.push(new_edge.to, Reverse(gamma_v));
		}
		while !queue.is_empty() && queue.get_priority(&new_edge.from).is_none() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			let _ = pi_new.insert(s, self.pi[s] + gamma_s);
			for &e in self.active_out[s].iter(ctx) {
				let edge = &self.edges[e];
				if !pi_new.contains_key(&edge.to) {
					let gamma_t = pi_new[&s] + edge.val - self.pi[edge.to];
					if gamma_t < 0 {
						let old = queue.push_increase(edge.to, Reverse(gamma_t));
						if old.is_none_or(|Reverse(old_gamma)| gamma_t < old_gamma) {
							self.backtrace[edge.to] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		if queue.get_priority(&new_edge.from).is_some() {
			let reason = self.get_cycle_reason(new_edge.from);
			if let Some(b) = new_edge.bool_var {
				let bv = self.bool_vars[b];
				bv.fix(ctx, false, reason)?;
			} else {
				return Err(ctx.declare_conflict(reason));
			}
			return Ok(false);
		}
		for (var, val) in pi_new {
			self.pi[var] = val;
		}
		Ok(true)
	}

	fn inc_ub(&mut self, ctx: &mut SolvingContext<'_>) -> Result<(), Conflict<Decision<bool>>> {
		self.reset_visit();
		let pi0 = self
			.upper_bound_changes
			.iter()
			.map(|&n| self.int_vars[n].max(ctx) + self.pi[n])
			.min()
			.unwrap();
		let mut queue = LazyPriorityQueue::new();
		for &n in self.upper_bound_changes.iter() {
			let _ = queue.push(n, Reverse(self.pi[n] + self.int_vars[n].max(ctx) - pi0));
		}
		while !queue.is_empty() {
			let (s, Reverse(gamma_s)) = queue.pop().unwrap();
			self.visit(s);
			let bound = pi0 + gamma_s - self.pi[s];
			if bound < self.get_cur_upper_bound(ctx, s) || self.upper_bound_changes.contains(&s) {
				self.update_ub(s, bound);
				if bound < self.int_vars[s].max(ctx) {
					let (prev, b) = self.backtrace[s].unwrap();
					let ub = self.get_cur_upper_bound(ctx, prev);
					self.set_int_upper_bound(ctx, s, bound, b, prev, ub)?;
					let _ = self.upper_bound_changes.insert(s);
				}
				for &e in self.active_in[s].iter(ctx) {
					let edge = &self.edges[e];
					if !self.visited[edge.from] {
						let path = gamma_s + self.pi[edge.from] + edge.val - self.pi[s];
						let old = queue.push_increase(edge.from, Reverse(path));
						if old.is_none_or(|Reverse(old_path)| path < old_path) {
							self.backtrace[edge.from] = Some((s, edge.bool_var));
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Find or create the node index for a gating Boolean view.
	pub(crate) fn intern_bool(&mut self, trail: &mut Trail, b: SolverView<bool>) -> usize {
		if let Some(&n) = self.bool_var_to_node.get(&b) {
			return n;
		}
		let n = self.bool_vars.len();
		self.bool_vars.push(b);
		let _ = self.bool_var_to_node.insert(b, n);
		self.bool_implications.push(TrailedOpenList::new(trail));
		n
	}

	/// Find or create the node index for an integer decision view.
	///
	/// O(1) amortised. Lazily extends the per-node trailed adjacency
	/// lists. Safe to call mid-search — the trail is updated so
	/// adjacency entries roll back correctly.
	pub(crate) fn intern_int(&mut self, trail: &mut Trail, x: SolverView<IntVal>) -> usize {
		if let Some(&n) = self.int_var_to_node.get(&x) {
			return n;
		}
		let n = self.int_vars.len();
		self.int_vars.push(x);
		let _ = self.int_var_to_node.insert(x, n);
		self.active_out.push(TrailedList::new(trail, false));
		self.active_in.push(TrailedList::new(trail, false));
		self.open_out.push(TrailedOpenList::new(trail));
		self.open_in.push(TrailedOpenList::new(trail));
		self.pi.push(0);
		self.lower_bound.push(None);
		self.upper_bound.push(None);
		self.backtrace.push(None);
		self.visited.push(false);
		n
	}

	pub(crate) fn notify_lb_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		SolverView<IntVal>: IntInspectionActions<Ctx>,
	{
		if self.lower_bound[n].is_none_or(|v| v < self.int_vars[n].min(ctx)) {
			return self.lower_bound_changes.insert(n);
		}
		false
	}

	pub(crate) fn notify_ub_change<Ctx>(&mut self, ctx: &Ctx, n: usize) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		SolverView<IntVal>: IntInspectionActions<Ctx>,
	{
		if self.upper_bound[n].is_none_or(|v| v > self.int_vars[n].max(ctx)) {
			return self.upper_bound_changes.insert(n);
		}
		false
	}

	/// Boolean propagation entry point invoked by the booleans phase.
	///
	/// For each gating Boolean newly fixed since the last call, either
	/// activate every edge it gates (gate fixed true) and propagate its
	/// consequences via `propagate_edge_addition`, or close every edge it
	/// gates (gate fixed false) so the rest of search ignores them.
	pub(crate) fn propagate_booleans(
		&mut self,
		ctx: &mut SolvingContext<'_>,
	) -> Result<(), Conflict<Decision<bool>>> {
		let fixed_bools = mem::take(&mut self.fixed_bools);
		let check_implied = self.use_inc_imp;
		for b in fixed_bools {
			let bv = self.bool_vars[b];
			let val = bv.val(ctx).unwrap();
			if val {
				let edges: Vec<usize> = {
					let mut out = Vec::new();
					for i in self.bool_implications[b].open_iter(ctx) {
						if let Some(&e) = self.bool_implications[b].index_opt(ctx, i) {
							out.push(e);
						}
					}
					out
				};
				for e in edges {
					self.close_imp_edge(ctx, e);
					self.activate_imp_edge(ctx, e);
					self.propagate_edge_addition(ctx, e, check_implied)?;
				}
			} else {
				let edges: Vec<usize> = {
					let mut out = Vec::new();
					for i in self.bool_implications[b].open_iter(ctx) {
						out.push(*self.bool_implications[b].index(ctx, i));
					}
					out
				};
				for e in edges {
					self.close_imp_edge(ctx, e);
				}
			}
		}
		Ok(())
	}

	/// Bounds propagation entry point invoked by the bounds phase.
	pub(crate) fn propagate_bounds(
		&mut self,
		ctx: &mut SolvingContext<'_>,
	) -> Result<(), Conflict<Decision<bool>>> {
		if !self.pi_initialized {
			self.bellman_ford_init_pi(ctx)?;
			self.pi_initialized = true;
			// On first run, seed every node so the initial incremental
			// pass propagates the graph-implied bounds.
			for n in 0..self.int_vars.len() {
				let _ = self.lower_bound_changes.insert(n);
				let _ = self.upper_bound_changes.insert(n);
			}
		}

		if !self.lower_bound_changes.is_empty() {
			self.inc_lb(ctx)?;
		}
		if !self.upper_bound_changes.is_empty() {
			self.inc_ub(ctx)?;
		}

		// Post-pass: for every node whose lower bound was tightened, walk
		// its dormant outgoing / incoming implication edges and either
		// falsify the gate (when the edge can no longer fire) or close
		// the edge silently (when its constraint is already entailed).
		let lb_changes = mem::take(&mut self.lower_bound_changes);
		for n in lb_changes {
			let Some(lb) = self.lower_bound[n] else {
				continue;
			};

			let out_pairs: Vec<usize> = self.open_out[n].open_iter(ctx).collect();
			for i in out_pairs {
				let &e = self.open_out[n].index(ctx, i);
				let edge = self.edges[e];
				let target_ub = self.get_cur_upper_bound(ctx, edge.to);
				if lb - target_ub > edge.val {
					self.set_bool_false(ctx, edge.bool_var, e, false)?;
					self.close_imp_edge(ctx, e);
				}
			}

			let in_pairs: Vec<usize> = self.open_in[n].open_iter(ctx).collect();
			for i in in_pairs {
				let &e = self.open_in[n].index(ctx, i);
				let edge = self.edges[e];
				if self.get_cur_upper_bound(ctx, edge.from) - lb <= edge.val {
					self.close_imp_edge(ctx, e);
				}
			}
		}

		let ub_changes = mem::take(&mut self.upper_bound_changes);
		for n in ub_changes {
			let Some(ub) = self.upper_bound[n] else {
				continue;
			};

			let out_pairs: Vec<usize> = self.open_out[n].open_iter(ctx).collect();
			for j in out_pairs {
				let &e = self.open_out[n].index(ctx, j);
				let edge = self.edges[e];
				if ub - self.get_cur_lower_bound(ctx, edge.to) <= edge.val {
					self.close_imp_edge(ctx, e);
				}
			}

			let in_pairs: Vec<usize> = self.open_in[n].open_iter(ctx).collect();
			for j in in_pairs {
				let &e = self.open_in[n].index(ctx, j);
				let edge = self.edges[e];
				let source_lb = self.get_cur_lower_bound(ctx, edge.from);
				if source_lb - ub > edge.val {
					self.set_bool_false(ctx, edge.bool_var, e, true)?;
					self.close_imp_edge(ctx, e);
				}
			}
		}

		Ok(())
	}

	/// Drive `inc_sat` + (optional) `inc_imp` + immediate bound propagation
	/// for a freshly-activated edge.
	fn propagate_edge_addition(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		e: usize,
		check_implied: bool,
	) -> Result<(), Conflict<Decision<bool>>> {
		let result = self.inc_sat(ctx, e)?;
		debug_assert!(result, "Adding {e} should be possible or cause a conflict!");
		if check_implied {
			self.inc_imp(ctx, e)?;
		}
		let edge = self.edges[e];
		let source_lb = self.get_cur_lower_bound(ctx, edge.from);
		let lb_y = source_lb - edge.val;
		if lb_y > self.get_cur_lower_bound(ctx, edge.to) {
			self.set_int_lower_bound(ctx, edge.to, lb_y, edge.bool_var, edge.from, source_lb)?;
			self.notify_lb_change(ctx, edge.to);
			self.update_lb(edge.to, lb_y);
		}
		let target_ub = self.get_cur_upper_bound(ctx, edge.to);
		let ub_x = target_ub + edge.val;
		if ub_x < self.get_cur_upper_bound(ctx, edge.from) {
			self.set_int_upper_bound(ctx, edge.from, ub_x, edge.bool_var, edge.to, target_ub)?;
			self.notify_ub_change(ctx, edge.from);
			self.update_ub(edge.from, ub_x);
		}
		Ok(())
	}

	/// Register a difference constraint `x − y ≤ d` in the engine
	/// graph.
	///
	/// `gate == None` is a globally-active edge; it enters `active_out`
	/// / `active_in` immediately. `gate == Some(b)` makes the edge a
	/// dormant implication; it lives in `open_out` / `open_in` /
	/// `bool_implications[gate]` until the booleans phase activates it
	/// (gate fixed true) or closes it (gate fixed false). Returns the
	/// edge's index in `self.edges`.
	pub(crate) fn register_edge(
		&mut self,
		trail: &mut Trail,
		x: SolverView<IntVal>,
		y: SolverView<IntVal>,
		d: IntVal,
		gate: Option<SolverView<bool>>,
	) -> usize {
		let from = self.intern_int(trail, x);
		let to = self.intern_int(trail, y);
		let bool_var = gate.map(|b| self.intern_bool(trail, b));
		// Lazily allocate the trailed `num_closed_edges` counter on
		// the very first gated edge.
		if bool_var.is_some() && self.num_closed_edges.is_none() {
			self.num_closed_edges = Some(trail.track(0_usize));
		}
		let mut edge = DiffEdge {
			from,
			to,
			val: d,
			bool_var,
			bool_index: 0,
			out_index: 0,
			in_index: 0,
		};
		let idx = self.edges.len();
		if let Some(b_idx) = bool_var {
			edge.bool_index = self.bool_implications[b_idx].len();
			self.bool_implications[b_idx].push(idx);
			edge.out_index = self.open_out[from].len();
			self.open_out[from].push(idx);
			edge.in_index = self.open_in[to].len();
			self.open_in[to].push(idx);
			// Permanent: the edge now exists for the rest of the
			// search. The open lists' `push` is likewise untrailed;
			// both must stay consistent when search backtracks past
			// this `register_edge`.
			self.num_gated_created += 1;
		} else {
			self.active_out[from].push(trail, idx);
			self.active_in[to].push(trail, idx);
		}
		self.edges.push(edge);
		idx
	}

	pub(crate) fn reset_bounds(&mut self) {
		self.lower_bound_changes.clear();
		self.upper_bound_changes.clear();
		for &n in self.lb_updates.iter() {
			self.lower_bound[n] = None;
		}
		for &n in self.ub_updates.iter() {
			self.upper_bound[n] = None;
		}
		self.lb_updates.clear();
		self.ub_updates.clear();
	}

	fn reset_visit(&mut self) {
		for &n in self.visited_updates.iter() {
			self.visited[n] = false;
		}
		self.visited_updates.clear();
	}

	/// Fix a gating Boolean to false (the gated edge can never fire). Used
	/// from the bounds phase when a domain extreme rules out the edge,
	/// and from `inc_sat` / `inc_imp` when a cycle would form. The reason
	/// mode (`bool_reasons`) selects between deferred and eager
	/// explanations.
	fn set_bool_false(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		bool_var: Option<usize>,
		edge: usize,
		lb_fixed: bool,
	) -> Result<(), Conflict<Decision<bool>>> {
		if self.bool_reasons == 0 {
			// Pack `edge` index into the high bits and `lb_fixed` into the
			// low bit so the booleans phase's `explain` handler can
			// recover both.
			let data = ((edge as u64) << 1) | u64::from(lb_fixed);
			if let Some(b) = bool_var {
				let bv = self.bool_vars[b];
				bv.fix(ctx, false, ctx.deferred_reason(data))?;
			} else {
				return Err(ctx.declare_conflict(ctx.deferred_reason(data)));
			}
		} else if let Some(b) = bool_var {
			let bv = self.bool_vars[b];
			bv.fix(ctx, false, self.get_bool_reason(edge, lb_fixed))?;
		} else {
			return Err(ctx.declare_conflict(self.get_bool_reason(edge, lb_fixed)));
		}
		Ok(())
	}

	fn set_int_lower_bound(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		n: usize,
		value: IntVal,
		bool_var: Option<usize>,
		lb_var: usize,
		lb_val: IntVal,
	) -> Result<(), Conflict<Decision<bool>>> {
		let target_view = self.int_vars[n];
		let source_view = self.int_vars[lb_var];
		let gate = bool_var.map(|b| self.bool_vars[b]);
		let reason = move |rctx: &mut SolvingContext<'_>| {
			let mut atoms = vec![source_view.lit(rctx, IntLitMeaning::GreaterEq(lb_val))];
			if let Some(g) = gate {
				atoms.push(g);
			}
			atoms
		};
		target_view.tighten_min(ctx, value, reason)?;
		Ok(())
	}

	fn set_int_upper_bound(
		&mut self,
		ctx: &mut SolvingContext<'_>,
		n: usize,
		value: IntVal,
		bool_var: Option<usize>,
		ub_var: usize,
		ub_val: IntVal,
	) -> Result<(), Conflict<Decision<bool>>> {
		let target_view = self.int_vars[n];
		let source_view = self.int_vars[ub_var];
		let gate = bool_var.map(|b| self.bool_vars[b]);
		let reason = move |rctx: &mut SolvingContext<'_>| {
			let mut atoms = vec![source_view.lit(rctx, IntLitMeaning::Less(ub_val + 1))];
			if let Some(g) = gate {
				atoms.push(g);
			}
			atoms
		};
		target_view.tighten_max(ctx, value, reason)?;
		Ok(())
	}

	#[expect(
		dead_code,
		reason = "global-edge subsumption check used once the diff-logic brancher/reservoir are reintroduced"
	)]
	pub(crate) fn subsuming_global_edge<Ctx>(
		&self,
		ctx: &Ctx,
		x: SolverView<IntVal>,
		y: SolverView<IntVal>,
		d: IntVal,
	) -> bool
	where
		Ctx: TrailingActions,
	{
		let (Some(&nx), Some(&ny)) = (self.int_var_to_node.get(&x), self.int_var_to_node.get(&y))
		else {
			return false;
		};
		self.active_out[nx].iter(ctx).any(|&e| {
			let edge = &self.edges[e];
			edge.to == ny && edge.bool_var.is_none() && edge.val <= d
		})
	}

	fn update_lb(&mut self, n: usize, val: IntVal) {
		if self.lower_bound[n].is_none() {
			self.lb_updates.push(n);
		}
		self.lower_bound[n] = Some(val);
	}

	fn update_ub(&mut self, n: usize, val: IntVal) {
		if self.upper_bound[n].is_none() {
			self.ub_updates.push(n);
		}
		self.upper_bound[n] = Some(val);
	}

	// ---- Visit bookkeeping ----

	fn visit(&mut self, n: usize) {
		if !self.visited[n] {
			self.visited_updates.push(n);
		}
		self.visited[n] = true;
	}
}

impl Default for DiffLogicPropagator {
	fn default() -> Self {
		Self {
			int_var_to_node: FxHashMap::default(),
			int_vars: Vec::new(),
			bool_var_to_node: FxHashMap::default(),
			bool_vars: Vec::new(),
			edges: Vec::new(),
			active_out: Vec::new(),
			active_in: Vec::new(),
			open_out: Vec::new(),
			open_in: Vec::new(),
			bool_implications: Vec::new(),
			num_gated_created: 0,
			num_closed_edges: None,
			pi: Vec::new(),
			lower_bound: Vec::new(),
			upper_bound: Vec::new(),
			backtrace: Vec::new(),
			visited: Vec::new(),
			visited_updates: Vec::new(),
			lower_bound_changes: FxHashSet::default(),
			upper_bound_changes: FxHashSet::default(),
			lb_updates: Vec::new(),
			ub_updates: Vec::new(),
			fixed_bools: FxHashSet::default(),
			pi_initialized: false,
			pending_install: Vec::new(),
			// Lazy lit_relaxed reasons (mode 0) + proactive implication
			// check (inc_imp) — both validated as net wins over the
			// previous {mode=2, inc_imp=false} default. See
			// `Self::explain` and `inc_imp`.
			bool_reasons: 0,
			use_inc_imp: true,
		}
	}
}

// =====================================================================
// Phase-4 trait impl: register `DiffLogicPropagator` as a propagator on
// `Engine`. `DiffLogicConstraint::to_solver` constructs an instance and
// registers it via `LoweringContext::add_propagator`; the engine then
// drives it through the usual `Propagator` interface (no more sentinel
// dispatch).
// =====================================================================

impl crate::constraints::Propagator<crate::solver::engine::Engine> for DiffLogicPropagator {
	fn advise_of_backtrack(
		&mut self,
		_ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::NotificationContext<'_>,
	) {
		self.reset_bounds();
		self.fixed_bools.clear();
	}

	fn advise_of_bool_change(
		&mut self,
		_ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::NotificationContext<'_>,
		data: u64,
	) -> bool {
		self.advise_bool_fixed(data as usize)
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		self.advise_int_change(ctx, data as usize, event)
	}

	fn explain(
		&mut self,
		ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::ExplanationContext<'_>,
		lit: <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::Atom,
		data: u64,
	) -> crate::Conjunction<<crate::solver::engine::Engine as crate::actions::ReasoningEngine>::Atom>
	{
		DiffLogicPropagator::explain(self, ctx, lit, data)
	}

	fn initialize(
		&mut self,
		ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::InitializationContext<'_>,
	) {
		use crate::{actions::InitActions, solver::queue::PriorityLevel};

		ctx.set_priority(PriorityLevel::High);
		ctx.advise_on_backtrack();

		// Record the owning `PropRef` so the mid-search lazy-edge drain
		// and CLI setters can locate this propagator.
		ctx.register_as_diff_logic_owner();

		// Drain the edges stashed by `DiffLogicConstraint::to_solver`
		// into the actual graph. `register_edge` mutates the trail; we
		// can't do this in `to_solver` because `LoweringContext`
		// doesn't expose the engine trail directly.
		let pending = mem::take(&mut self.pending_install);
		for (x, y, d, gate) in pending {
			let trail = ctx.state_trail_mut();
			let _ = self.register_edge(trail, x, y, d, gate);
		}

		// Subscribe bounds advisors on every interned int endpoint and
		// fixed advisors on every gating Boolean. Each advisor's `data`
		// is the node index in the propagator's graph.
		for n in 0..self.int_vars.len() {
			let view = self.int_vars[n];
			ctx.subscribe_diff_logic_int_bounds(view, n as u64);
		}
		for n in 0..self.bool_vars.len() {
			let view = self.bool_vars[n];
			ctx.subscribe_diff_logic_bool_fixed(view, n as u64);
		}
	}

	fn propagate(
		&mut self,
		ctx: &mut <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::PropagationContext<'_>,
	) -> Result<(), <crate::solver::engine::Engine as crate::actions::ReasoningEngine>::Conflict> {
		self.propagate_bounds(ctx)?;
		self.propagate_booleans(ctx)?;
		Ok(())
	}
}

// =====================================================================
// Auto-detection + expansion (M.2).
//
// The methods below live on `Model` because the expansion paths need to
// interleave reads/writes against `self.diff_logic` with calls into
// `Model` itself (alias resolution, Boolean minting, CNF clause posting,
// `unify`). Splitting the data (here) from the API (on `Model`) keeps
// the diff-logic surface in this single module while respecting the
// borrow checker.
// =====================================================================

impl Model {
	/// Post a `Reified(b, x, y, d)` diff-logic constraint, routing
	/// through the model-side subsumption cache.
	///
	/// If `diff_lit_map` already holds a canonical Boolean for
	/// `(canonical_x, canonical_y, d)` (or its reverse-direction
	/// equivalent at `(canonical_y, canonical_x, −d − 1)`), the
	/// supplied `b` is aliased onto the canonical Boolean via
	/// [`View::unify`] and NO new edges are added.
	///
	/// Otherwise the supplied `b` becomes the new canonical: two
	/// gated edges (`b → (x − y ≤ d)` and `¬b → (y − x ≤ −d − 1)`)
	/// land in `pending_edges`, the cache is populated in both
	/// directions, and order-encoding chain implication clauses
	/// (`prev → b` and `b → next`) are posted to immediate
	/// `d`-neighbours.
	pub(crate) fn add_diff_logic_reified(
		&mut self,
		b: View<bool>,
		x: View<IntVal>,
		y: View<IntVal>,
		d: IntVal,
	) {
		let x = x.resolve_alias(self).0;
		let y = y.resolve_alias(self).0;

		// Forward exact hit: alias `b` onto the canonical.
		if let Some(&canonical) = self
			.diff_edges
			.diff_lit_map
			.get(&(x, y))
			.and_then(|m| m.get(&d))
		{
			let _ = b
				.resolve_alias(self)
				.unify(self, canonical.resolve_alias(self));
			return;
		}
		// Reverse exact hit: `(x − y ≤ d)` ≡ `¬(y − x ≤ −d − 1)`.
		if let Some(&canonical) = self
			.diff_edges
			.diff_lit_map
			.get(&(y, x))
			.and_then(|m| m.get(&(-d - 1)))
		{
			let _ = b
				.resolve_alias(self)
				.unify(self, (!canonical).resolve_alias(self));
			return;
		}

		// Cache miss: `b` becomes the new canonical.
		self.diff_lit_insert(b, x, y, d);
	}

	/// Insert a freshly-canonical Reified Boolean into the diff-logic
	/// pipeline: push the two underlying gated edges, populate
	/// `diff_lit_map` in both directions, and emit order-encoding
	/// chain implication clauses against immediate `d` neighbours.
	/// Assumes `(x, y, d)` is NOT already in the cache (the lookup
	/// is the caller's responsibility) and that `x, y` are already
	/// canonical (alias-resolved).
	pub(crate) fn diff_lit_insert(
		&mut self,
		b: View<bool>,
		x: View<IntVal>,
		y: View<IntVal>,
		d: IntVal,
	) {
		// Probe forward-direction chain neighbours BEFORE mutating the map.
		let prev = self
			.diff_edges
			.diff_lit_map
			.get(&(x, y))
			.and_then(|m| m.range(..d).next_back().map(|(_, &b)| b));
		let next = self
			.diff_edges
			.diff_lit_map
			.get(&(x, y))
			.and_then(|m| m.range((d + 1)..).next().map(|(_, &b)| b));

		// Two gated edges encoding `b ↔ (x − y ≤ d)`.
		self.push_pending_diff_edge(ModelDiffEdge {
			x,
			y,
			d,
			gate: Some(b),
		});
		self.push_pending_diff_edge(ModelDiffEdge {
			x: y,
			y: x,
			d: -d - 1,
			gate: Some(!b),
		});

		// Populate cache in both directions.
		let _ = self
			.diff_edges
			.diff_lit_map
			.entry((x, y))
			.or_default()
			.insert(d, b);
		let _ = self
			.diff_edges
			.diff_lit_map
			.entry((y, x))
			.or_default()
			.insert(-d - 1, !b);

		// Chain clauses for SAT-level subsumption against `d`-neighbours.
		if let Some(bp) = prev {
			let _ = self
				.proposition(BoolFormula::Implies(
					BoolFormula::Atom(bp).into(),
					BoolFormula::Atom(b).into(),
				))
				.post();
		}
		if let Some(bn) = next {
			let _ = self
				.proposition(BoolFormula::Implies(
					BoolFormula::Atom(b).into(),
					BoolFormula::Atom(bn).into(),
				))
				.post();
		}
	}

	/// Lower `b → (x − y ≠ d)` into two gated edges plus the CNF
	/// disjunction that links them. Allocates two fresh Booleans
	/// `c1`, `c2` and posts `b → (c1 ∨ c2)` and `(¬c1 ∨ ¬c2)`.
	fn expand_implied_not_equals(
		&mut self,
		b: View<bool>,
		x: View<IntVal>,
		y: View<IntVal>,
		d: IntVal,
	) -> Result<(), Conflict<View<bool>>> {
		let c1 = self.new_bool_decision();
		let c2 = self.new_bool_decision();

		// b → (c1 ∨ c2).
		let _ = self
			.proposition(BoolFormula::Implies(
				BoolFormula::Atom(b).into(),
				BoolFormula::Or(vec![BoolFormula::Atom(c1), BoolFormula::Atom(c2)]).into(),
			))
			.post();
		// ¬c1 ∨ ¬c2 (at most one of c1, c2 can be true — keeps the
		// witness disjoint between the two edges).
		let _ = self
			.proposition(BoolFormula::Or(vec![
				BoolFormula::Atom(!c1),
				BoolFormula::Atom(!c2),
			]))
			.post();

		// c1 → (x − y ≤ d − 1).
		self.push_pending_diff_edge(ModelDiffEdge {
			x,
			y,
			d: d - 1,
			gate: Some(c1),
		});
		// c2 → (y − x ≤ −d − 1).
		self.push_pending_diff_edge(ModelDiffEdge {
			x: y,
			y: x,
			d: -d - 1,
			gate: Some(c2),
		});

		Ok(())
	}

	/// Expand one `DifferenceLogicConstraint` into edges (appended to
	/// `diff_logic.pending_edges`), routing the Reified case through
	/// subsumption first. Disequality variants allocate fresh model
	/// Booleans and post the supporting CNF disjunctions.
	pub(crate) fn expand_one_diff_logic(
		&mut self,
		c: DifferenceLogicConstraint,
	) -> Result<(), Conflict<View<bool>>> {
		use DifferenceLogicConstraint as DLC;
		match c {
			DLC::Global(x, y, d) => {
				self.push_pending_diff_edge(ModelDiffEdge {
					x,
					y,
					d,
					gate: None,
				});
			}
			DLC::Implied(b, x, y, d) => {
				self.push_pending_diff_edge(ModelDiffEdge {
					x,
					y,
					d,
					gate: Some(b),
				});
			}
			DLC::Reified(b, x, y, d) => {
				// Route through subsumption — `add_diff_logic_reified` will
				// either alias `b` onto a canonical or push the two edges
				// itself.
				self.add_diff_logic_reified(b, x, y, d);
			}
			DLC::ImpliedEquals(b, x, y, d) => {
				self.push_pending_diff_edge(ModelDiffEdge {
					x,
					y,
					d,
					gate: Some(b),
				});
				self.push_pending_diff_edge(ModelDiffEdge {
					x: y,
					y: x,
					d: -d,
					gate: Some(b),
				});
			}
			DLC::NotEquals(x, y, d) => {
				let g = self.new_bool_decision();
				self.push_pending_diff_edge(ModelDiffEdge {
					x,
					y,
					d: d - 1,
					gate: Some(g),
				});
				self.push_pending_diff_edge(ModelDiffEdge {
					x: y,
					y: x,
					d: -d - 1,
					gate: Some(!g),
				});
			}
			DLC::ImpliedNotEquals(b, x, y, d) => {
				self.expand_implied_not_equals(b, x, y, d)?;
			}
			DLC::ReifiedEquals(b, x, y, d) => {
				// `b → (x − y == d)` — two edges gated by `b`.
				self.push_pending_diff_edge(ModelDiffEdge {
					x,
					y,
					d,
					gate: Some(b),
				});
				self.push_pending_diff_edge(ModelDiffEdge {
					x: y,
					y: x,
					d: -d,
					gate: Some(b),
				});
				// `¬b → (x − y ≠ d)`.
				self.expand_implied_not_equals(!b, x, y, d)?;
			}
		}
		Ok(())
	}

	/// Try to route a normalized two-term linear constraint into the
	/// model-side diff-logic service.
	///
	/// Returns:
	/// - `Some(Ok(()))` — the shape matched, the constraint was expanded into
	///   edges (pending the next `process_round`), and the caller should NOT
	///   post an `IntLinear`. **Not currently reachable** — see the note below.
	/// - `Some(Err(_))` — match succeeded but an expansion side-effect produced
	///   a conflict.
	/// - `None` — shape did not match (or `diff_logic.level == 0`); caller
	///   should fall back to the normal `IntLinear` post.
	///
	/// # Transitional behaviour (M.2 → M.5)
	///
	/// In M.2 the service *records* matched constraints into
	/// `pending_edges` and `diff_lit_map` (for subsumption / future
	/// processing) but ALWAYS returns `None` so the caller still posts
	/// the regular `IntLinear`. M.5 flips the switch to return
	/// `Some(Ok(()))` on a successful match and assumes responsibility
	/// for the engine-side handoff via Phase-M lowering. Keeping the
	/// fallback `IntLinear` in M.2..M.4 preserves correctness of the
	/// existing test suite while the service is being built out.
	///
	/// Shape requirement: exactly two terms, both unit-scaled
	/// (`scale == ±1`, `offset == 0`) integer views, with opposite signs
	/// (one `+x`, one `−y`).
	pub(crate) fn try_route_diff_logic(
		&mut self,
		terms: &[View<IntVal>],
		comparator: LinComparator,
		rhs: IntVal,
		reif: Option<Reification>,
	) -> Option<Result<(), Conflict<View<bool>>>> {
		use crate::{
			constraints::diff_logic::DifferenceLogicConstraint as DLC,
			model::view::integer::IntView,
		};

		if self.diff_logic_level == DiffLogicLevel::Off || terms.len() != 2 {
			return None;
		}

		// Pull (variable view, sign) out of each term. Both must be
		// unit-scaled (Linear or Bool) with zero offset.
		fn unit_scale(term: View<IntVal>) -> Option<(View<IntVal>, IntVal)> {
			match term.0 {
				IntView::Linear(lin) => {
					if lin.offset != 0 {
						return None;
					}
					match lin.scale.get() {
						1 => Some((term, 1)),
						-1 => Some((-term, -1)),
						_ => None,
					}
				}
				IntView::Bool(lin) => {
					if lin.offset != 0 {
						return None;
					}
					match lin.scale.get() {
						1 => Some((term, 1)),
						-1 => Some((-term, -1)),
						_ => None,
					}
				}
				IntView::Const(_) => None,
			}
		}

		let (a, sa) = unit_scale(terms[0])?;
		let (b, sb) = unit_scale(terms[1])?;
		if sa + sb != 0 {
			// `x + y` shape, not `x − y`.
			return None;
		}
		// Normalize so `x` carries the +1 coefficient.
		let (x, y) = if sa == 1 { (a, b) } else { (b, a) };

		let level = self.diff_logic_level;

		// Map (comparator, reif) → list of DifferenceLogicConstraints to expand.
		// The level guards reject the constraint by returning `None` so the
		// caller falls back to a normal IntLinear post.
		let constraints: Vec<DLC> = match (comparator, reif) {
			(LinComparator::LessEq, None) if level >= DiffLogicLevel::Basic => {
				vec![DLC::Global(x, y, rhs)]
			}
			(LinComparator::Equal, None) if level >= DiffLogicLevel::Basic => {
				// `x − y == d` ≡ both `x − y ≤ d` and `y − x ≤ −d`.
				vec![DLC::Global(x, y, rhs), DLC::Global(y, x, -rhs)]
			}
			(LinComparator::NotEqual, None) if level >= DiffLogicLevel::NotEquals => {
				vec![DLC::NotEquals(x, y, rhs)]
			}
			(LinComparator::LessEq, Some(Reification::ImpliedBy(g)))
				if level >= DiffLogicLevel::Basic =>
			{
				vec![DLC::Implied(g, x, y, rhs)]
			}
			(LinComparator::LessEq, Some(Reification::ReifiedBy(g)))
				if level >= DiffLogicLevel::Basic =>
			{
				vec![DLC::Reified(g, x, y, rhs)]
			}
			(LinComparator::Equal, Some(Reification::ImpliedBy(g)))
				if level >= DiffLogicLevel::Equals =>
			{
				vec![DLC::ImpliedEquals(g, x, y, rhs)]
			}
			(LinComparator::Equal, Some(Reification::ReifiedBy(g)))
				if level >= DiffLogicLevel::NotEquals =>
			{
				vec![DLC::ReifiedEquals(g, x, y, rhs)]
			}
			(LinComparator::NotEqual, Some(Reification::ImpliedBy(g)))
				if level >= DiffLogicLevel::NotEquals =>
			{
				vec![DLC::ImpliedNotEquals(g, x, y, rhs)]
			}
			// `b ↔ (x − y ≠ d)` ≡ `¬b ↔ (x − y == d)`.
			(LinComparator::NotEqual, Some(Reification::ReifiedBy(g)))
				if level >= DiffLogicLevel::NotEquals =>
			{
				vec![DLC::ReifiedEquals(!g, x, y, rhs)]
			}
			_ => return None,
		};

		for c in constraints {
			if let Err(e) = self.expand_one_diff_logic(c) {
				return Some(Err(e));
			}
		}
		// Re-enqueue the posted `DiffLogicConstraint` so the next
		// propagation iteration runs `process_round` over the freshly
		// pushed pending edges. No-op pre-lowering (constraint not yet
		// posted) — `process_round` is replayed on the very first
		// simplify after `Lowerer` calls `post_constraint`.
		self.enqueue_diff_logic();
		Some(Ok(()))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	/// M.5: a two-term linear posted via `Model::linear` should auto-
	/// detect into the diff-logic service, get lowered as a half-reified
	/// `IntLinear` at solve time, and produce the correct answer.
	///
	/// Reified `b ↔ (x − y ≥ 3)` on `x, y ∈ [0, 5]`: when `b` is
	/// asserted, `x` must be at least 3. Mirrors the doctest from
	/// `model/expressions.rs` (`ModelLinearBuilder::reify`).
	#[test]
	fn auto_detected_reify_solves_correctly() {
		use crate::solver::{Solver, Status, Valuation};

		let mut model = Model::default();
		let x = model.new_int_decision(0..=5);
		let y = model.new_int_decision(0..=5);
		let b = model.linear(x - y).ge(3).reify();
		model.proposition(b).post().unwrap();

		let (mut slv, map): (Solver, _) = model.lower().to_solver().unwrap();
		let x = map.get(&mut slv, x);
		let b = map.get(&mut slv, b);
		let status = slv
			.solve()
			.on_solution(|sol| {
				assert!(<_ as Valuation>::val(&b, sol));
				assert!(<_ as Valuation>::val(&x, sol) >= 3);
			})
			.satisfy();
		assert_eq!(status, Status::Satisfied);
	}

	/// M.4: `Model::propagate` should drive `process_round` in its
	/// fix-point. Posting edges via the service then calling propagate
	/// must produce the same tightening as calling `process_round`
	/// directly on the constraint.
	#[test]
	fn model_propagate_drives_diff_logic_process_round() {
		let mut model = Model::default();
		let x = model.new_int_decision(0..=100);
		let y = model.new_int_decision(0..=100);
		let z = model.new_int_decision(0..=10);
		model.post_diff_logic_constraint();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(x, y, 2))
			.unwrap();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(y, z, 3))
			.unwrap();
		model.propagate().unwrap();
		assert_eq!(x.max(&model), 15);
		assert_eq!(y.max(&model), 13);
	}

	/// A negative cycle in the globally-active subgraph (`x − y ≤ −1`
	/// together with `y − x ≤ −1` gives `0 ≤ −2`) must be caught by
	/// slice 1 inside `process_round`.
	#[test]
	fn process_round_catches_negative_cycle() {
		let mut model = Model::default();
		let x = model.new_int_decision(0..=10);
		let y = model.new_int_decision(0..=10);
		// Post the DL constraint, then push two contradictory Global
		// edges. `model.propagate()` runs the constraint's `simplify`
		// (= `process_round`) which slices 1 must reject.
		model.post_diff_logic_constraint();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(x, y, -1))
			.unwrap();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(y, x, -1))
			.unwrap();
		assert!(model.propagate().is_err());
	}

	/// A chain of Global edges `x − y ≤ 2`, `y − z ≤ 3` should let
	/// slice 2 tighten `x.max` down by `5` from `z.max`.
	#[test]
	fn process_round_tightens_chain_bounds() {
		let mut model = Model::default();
		let x = model.new_int_decision(0..=100);
		let y = model.new_int_decision(0..=100);
		let z = model.new_int_decision(0..=10);
		model.post_diff_logic_constraint();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(x, y, 2))
			.unwrap();
		model
			.expand_one_diff_logic(DifferenceLogicConstraint::Global(y, z, 3))
			.unwrap();
		model.propagate().unwrap();
		assert_eq!(x.max(&model), 15);
		assert_eq!(y.max(&model), 13);
	}
}
