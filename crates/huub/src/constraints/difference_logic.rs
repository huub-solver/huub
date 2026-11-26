//! The global difference logic constraint: every `x - y ≤ d` in the model
//! collected into one weighted graph and reasoned over as a whole.
//!
//! `x - y ≤ d` is an edge from `x` to `y` of weight `d`, so a path bounds the
//! difference between its endpoints and the graph propagates transitively in a
//! way the individual constraints cannot. A half-reified `b → x - y ≤ d` is an
//! *implied* edge, activated when `b` becomes true and dropped when it becomes
//! false; every other two-decision comparison reduces to these two forms.
//!
//! Nothing posts the component by hand:
//! [`Model::post_constraint`](crate::model::Model::post_constraint) recognises
//! a difference constraint as it arrives, and
//! [`DifferenceLogicLevel`] decides which shapes are taken. Recognition and the
//! two search propagators live here; `graph` holds the graph and the
//! algorithms both layers share, and `simplify` the component that owns the
//! graph while the model is simplified.
//!
//! The algorithms follow "Global Difference Constraint Propagation for Finite
//! Domain Solvers", including the incremental `IncSat`, `IncLB`, and `IncUB`
//! procedures and Cotton and Maler's relevance-restricted Dijkstra.

pub(crate) mod graph;
pub(crate) mod simplify;

use std::{cell::RefCell, fmt, num::NonZero, rc::Rc};

pub(crate) use crate::constraints::difference_logic::{
	graph::DifferenceLogicGraph, simplify::DifferenceLogicModel,
};
use crate::{
	DeepClone, IntVal,
	actions::{BoolInitActions, InitActions, IntEvent, IntInitActions, IntPropCond},
	constraints::{
		Conflict, Propagator,
		int_linear::{LinComparator, Reification},
	},
	model::{self, Model, resolved::Resolved},
	solver::{
		self,
		engine::{Engine, PropagatorId, State},
		initialization_context::InitializationContext,
		queue::PriorityLevel,
		solving_context::SolvingContext,
	},
	views::ScaledView,
};

/// The most work, estimated as `|V| · (|V| + |E|)` over every node and edge
/// that the graph has ever held, that a repeated all-pairs pass in
/// [`DifferenceLogicModel::johnson_full`] may cost before it is skipped.
///
/// The first pass, and any pass over a graph whose active edges have doubled
/// since the last one, runs regardless. Skipping costs only the reduction.
const MAX_ALL_PAIRS_WORK: usize = 400_000_000;

/// Propagator that fixes the Boolean of an implied edge that the graph has
/// shown cannot hold, and activates the edges of Booleans fixed to true. Shares
/// its graph with [`DifferenceLogicBounds`]; see there.
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct DifferenceLogicBooleans {
	/// The graph, shared with [`DifferenceLogicBounds`].
	pub(crate) graph: Rc<RefCell<SolverGraph>>,
}

/// Propagator that tightens the bounds of the graph's nodes along its shortest
/// paths.
///
/// Bound and Boolean propagation are separate propagators so that they can run
/// at separate priorities, but share one graph, which deep cloning copies once
/// for both. Only one runs at a time — [`SolvingContext::run_propagators`]
/// takes them by mutable reference — so the shared borrow never fails.
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct DifferenceLogicBounds {
	/// The graph, shared with [`DifferenceLogicBooleans`].
	pub(crate) graph: Rc<RefCell<SolverGraph>>,
}

/// A difference constraint recognised in the model, before
/// [`DifferenceLogicModel::add`] reduces it to graph edges.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DifferenceLogicConstraint {
	/// The left endpoint of `x - y ⋈ d`: a resolved decision and its scale,
	/// with any offset folded into [`Self::d`].
	x: ModelNode,
	/// The right endpoint of `x - y ⋈ d`, in the same shape as [`Self::x`].
	y: ModelNode,
	/// The bound in `x - y ⋈ d`.
	d: IntVal,
	/// The comparison in `x - y ⋈ d`.
	///
	/// An unreified [`LinComparator::Equal`] never reaches here: one endpoint
	/// is then a view of the other, which the model unifies while simplifying
	/// [`IntLinear`](crate::constraints::int_linear::IntLinear).
	comparator: LinComparator,
	/// The Boolean gating the constraint, if it is (half-)reified.
	///
	/// The gate is resolved to the view the graph names it by. Any Boolean
	/// view can gate an edge: a Boolean decision, but also a literal over an
	/// integer comparison, so that an edge activates when a bound moves.
	reif: Option<Reification>,
}

/// Which difference constraints the model hands to its difference logic
/// component.
///
/// Higher levels capture more, but the disequality shapes cost extra Boolean
/// decisions and edges, which does not always pay off.
#[derive(Clone, Copy, Debug, DeepClone, Default, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum DifferenceLogicLevel {
	/// Capture nothing; every constraint stays an
	/// [`IntLinear`](crate::constraints::int_linear::IntLinear).
	Off,
	/// Capture `x - y ≤ d` and its (half-)reified forms.
	///
	/// The default, and the configuration the difference logic paper settles
	/// on.
	#[default]
	Difference,
	/// Also capture `b → x - y = d`.
	Equality,
	/// Also capture `x - y ≠ d`, `b → x - y ≠ d`, and `b ↔ x - y = d`, each of
	/// which introduces Boolean decisions.
	Inequality,
}

/// The two propagators that share the difference logic graph in a solver, as
/// recorded by the lowerer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DifferenceLogicPropagators {
	/// The [`DifferenceLogicBounds`] propagator.
	pub(crate) bounds: PropagatorId,
	/// The [`DifferenceLogicBooleans`] propagator.
	pub(crate) booleans: PropagatorId,
}

/// A node of the model's graph: a decision under a scale, never an offset, a
/// constant, or a Boolean-backed view.
pub(crate) type ModelNode = ScaledView<NonZero<IntVal>, model::Decision<IntVal>>;

/// The graph as it exists during search.
pub(crate) type SolverGraph = DifferenceLogicGraph<SolverNode, solver::Decision<bool>>;

/// A node of the solver's graph; see [`ModelNode`].
pub(crate) type SolverNode = ScaledView<NonZero<IntVal>, solver::Decision<IntVal>>;

impl Propagator<Engine> for DifferenceLogicBooleans {
	fn advise_of_backtrack(&mut self, _: &mut State) {
		self.graph.borrow_mut().fixed_bools.clear();
	}

	fn advise_of_bool_change(&mut self, _: &mut State, data: u64) -> bool {
		self.graph.borrow_mut().fixed_bools.insert(data as usize)
	}

	fn initialize(&mut self, ctx: &mut InitializationContext<'_>) {
		// Four of the paper's five best configurations put Boolean propagation
		// highest.
		ctx.set_priority(PriorityLevel::Highest);
		for (i, b) in self.graph.borrow().bool_dcns.iter().enumerate() {
			b.advise_when_fixed(ctx, i as u64);
		}
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(
		name = "diff_logic_booleans",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(
		&mut self,
		ctx: &mut SolvingContext<'_>,
	) -> Result<(), Conflict<solver::Decision<bool>>> {
		self.graph
			.borrow_mut()
			.propagate_booleans::<Engine, false>(ctx)
	}
}

impl Propagator<Engine> for DifferenceLogicBounds {
	fn advise_of_backtrack(&mut self, _: &mut State) {
		self.graph.borrow_mut().reset_bounds();
	}

	fn advise_of_int_change(&mut self, ctx: &mut State, data: u64, event: IntEvent) -> bool {
		self.graph
			.borrow_mut()
			.notify_int_change(ctx, data as usize, event)
	}

	fn initialize(&mut self, ctx: &mut InitializationContext<'_>) {
		// All five of the paper's best configurations put bound propagation
		// lowest.
		ctx.set_priority(PriorityLevel::Lowest);
		for (i, n) in self.graph.borrow().int_dcns.iter().enumerate() {
			n.advise_when(ctx, IntPropCond::Bounds, i as u64);
		}
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(
		name = "diff_logic_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(
		&mut self,
		ctx: &mut SolvingContext<'_>,
	) -> Result<(), Conflict<solver::Decision<bool>>> {
		self.graph.borrow_mut().propagate_bounds::<Engine>(ctx)
	}
}

impl DifferenceLogicConstraint {
	/// Recognise a difference constraint in a normalised linear constraint
	/// `terms[0] + terms[1] ⋈ rhs`, or return `None` when the shape is not one
	/// the graph can take.
	///
	/// Any two-term linear constraint qualifies: `c₀·v₀ + c₁·v₁ ≤ d` becomes
	/// `x - y ≤ d` by negating one term. Rejected is anything not about *two*
	/// decisions — a constant or Boolean-backed endpoint, or two views of one
	/// decision — which the linear propagator handles better, and which would
	/// otherwise bounce between the model and the graph (see
	/// [`DifferenceLogicModel::retain_edge`]).
	pub(crate) fn recognise(
		prb: &mut Model,
		terms: &[model::View<IntVal>],
		comparator: LinComparator,
		rhs: IntVal,
		reif: Option<Reification>,
	) -> Option<Self> {
		if !prb.diff_logic_level.accepts(comparator, reif) {
			return None;
		}
		let &[first, second] = terms else {
			return None;
		};
		let first = first.resolve_alias(prb);
		let second = second.resolve_alias(prb);
		let first_dec = first.integer_decision()?.into_inner();
		let second_dec = second.integer_decision()?.into_inner();
		if first_dec == second_dec {
			return None;
		}

		// Negating the negative term gives both endpoints a positive scale;
		// when the signs agree, the decision order picks, so that the result
		// does not depend on the order of the terms.
		let negate_second = match (first.scale().is_negative(), second.scale().is_negative()) {
			(false, true) => true,
			(true, false) => false,
			_ => first_dec.idx() < second_dec.idx(),
		};
		let (x, x_dec, y, y_dec) = if negate_second {
			(first, first_dec, second, second_dec)
		} else {
			(second, second_dec, first, first_dec)
		};
		// A view whose negation overflows cannot be an endpoint; the linear
		// propagator reports the problem if there really is one.
		let y = Resolved(y.0.bounding_neg(prb).ok()?);

		// `b ↔ x - y ≠ d` is `¬b ↔ x - y = d`, which is the form the graph
		// reduces.
		let (comparator, reif) = match (comparator, reif) {
			(LinComparator::NotEqual, Some(Reification::ReifiedBy(r))) => {
				(LinComparator::Equal, Some(Reification::ReifiedBy(!r)))
			}
			other => other,
		};
		let reif = reif.map(|reif| match reif {
			Reification::ImpliedBy(b) => Reification::ImpliedBy(b.resolve_alias(prb).into()),
			Reification::ReifiedBy(b) => Reification::ReifiedBy(b.resolve_alias(prb).into()),
		});
		Some(Self {
			x: ScaledView::new(x.scale(), x_dec),
			y: ScaledView::new(y.scale(), y_dec),
			d: rhs - x.offset() + y.offset(),
			comparator,
			reif,
		})
	}
}

impl DifferenceLogicLevel {
	/// Whether a two-term linear constraint with the given comparator and
	/// reification is captured at this level.
	fn accepts(self, comparator: LinComparator, reif: Option<Reification>) -> bool {
		use LinComparator::*;
		use Reification::*;

		match (comparator, reif) {
			// Unified by the model instead.
			(Equal, None) => false,
			(LessEq, _) => self != Self::Off,
			(Equal, Some(ImpliedBy(_))) => matches!(self, Self::Equality | Self::Inequality),
			(Equal, Some(ReifiedBy(_))) | (NotEqual, _) => self == Self::Inequality,
		}
	}
}

impl fmt::Display for DifferenceLogicLevel {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let name = match self {
			Self::Off => "off",
			Self::Difference => "difference",
			Self::Equality => "equality",
			Self::Inequality => "inequality",
		};
		f.write_str(name)
	}
}

#[cfg(test)]
mod tests {
	use std::{any::Any, rc::Rc};

	use expect_test::expect;
	use itertools::Itertools;

	use crate::{
		IntSet, IntVal,
		actions::{BoolInspectionActions, IntInspectionActions, IntSimplificationActions},
		constraints::{
			difference_logic::{
				DifferenceLogicBooleans, DifferenceLogicBounds, DifferenceLogicLevel,
			},
			int_linear::{IntLinear, LinComparator},
		},
		helpers::overflow::OverflowImpossible,
		lower::LoweringError,
		model::{Model, View, deserialize::AnyView as ModelView},
		solver::{Solver, Status, Value},
	};

	/// Assert that the model that `build` makes has the same solutions with the
	/// difference logic component as without it.
	fn assert_agrees_with_off<V, Vars>(build: impl Fn(DifferenceLogicLevel) -> (Model, Vars))
	where
		V: Clone + Into<ModelView>,
		Vars: AsRef<[V]>,
	{
		let (prb, vars) = build(DifferenceLogicLevel::Difference);
		let (reference, ref_vars) = build(DifferenceLogicLevel::Off);
		assert_eq!(
			prb.solutions(vars.as_ref()),
			reference.solutions(ref_vars.as_ref())
		);
	}

	/// Build a model of two difference constraints that force `x + 2 ≤ y` and
	/// `y + 3 ≤ z`, with every decision in `0..=bound`.
	fn chain_model(bound: IntVal) -> (Model, [View<IntVal>; 3]) {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=bound);
		let y = prb.new_int_decision(0..=bound);
		let z = prb.new_int_decision(0..=bound);
		prb.linear(x - y).le(-2).post().unwrap();
		prb.linear(y - z).le(-3).post().unwrap();
		(prb, [x, y, z])
	}

	/// A model in which `p → x - y ≤ -10` is analysed first, and `y - x ≤ -20`,
	/// which rules `p` out, arrives after that. Only the all-pairs pass sees
	/// this: the bounds stay too wide for the bound-based check. With
	/// `padding`, two active edges are there from the start, so that the late
	/// edge does not double the graph.
	fn late_edge_model(budget: Option<usize>, padding: bool) -> (Model, View<bool>) {
		let mut prb = Model::default();
		prb.diff_logic_all_pairs_budget = budget;
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		let p = prb.new_bool_decision();
		prb.linear(x - y).le(-10).implied_by(p).post().unwrap();
		if padding {
			let w = prb.new_int_decision(0..=100);
			let z = prb.new_int_decision(0..=100);
			prb.linear(w - x).le(0).post().unwrap();
			prb.linear(y - z).le(0).post().unwrap();
		}
		prb.propagate().unwrap();

		prb.linear(y - x).le(-20).post().unwrap();
		prb.propagate().unwrap();
		(prb, p)
	}

	/// A model exercising every shape the graph can take: a plain edge, a
	/// half-reified edge, a reified edge, a half-reified equality, and a
	/// disequality.
	fn mixed_model(level: DifferenceLogicLevel) -> (Model, Vec<ModelView>) {
		let mut prb = Model::default();
		prb.set_difference_logic_level(level);
		let x = prb.new_int_decision(0..=3);
		let y = prb.new_int_decision(0..=3);
		let z = prb.new_int_decision(0..=3);
		let v = prb.new_int_decision(0..=3);
		let p = prb.new_bool_decision();
		let q = prb.new_bool_decision();

		prb.linear(x - y).le(1).post().unwrap();
		prb.linear(y - z).le(0).implied_by(p).post().unwrap();
		prb.linear(x - z).le(-1).reified_by(q).post().unwrap();
		prb.linear(x - y).eq(1).implied_by(q).post().unwrap();
		prb.linear(y - z).ne(2).post().unwrap();
		// `v` becomes a node of its own and is then unified with `x`, so the
		// component has to merge two nodes while simplifying.
		prb.linear(v - z).le(0).post().unwrap();
		prb.linear(v - x).eq(0).post().unwrap();

		let vars = vec![x.into(), y.into(), z.into(), v.into(), p.into(), q.into()];
		(prb, vars)
	}

	/// The all-pairs budget does not apply to a graph whose active edges have
	/// at least doubled since the last pass, so the first pass always runs, and
	/// so does one after enough edges have arrived.
	#[test]
	fn test_difference_all_pairs_budget_allows_doubled_graph() {
		// The first pass saw no active edge, so the late one doubles the graph
		// and the pass runs, even on a budget of zero.
		let (prb, p) = late_edge_model(Some(0), false);
		assert_eq!(p.val(&prb), Some(false));
	}

	/// A repeated all-pairs pass over the budget is skipped when the graph has
	/// not doubled. Skipping costs strength, never correctness: the gate that
	/// the pass would have falsified stays open, but still cannot hold.
	#[test]
	fn test_difference_all_pairs_budget_exhausted() {
		// Two active edges become three, which is not double.
		let (prb, p) = late_edge_model(None, true);
		assert_eq!(p.val(&prb), Some(false), "the pass falsifies the gate");

		let (mut prb, p) = late_edge_model(Some(0), true);
		assert_eq!(p.val(&prb), None, "the skipped pass leaves the gate open");
		let conflict = prb
			.proposition(p)
			.post()
			.err()
			.or_else(|| prb.propagate().err());
		assert!(conflict.is_some(), "the gate still cannot hold");
	}

	/// The growth that forces an all-pairs pass is measured against the edges
	/// that the last pass started with. Here that pass removes three of its
	/// five active edges, and two more arrive: four is double what the pass
	/// kept, but not double what it saw, so the budget still applies.
	#[test]
	fn test_difference_all_pairs_budget_ignores_pruned_edges() {
		let mut prb = Model::default();
		prb.diff_logic_all_pairs_budget = Some(0);
		let [a, b, c, d, x, y] = [(); 6].map(|()| prb.new_int_decision(0..=100));
		let p = prb.new_bool_decision();
		prb.linear(x - y).le(-10).implied_by(p).post().unwrap();
		prb.linear(a - b).le(0).post().unwrap();
		prb.linear(b - c).le(0).post().unwrap();
		for redundant in 1..=3 {
			prb.linear(a - c).le(redundant).post().unwrap();
		}
		prb.propagate().unwrap();

		prb.linear(c - d).le(0).post().unwrap();
		prb.linear(y - x).le(-20).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(p.val(&prb), None, "the skipped pass leaves the gate open");
	}

	#[test]
	fn test_difference_chain_propagates_transitively() {
		// The graph derives `z ≥ x + 5` from the two edges, which neither
		// constraint implies on its own.
		let (mut prb, [x, _, z]) = chain_model(20);
		prb.propagate().unwrap();
		assert_eq!(x.max(&prb), 15);
		assert_eq!(z.min(&prb), 5);
	}

	/// A constraint that only becomes a difference constraint while being
	/// simplified still reaches the graph: only the graph unifies a zero-length
	/// cycle, which the assertion checks.
	#[test]
	fn test_difference_constraint_folded_while_simplifying() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=3);
		let y = prb.new_int_decision(0..=3);
		let c = prb.new_int_decision(0..=1);

		// Three terms while `c` is unfixed, so this is not a difference
		// constraint when it is posted.
		prb.linear(x - y + c).le(0).post().unwrap();
		prb.linear(y - x).le(0).post().unwrap();
		// Fixing `c` folds the first constraint down to two terms.
		prb.linear(c).le(0).post().unwrap();
		prb.propagate().unwrap();

		assert_eq!(
			x.resolve_alias(&prb).into_inner(),
			y.resolve_alias(&prb).into_inner(),
			"the zero-length cycle should have unified the two decisions"
		);
	}

	/// A node whose decision becomes a view of a Boolean has its edges turned
	/// into clauses, over the values the node really takes: here `x` becomes
	/// `p + 3`, so `x - y ≤ -1` is `y ≥ 4` or, with `p`, `y ≥ 5`.
	#[test]
	fn test_difference_dissolved_node_keeps_its_offset() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=9);
			let y = prb.new_int_decision(0..=9);
			let p = prb.new_bool_decision();
			prb.linear(x - y).le(-1).post().unwrap();
			prb.propagate().unwrap();
			x.unify(&mut prb, View::<IntVal>::from(p) + 3).unwrap();
			prb.propagate().unwrap();
			let vars: Vec<ModelView> = vec![y.into(), p.into()];
			(prb, vars)
		});
	}

	/// A node left without edges is removed, but an edge posted later brings it
	/// back. Here fixing `y` removes `x` as well, since its only edge was to
	/// `y`, which leaves the graph empty. The component must stay in the model
	/// to take the late edge, and lowering must not drop it.
	#[test]
	fn test_difference_edge_after_node_is_removed() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=5);
			let y = prb.new_int_decision(0..=5);
			let z = prb.new_int_decision(0..=5);
			let p = prb.new_bool_decision();
			prb.linear(x - y).le(0).post().unwrap();
			prb.propagate().unwrap();
			prb.linear(y).le(3).post().unwrap();
			prb.linear(y * -1).le(-3).post().unwrap();
			prb.propagate().unwrap();

			prb.linear(z - x).le(-3).implied_by(p).post().unwrap();
			prb.propagate().unwrap();
			let vars: Vec<ModelView> = vec![x.into(), z.into(), p.into()];
			(prb, vars)
		});
	}

	/// A node that is merged into one removed earlier brings that node back.
	/// Here `b` loses its only edge when `c` is fixed, and `a`, which still has
	/// an edge of its own, then becomes an alias of `b`.
	#[test]
	fn test_difference_edge_moved_onto_a_removed_node() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let b = prb.new_int_decision(0..=9);
			let c = prb.new_int_decision(0..=9);
			let a = prb.new_int_decision(0..=9);
			let d = prb.new_int_decision(0..=9);
			prb.linear(b - c).le(5).post().unwrap();
			prb.linear(a - d).le(-2).post().unwrap();
			prb.propagate().unwrap();
			prb.linear(c).le(4).post().unwrap();
			prb.linear(c * -1).le(-4).post().unwrap();
			prb.propagate().unwrap();
			prb.linear(a - b).eq(0).post().unwrap();
			prb.propagate().unwrap();
			(prb, [a, b, d])
		});
	}

	/// An edge unified onto a *scaled* view of its own other endpoint — `a` and
	/// `2a` are different nodes, since node identity keeps the scale — must
	/// still resolve to the right bound on `a`.
	#[test]
	fn test_difference_edge_reduces_after_unification_with_different_scale() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(-10..=10);
		let b = prb.new_int_decision(-10..=10);
		// An edge between two distinct decisions, `b` and `2a`.
		prb.linear(b - a * 2).le(-3).post().unwrap();
		// A zero-length cycle forcing `a == b`, which folds `b`'s edges onto
		// `a`'s node — turning the edge above into `a - 2a ≤ -3`.
		prb.linear(a - b).le(0).post().unwrap();
		prb.linear(b - a).le(0).post().unwrap();
		prb.propagate().unwrap();

		// `a - 2a ≤ -3` is `-a ≤ -3`, i.e. `a ≥ 3`.
		assert_eq!(a.min(&prb), 3);
	}

	/// A gate that the component fixes itself, by unifying the nodes of a
	/// zero-length cycle, is still reported to it: here `x = y` rules out
	/// `x = 3`, since `y` cannot be 3, while the component is being simplified.
	#[test]
	fn test_difference_gate_fixed_by_a_unification() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			// `x` is created last, so that it is the one to become the alias.
			let y = prb.new_int_decision(IntSet::from_iter([0..=2, 4..=6]));
			let x = prb.new_int_decision(0..=6);
			let a = prb.new_int_decision(0..=3);
			let b = prb.new_int_decision(0..=3);
			prb.linear(x - y).le(0).post().unwrap();
			prb.linear(y - x).le(0).post().unwrap();
			prb.linear(a - b).le(0).implied_by(x.eq(3)).post().unwrap();
			(prb, [x, y, a, b])
		});
	}

	/// A gate that is a literal over a decision keeps working when that
	/// decision becomes a view of a Boolean: here `x` becomes `4p + 3`, so the
	/// gate `x ≥ 5` is `p`.
	#[test]
	fn test_difference_gate_over_a_decision_aliased_to_a_boolean() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=9);
			let a = prb.new_int_decision(0..=3);
			let b = prb.new_int_decision(0..=3);
			let p = prb.new_bool_decision();
			prb.linear(a - b)
				.le(-1)
				.implied_by(x.geq(5))
				.post()
				.unwrap();
			prb.propagate().unwrap();
			x.unify(&mut prb, View::<IntVal>::from(p) * 4 + 3).unwrap();
			prb.propagate().unwrap();
			prb.proposition(p).post().unwrap();
			prb.propagate().unwrap();
			let vars: Vec<ModelView> = vec![a.into(), b.into(), p.into()];
			(prb, vars)
		});
	}

	/// A literal over an integer comparison gates an edge just as a Boolean
	/// decision does.
	#[test]
	fn test_difference_gate_over_an_integer_literal() {
		let build = |level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=3);
			let y = prb.new_int_decision(0..=3);
			let z = prb.new_int_decision(0..=3);
			prb.linear(x - y).le(0).post().unwrap();
			prb.linear(y - z)
				.le(-2)
				.implied_by(x.geq(2))
				.post()
				.unwrap();
			(prb, [x, y, z])
		};
		let (prb, _) = build(DifferenceLogicLevel::Difference);
		assert_eq!(prb.num_constraints(), 1, "both edges should join the graph");
		assert_agrees_with_off(build);
	}

	/// A gate whose only edge closed must still gate an edge posted later.
	#[test]
	fn test_difference_gate_reused_after_its_edges_closed() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=5);
			let y = prb.new_int_decision(0..=5);
			let p = prb.new_bool_decision();
			// The bounds entail this edge, so it closes and leaves `p` without
			// an open edge.
			prb.linear(x - y).le(10).implied_by(p).post().unwrap();
			prb.propagate().unwrap();

			prb.linear(x - y).le(-2).implied_by(p).post().unwrap();
			prb.propagate().unwrap();
			let vars: Vec<ModelView> = vec![x.into(), y.into(), p.into()];
			(prb, vars)
		});
	}

	/// The two propagators hold one graph between them after lowering, and a
	/// copy of the solver keeps them sharing one graph of their own.
	#[test]
	fn test_difference_graph_is_shared_by_the_propagators() {
		let diff_logic_graphs = |slv: &Solver| {
			slv.engine
				.borrow()
				.propagators
				.iter()
				.filter_map(|prop| {
					let prop: &dyn Any = &**prop;
					prop.downcast_ref::<DifferenceLogicBounds>()
						.map(|p| Rc::clone(&p.graph))
						.or_else(|| {
							prop.downcast_ref::<DifferenceLogicBooleans>()
								.map(|p| Rc::clone(&p.graph))
						})
				})
				.collect_vec()
		};

		// The graph as reached through the two propagators that the solver
		// records.
		let recorded_graph = |slv: &Solver| {
			let ids = slv.engine.borrow().state.diff_logic?;
			let bounds = Rc::clone(&slv.propagator::<DifferenceLogicBounds>(ids.bounds)?.graph);
			let booleans = slv.propagator::<DifferenceLogicBooleans>(ids.booleans)?;
			assert!(Rc::ptr_eq(&bounds, &booleans.graph));
			Some(bounds)
		};

		let (mut prb, _) = chain_model(10);
		let (slv, _): (Solver, _) = prb.lower().to_solver().unwrap();
		let graphs = diff_logic_graphs(&slv);
		assert_eq!(graphs.len(), 2, "both propagators are posted");
		assert!(Rc::ptr_eq(&graphs[0], &graphs[1]), "they share one graph");
		let recorded = recorded_graph(&slv).expect("the solver records the propagator");
		assert!(Rc::ptr_eq(&recorded, &graphs[0]));

		// Copying the solver must copy the graph once, not alias it and not
		// split it in two.
		let copy = slv.clone();
		let copied = diff_logic_graphs(&copy);
		assert_eq!(copied.len(), 2);
		assert!(Rc::ptr_eq(&copied[0], &copied[1]), "the copies still share");
		assert!(
			!Rc::ptr_eq(&copied[0], &graphs[0]),
			"the copy is independent of the original"
		);
		let recorded = recorded_graph(&copy).expect("the copy records the propagator");
		assert!(Rc::ptr_eq(&recorded, &copied[0]));

		// A model without any difference constraint posts no propagators.
		let mut empty = Model::default();
		let x = empty.new_int_decision(0..=2);
		empty.linear(x).le(1).post().unwrap();
		let (slv, _): (Solver, _) = empty.lower().to_solver().unwrap();
		assert!(diff_logic_graphs(&slv).is_empty());
		assert!(recorded_graph(&slv).is_none());
	}

	/// An implied edge unified onto a scaled view of its own other endpoint
	/// collapses to one decision, and the bound it enforces must stay
	/// conditional on its gate.
	#[test]
	fn test_difference_implied_edge_reduces_after_unification_with_different_scale() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(-3..=3);
		let b = prb.new_int_decision(-3..=3);
		let p = prb.new_bool_decision();
		// An implied edge between two distinct decisions, `b` and `2a`.
		prb.linear(b - a * 2).le(1).implied_by(p).post().unwrap();
		// A zero-length cycle forcing `a == b`, which folds `b`'s edges onto
		// `a`'s node — turning the edge above into `p → a - 2a ≤ 1`.
		prb.linear(a - b).le(0).post().unwrap();
		prb.linear(b - a).le(0).post().unwrap();

		// `a - 2a ≤ 1` is `-a ≤ 1`, i.e. `a ≥ -1`, but only when `p` holds.
		prb.expect_solutions(
			&[ModelView::from(a), p.into()],
			expect![[r#"
			-3, false
			-2, false
			-1, false
			-1, true
			0, false
			0, true
			1, false
			1, true
			2, false
			2, true
			3, false
			3, true"#]],
		);
	}

	/// An implied edge posted after the graph has been analysed is checked
	/// against the distances of that analysis, without redoing it: here the
	/// earlier `y - x ≤ -20` rules out `p → x - y ≤ -10`. The bounds stay wide
	/// enough that the bound-based falsification check cannot see this.
	#[test]
	fn test_difference_late_implied_edge_is_checked() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		let p = prb.new_bool_decision();
		prb.linear(y - x).le(-20).post().unwrap();
		prb.propagate().unwrap();

		prb.linear(x - y).le(-10).implied_by(p).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(p.val(&prb), Some(false));
	}

	/// Each level captures more, but capturing must never change what the model
	/// means. Higher levels introduce Boolean decisions of their own, so only
	/// the projection onto the original decisions is compared.
	#[test]
	fn test_difference_levels_agree() {
		let (prb, vars) = mixed_model(DifferenceLogicLevel::Off);
		let reference = prb.solutions(&vars);
		assert!(!reference.is_empty(), "the model should be satisfiable");
		for level in [
			DifferenceLogicLevel::Difference,
			DifferenceLogicLevel::Equality,
			DifferenceLogicLevel::Inequality,
		] {
			let (prb, vars) = mixed_model(level);
			assert_eq!(
				prb.solutions(&vars),
				reference,
				"level {level} changed the solution set"
			);
		}
	}

	/// Lowering moves the offset that a decision gained late into the weights
	/// of its edges, and shifts the potential with them: the search algorithms
	/// rely on every reduced cost staying non-negative. Here `x` becomes the
	/// alias `z - 3` without any change to its domain, so nothing wakes the
	/// component before it is lowered.
	#[test]
	fn test_difference_lowering_offset_keeps_potential() {
		let mut prb = Model::default();
		// The domains are already consistent with both constraints, so that
		// the alias changes none of them.
		let z = prb.new_int_decision(5..=9);
		let y = prb.new_int_decision(0..=4);
		let x = prb.new_int_decision(2..=6);
		prb.linear(y - x).le(-2).post().unwrap();
		prb.propagate().unwrap();
		prb.linear(x - z).eq(-3).post().unwrap();

		let (slv, _): (Solver, _) = prb.lower().to_solver().unwrap();
		let ids = slv.engine.borrow().state.diff_logic.unwrap();
		let prop = slv.propagator::<DifferenceLogicBounds>(ids.bounds).unwrap();
		let graph = prop.graph.borrow();
		assert!(
			graph.potential_is_feasible(0..graph.edges.len()),
			"negative reduced cost"
		);
	}

	#[test]
	fn test_difference_negative_cycle_is_unsatisfiable() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=10);
		let y = prb.new_int_decision(0..=10);
		prb.linear(x - y).le(-1).post().unwrap();
		prb.linear(y - x).le(-1).post().unwrap();

		prb.assert_root_infeasible();
	}

	/// A difference constraint recognised only after the graph has been
	/// analysed introduces nodes the all-pairs distance matrix does not cover.
	#[test]
	fn test_difference_node_added_after_initialisation() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=4);
		let y = prb.new_int_decision(0..=4);
		let z = prb.new_int_decision(0..=4);
		let w = prb.new_int_decision(0..=4);
		let c = prb.new_int_decision(1..=1);

		// Analyse a graph over `x` and `y` first, so the distance matrix covers
		// two nodes.
		prb.linear(x - y).le(-1).post().unwrap();
		prb.propagate().unwrap();

		// `c` is a constant, so this is two-term, and joins a graph already
		// analysed; the equality then unifies its nodes.
		prb.linear(z - w + c).le(1).post().unwrap();
		prb.linear(z - w).eq(0).post().unwrap();

		let found = prb.solutions(&[ModelView::from(x), y.into(), z.into(), w.into()]);
		assert_eq!(
			found.len(),
			50,
			"10 ordered pairs for `x < y`, 5 for `z = w`"
		);
		for sol in &found {
			let [Value::Int(x), Value::Int(y), Value::Int(z), Value::Int(w)] = sol[..] else {
				panic!("expected four integer values")
			};
			assert!(x < y, "{x} < {y}");
			assert_eq!(z, w);
		}
	}

	/// A node that a hole in its domain fixes at a value beyond the bound the
	/// graph asked for still passes that value on before it is removed: here
	/// `x ≥ w ≥ 3` leaves `x = 10`, so `x ≤ y` needs `y ≥ 10`, not `y ≥ 3`.
	#[test]
	fn test_difference_node_fixed_by_a_domain_hole() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(IntSet::from_iter([0..=0, 10..=10]));
			let w = prb.new_int_decision(3..=12);
			let y = prb.new_int_decision(0..=12);
			prb.linear(w - x).le(0).post().unwrap();
			prb.linear(x - y).le(0).post().unwrap();
			(prb, [x, w, y])
		});
	}

	/// An endpoint that is an alias with an offset folds that offset into the
	/// weight. The equality makes `z` the alias `y - 2`, so `x - z ≤ 0` is the
	/// edge `x - y ≤ -2`.
	#[test]
	fn test_difference_offset_endpoints() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=5);
		let y = prb.new_int_decision(0..=5);
		let z = prb.new_int_decision(0..=5);
		prb.linear(y - z).eq(2).post().unwrap();
		prb.propagate().unwrap();
		prb.linear(x - z).le(0).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(x.max(&prb), 3);
	}

	/// An edge whose endpoints turn out to be views of one decision is handed
	/// back to the linear propagator, which must still enforce it.
	#[test]
	fn test_difference_over_a_single_decision() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=5);
		let y = prb.new_int_decision(0..=5);
		// The equality unifies `y` with `x`, which turns the difference
		// constraint into the unsatisfiable `x - x ≤ -1`.
		prb.linear(x - y).le(-1).post().unwrap();
		prb.linear(x - y).eq(0).post().unwrap();

		prb.assert_root_infeasible();
	}

	/// A Boolean decision seen as a `0`/`1` integer is not backed by an integer
	/// decision, so it never becomes a node. The constraint stays an
	/// [`IntLinear`], which must still enforce it.
	#[test]
	fn test_difference_over_boolean_backed_views() {
		let mut prb = Model::default();
		let p = prb.new_bool_decision();
		let q = prb.new_bool_decision();
		let z = prb.new_int_decision(0..=2);
		// Neither endpoint of the first constraint is an integer decision; the
		// second mixes one that is with one that is not.
		prb.linear(p * 1 - q * 1).le(0).post().unwrap();
		prb.linear(z - p * 2).le(0).post().unwrap();

		prb.expect_solutions(
			&[ModelView::from(p), q.into(), z.into()],
			expect![[r#"
			false, false, 0
			false, true, 0
			true, true, 0
			true, true, 1
			true, true, 2"#]],
		);
	}

	/// A difference constraint joins the graph rather than becoming a
	/// constraint of its own, so posting one reports the component's
	/// identifier — the same for every constraint that joins.
	#[test]
	fn test_difference_posting_reports_the_component() {
		let mut prb = Model::default();
		let a = prb.new_int_decision(0..=10);
		let b = prb.new_int_decision(0..=10);
		let c = prb.new_int_decision(0..=10);
		// Posted without the builder, which does not report the identifier.
		let le = |terms, rhs| IntLinear::<OverflowImpossible> {
			terms,
			rhs,
			reif: None,
			comparator: LinComparator::LessEq,
		};
		let first = prb.post_constraint(le(vec![a, -b], 2)).unwrap();
		let second = prb.post_constraint(le(vec![b, -c], 3)).unwrap();
		assert_eq!(first, second);

		// A constraint the graph does not capture keeps an identifier of its
		// own.
		let other = prb.post_constraint(le(vec![a, b, c], 12)).unwrap();
		assert_ne!(other, first);
	}

	/// A constraint the graph consumed is still enforced when another tightens
	/// one of its endpoints later: the component subscribes to a node as the
	/// edge that created it is added, so a later bound change still wakes it,
	/// whether it reports one bound or both at once.
	#[test]
	fn test_difference_propagates_later_external_bounds() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		let z = prb.new_int_decision(0..=100);
		// Consumed by the graph, so nothing else in the model enforces them.
		prb.linear(z - x).le(0).post().unwrap();
		prb.linear(x - y).le(-10).post().unwrap();
		prb.propagate().unwrap();

		// Tighten one bound of `y` from outside the graph, after the analysis
		// has run.
		prb.linear(y).le(50).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(x.max(&prb), 40);
		assert_eq!(z.max(&prb), 40);

		// Tighten both bounds of `x` in a single event.
		x.restrict_domain(
			&mut prb,
			&IntSet::from(20..=30),
			|_: &mut Model, _: &mut _| {},
		)
		.unwrap();
		prb.propagate().unwrap();
		assert_eq!(y.min(&prb), 30);
		assert_eq!(z.max(&prb), 30);
	}

	/// A node whose decision becomes an alias of negative scale still passes
	/// its bounds on: here `x` becomes `9 - y`, so `y ≥ 5` is `x ≤ 4`, and
	/// `z ≤ x` needs `z ≤ 4`.
	#[test]
	fn test_difference_propagates_through_a_negated_alias() {
		let mut prb = Model::default();
		let y = prb.new_int_decision(0..=9);
		let x = prb.new_int_decision(0..=9);
		let z = prb.new_int_decision(0..=9);
		prb.linear(z - x).le(0).post().unwrap();
		prb.propagate().unwrap();
		prb.linear(x + y).eq(9).post().unwrap();
		prb.propagate().unwrap();

		prb.linear(y * -1).le(-5).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(z.max(&prb), 4);
	}

	/// A model that only the graph can show to be infeasible reports the
	/// conflict at the root, rather than leaving it to search.
	#[test]
	fn test_difference_reports_a_later_root_conflict() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		prb.linear(x - y).le(-10).post().unwrap();
		prb.propagate().unwrap();

		// `x >= 50` and `y <= 20` leave `x - y >= 30`, which the edge forbids.
		prb.linear(y).le(20).post().unwrap();
		let conflict = prb
			.linear(x * -1)
			.le(-50)
			.post()
			.err()
			.or_else(|| prb.propagate().err());
		assert!(conflict.is_some(), "the graph must report the conflict");
	}

	/// Any two-term linear constraint is an edge. Two terms of the same sign
	/// make one endpoint a negated view, and a scaled view is a node of its
	/// own.
	#[test]
	fn test_difference_scaled_and_same_sign_terms() {
		let build = |level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let x = prb.new_int_decision(0..=3);
			let y = prb.new_int_decision(0..=3);
			let z = prb.new_int_decision(0..=3);
			prb.linear(x + y).le(2).post().unwrap();
			prb.linear(x * 2 - z).le(1).post().unwrap();
			(prb, [x, y, z])
		};
		let (prb, _) = build(DifferenceLogicLevel::Difference);
		assert_eq!(
			prb.num_constraints(),
			1,
			"both constraints should join the graph"
		);
		assert_agrees_with_off(build);
	}

	/// A node shifted by an alias keeps its distances in step, so that a node
	/// unified onto it later is compared against the right paths. Here `a`
	/// becomes `d - 4` and `c` becomes `d + 1` in one pass: `c - b ≤ 7` is then
	/// `d - b ≤ 6`, which `a - b ≤ 5`, now `d - b ≤ 9`, does not imply.
	#[test]
	fn test_difference_unify_after_offset_shift() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let d = prb.new_int_decision(0..=20);
			let a = prb.new_int_decision(-10..=20);
			let b = prb.new_int_decision(0..=20);
			let c = prb.new_int_decision(0..=21);
			prb.linear(a - b).le(5).post().unwrap();
			prb.linear(c - b).le(7).post().unwrap();
			prb.propagate().unwrap();
			prb.linear(a - d).eq(-4).post().unwrap();
			prb.linear(c - d).eq(1).post().unwrap();
			prb.propagate().unwrap();
			(prb, [b, d])
		});
	}

	/// A zero-length cycle is unified along the predecessors of its origin,
	/// which must come from the cycle itself: here the pass from `c`, which
	/// runs after the one from `a`, last set the predecessor of `a` to `c`.
	#[test]
	fn test_difference_zero_cycle_unifies_along_the_cycle() {
		assert_agrees_with_off(|level| {
			let mut prb = Model::default();
			prb.set_difference_logic_level(level);
			let a = prb.new_int_decision(0..=5);
			let b = prb.new_int_decision(0..=5);
			let c = prb.new_int_decision(0..=5);
			prb.linear(a - b).le(-1).post().unwrap();
			prb.linear(b - a).le(1).post().unwrap();
			prb.linear(c - a).le(2).post().unwrap();
			(prb, [a, b, c])
		});
	}

	impl Model {
		/// Assert that lowering proves the model infeasible without search.
		fn assert_root_infeasible(mut self) {
			let result: Result<(Solver, _), _> = self.lower().to_solver();
			match result {
				Err(LoweringError::Simplification(nogood)) => assert!(
					nogood.is_unconditional(),
					"expected unconditional infeasibility, found {nogood:?}"
				),
				Err(err) => panic!("unexpected lowering error: {err}"),
				Ok(_) => panic!("expected the model to be infeasible"),
			}
		}

		/// The number of constraints in the model, where the difference logic
		/// component counts as one.
		fn num_constraints(&self) -> usize {
			self.constraints.iter().flatten().count()
		}

		/// Every solution of the model, projected onto `vars` and sorted, so
		/// that two models can be compared whatever order they enumerate in.
		/// Unlike [`Self::expect_solutions`], this returns data rather than
		/// asserting against a fixed string.
		fn solutions(mut self, vars: &[impl Clone + Into<ModelView>]) -> Vec<Vec<Value>> {
			let (mut slv, map): (Solver, _) = self.lower().to_solver().unwrap();
			let vars = vars
				.iter()
				.map(|v| map.get_any(&mut slv, v.clone().into()))
				.collect_vec();
			let mut found = Vec::new();
			let status = slv
				.solve()
				.all_solutions(vars.clone())
				.collect_solutions_in(vars, &mut found)
				.satisfy();
			assert_eq!(status, Status::Complete);
			found.sort();
			found
		}
	}
}
