//! The global difference logic constraint: every `x - y ≤ d` in the model
//! collected into one weighted graph and reasoned over as a whole.
//!
//! `x - y ≤ d` is an edge from `x` to `y` of weight `d`, so a path bounds the
//! difference between its endpoints and the graph propagates transitively in a
//! way the individual constraints cannot. A half-reified `b → x - y ≤ d` is an
//! *implied* edge, activated when `b` becomes true and dropped when it becomes
//! false; every other two-variable comparison reduces to these two forms.
//!
//! Nothing posts the component by hand: [`Model::linear`](crate::model::Model)
//! recognises a difference constraint as it arrives, and
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
		engine::{Engine, State},
		initialization_context::InitializationContext,
		queue::PriorityLevel,
		solving_context::SolvingContext,
	},
	views::ScaledView,
};

/// The most work, as `|V| · (|V| + |E|)`, that the all-pairs pass in
/// [`DifferenceLogicModel::johnson_full`] may cost before it is skipped.
///
/// On an M4 the pass costs roughly a second per `4·10⁷` of this measure and
/// eight bytes per node pair, so this bounds it at about ten seconds and six
/// hundred megabytes. Edges count as well as nodes, which a bound on nodes
/// alone would miss. Skipping costs only the reduction.
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
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct DifferenceLogicConstraint {
	/// The left endpoint of `x - y ⋈ d`, as decision and scale, with any offset
	/// folded into [`Self::d`]. Not a claim that the decision is still
	/// unaliased once [`DifferenceLogicModel::add`] runs; that is
	/// [`DifferenceLogicModel::resolve_aliases`]'s job.
	x: (model::Decision<IntVal>, NonZero<IntVal>),
	/// The right endpoint of `x - y ⋈ d`, in the same shape as [`Self::x`].
	y: (model::Decision<IntVal>, NonZero<IntVal>),
	/// The bound in `x - y ⋈ d`.
	d: IntVal,
	/// The comparison in `x - y ⋈ d`.
	///
	/// An unreified [`LinComparator::Equal`] never reaches here: one endpoint
	/// is then a view of the other, which the model unifies while simplifying
	/// [`IntLinear`].
	comparator: LinComparator,
	/// The Boolean gating the constraint, if it is (half-)reified.
	reif: Option<Gate>,
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

/// The same shape as [`Reification`], but for a gate
/// [`DifferenceLogicConstraint::recognise`] has already confirmed is backed by
/// a genuine Boolean decision rather than a constant or a literal derived from
/// an integer comparison.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Gate {
	/// `b → x - y ⋈ d`.
	ImpliedBy(model::Decision<bool>),
	/// `b ↔ x - y ⋈ d`.
	ReifiedBy(model::Decision<bool>),
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
		for (i, b) in self.graph.borrow().bool_vars.iter().enumerate() {
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
		let mut graph = self.graph.borrow_mut();
		let n = data as usize;
		let mut enqueue = false;
		if matches!(event, IntEvent::LowerBound | IntEvent::Fixed) {
			enqueue = graph.notify_lb_change(ctx, n);
		}
		if matches!(event, IntEvent::UpperBound | IntEvent::Fixed) {
			enqueue |= graph.notify_ub_change(ctx, n);
		}
		enqueue
	}

	fn initialize(&mut self, ctx: &mut InitializationContext<'_>) {
		// All five of the paper's best configurations put bound propagation
		// lowest.
		ctx.set_priority(PriorityLevel::Lowest);
		for (i, n) in self.graph.borrow().int_vars.iter().enumerate() {
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
	/// decisions — a constant endpoint, or two views of one — which the linear
	/// propagator handles better, and which would otherwise bounce between the
	/// model and the graph (see [`DifferenceLogicModel::retain_edge`]).
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

		// Negating the already-negative term keeps both endpoints as the graph
		// names them; ordering by decision makes the pair term-order agnostic.
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
		let x_scale = x.scale();
		let (_, x_offset) = x.strip_offset();
		// A view whose negation overflows cannot be an endpoint; the linear
		// propagator reports the problem if there really is one.
		let y = Resolved(y.0.bounding_neg(prb).ok()?);
		let y_scale = y.scale();
		let (_, y_offset) = y.strip_offset();

		// `b ↔ x - y ≠ d` is `¬b ↔ x - y = d`, which is the form the graph
		// reduces.
		let (comparator, reif) = match (comparator, reif) {
			(LinComparator::NotEqual, Some(Reification::ReifiedBy(r))) => {
				(LinComparator::Equal, Some(Reification::ReifiedBy(!r)))
			}
			other => other,
		};
		// A constant, or a literal over an integer comparison, cannot gate an
		// edge; the linear propagator takes those.
		let reif = match reif {
			None => None,
			Some(Reification::ImpliedBy(b)) => Some(Gate::ImpliedBy(
				b.resolve_alias(prb).decision()?.into_inner(),
			)),
			Some(Reification::ReifiedBy(b)) => Some(Gate::ReifiedBy(
				b.resolve_alias(prb).decision()?.into_inner(),
			)),
		};
		Some(Self {
			x: (x_dec, x_scale),
			y: (y_dec, y_scale),
			d: rhs - x_offset - y_offset,
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
			// `x - y = d` needs no constraint: the model unifies the two views.
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
		IntVal,
		actions::{BoolInspectionActions, IntInspectionActions},
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

	/// Build a model of two difference constraints that force `x + 2 ≤ y` and
	/// `y + 3 ≤ z`, over the given domains.
	fn chain_model(bound: IntVal) -> (Model, [View<IntVal>; 3]) {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=bound);
		let y = prb.new_int_decision(0..=bound);
		let z = prb.new_int_decision(0..=bound);
		prb.linear(x - y).le(-2).post().unwrap();
		prb.linear(y - z).le(-3).post().unwrap();
		(prb, [x, y, z])
	}

	/// A model exercising every shape the graph can take: a plain edge, a
	/// half-reified edge, a reified edge, a half-reified equality, and a
	/// disequality.
	fn mixed_model(level: DifferenceLogicLevel) -> (Model, Vec<ModelView>) {
		mixed_model_configured(level, None)
	}

	/// [`mixed_model`] with the all-pairs budget spelled out.
	fn mixed_model_configured(
		level: DifferenceLogicLevel,
		budget: Option<usize>,
	) -> (Model, Vec<ModelView>) {
		let mut prb = Model::default();
		prb.set_difference_logic_level(level);
		prb.diff_logic_all_pairs_budget = budget;
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

	/// A graph too large to reduce skips the all-pairs pass, leaving no
	/// distance matrix. Everything consulting it must cope, and the solutions
	/// must not change: skipping costs strength, never correctness.
	#[test]
	fn test_difference_all_pairs_budget_exhausted() {
		let level = DifferenceLogicLevel::Inequality;
		let (prb, vars) = mixed_model_configured(level, None);
		let reduced = prb.solutions(&vars);
		assert!(!reduced.is_empty(), "the model should be satisfiable");

		// A budget of zero skips the pass whatever the graph looks like.
		let (prb, vars) = mixed_model_configured(level, Some(0));
		assert_eq!(prb.solutions(&vars), reduced);
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

	#[test]
	fn test_difference_chain_solutions() {
		let (prb, vars) = chain_model(5);
		prb.expect_solutions(
			&vars,
			expect![[r#"
			0, 2, 5"#]],
		);
	}

	/// A constraint that only becomes a difference constraint while being
	/// simplified must still reach the graph. Unifying the zero-length cycle is
	/// something only the graph does, so had the folded one stayed an
	/// [`IntLinear`] the two decisions would remain distinct.
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

		let (mut prb, _) = chain_model(10);
		let (slv, _): (Solver, _) = prb.lower().to_solver().unwrap();
		let graphs = diff_logic_graphs(&slv);
		assert_eq!(graphs.len(), 2, "both propagators are posted");
		assert!(Rc::ptr_eq(&graphs[0], &graphs[1]), "they share one graph");

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

		// A model without any difference constraint posts no propagators.
		let mut empty = Model::default();
		let x = empty.new_int_decision(0..=2);
		empty.linear(x).le(1).post().unwrap();
		let (slv, _): (Solver, _) = empty.lower().to_solver().unwrap();
		assert!(diff_logic_graphs(&slv).is_empty());
	}

	/// A half-reified edge constrains its endpoints exactly when its gate
	/// holds, and nothing otherwise.
	#[test]
	fn test_difference_implied_edge() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=2);
		let y = prb.new_int_decision(0..=2);
		let b = prb.new_bool_decision();
		prb.linear(x - y).le(-2).implied_by(b).post().unwrap();

		prb.expect_solutions(
			&[ModelView::from(x), y.into(), b.into()],
			expect![[r#"
			0, 0, false
			0, 1, false
			0, 2, false
			0, 2, true
			1, 0, false
			1, 1, false
			1, 2, false
			2, 0, false
			2, 1, false
			2, 2, false"#]],
		);
	}

	/// The same reduction, but for an *implied* edge: once it collapses to one
	/// decision, the bound it enforces must stay conditional on its gate.
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

	/// An edge posted after the graph has been analysed is still reduced: it
	/// closes a negative cycle with an implied edge, so that edge's gate cannot
	/// hold. Only the global analysis sees this — the bounds stay wide enough
	/// that the bound-based falsification check cannot.
	#[test]
	fn test_difference_late_edge_is_still_analysed() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		let p = prb.new_bool_decision();
		prb.linear(x - y).le(-10).implied_by(p).post().unwrap();
		// Analyses the graph while it holds only the implied edge.
		prb.propagate().unwrap();
		assert_eq!(p.val(&prb), None, "nothing decides `p` yet");

		// `y - x ≤ -20` and `p → x - y ≤ -10` cannot both hold.
		prb.linear(y - x).le(-20).post().unwrap();
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
		let edge = |x: View<IntVal>, y: View<IntVal>, rhs| IntLinear::<OverflowImpossible> {
			terms: vec![x, -y],
			rhs,
			reif: None,
			comparator: LinComparator::LessEq,
		};

		let first = prb.post_constraint(edge(a, b, 2)).unwrap();
		let second = prb.post_constraint(edge(b, c, 3)).unwrap();
		assert_eq!(first, second);

		// A constraint the graph does not capture keeps an identifier of its
		// own.
		let other = prb
			.post_constraint(IntLinear::<OverflowImpossible> {
				terms: vec![a, b, c],
				rhs: 12,
				reif: None,
				comparator: LinComparator::LessEq,
			})
			.unwrap();
		assert_ne!(other, first);
	}

	/// A constraint the graph consumed is still enforced when another tightens
	/// one of its endpoints later: the component subscribes to a node as the
	/// edge that created it is added, so a later bound change still wakes it.
	#[test]
	fn test_difference_propagates_a_later_external_bound() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=100);
		let y = prb.new_int_decision(0..=100);
		// Consumed by the graph, so nothing else in the model enforces it.
		prb.linear(x - y).le(-10).post().unwrap();
		prb.propagate().unwrap();

		// Tighten `y` from outside the graph, after the analysis has run.
		prb.linear(y * 1).le(20).post().unwrap();
		prb.propagate().unwrap();
		assert_eq!(x.max(&prb), 10);
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
		prb.linear(y * 1).le(20).post().unwrap();
		let conflict = prb
			.linear(x * -1)
			.le(-50)
			.post()
			.err()
			.or_else(|| prb.propagate().err());
		assert!(conflict.is_some(), "the graph must report the conflict");
	}

	/// Two terms of the same sign are still a difference constraint: one
	/// endpoint is simply a negated view.
	#[test]
	fn test_difference_same_sign_terms() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=3);
		let y = prb.new_int_decision(0..=3);
		prb.linear(x + y).le(2).post().unwrap();

		prb.expect_solutions(
			&[x, y],
			expect![[r#"
			0, 0
			0, 1
			0, 2
			1, 0
			1, 1
			2, 0"#]],
		);
	}

	/// A scaled view is a node of its own, so `2x - y ≤ 1` is an edge too.
	#[test]
	fn test_difference_scaled_terms() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=3);
		let y = prb.new_int_decision(0..=3);
		prb.linear(x * 2 - y).le(1).post().unwrap();

		prb.expect_solutions(
			&[x, y],
			expect![[r#"
			0, 0
			0, 1
			0, 2
			0, 3
			1, 1
			1, 2
			1, 3
			2, 3"#]],
		);
	}

	/// `x - y ≤ 0` and `y - x ≤ 0` is a cycle of length zero, so the two
	/// decisions must take the same value.
	#[test]
	fn test_difference_zero_cycle_unifies() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(0..=2);
		let y = prb.new_int_decision(0..=2);
		prb.linear(x - y).le(0).post().unwrap();
		prb.linear(y - x).le(0).post().unwrap();

		prb.expect_solutions(
			&[x, y],
			expect![[r#"
			0, 0
			1, 1
			2, 2"#]],
		);
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
