//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use std::{
	any::Any,
	collections::VecDeque,
	error::Error,
	fmt::{self, Debug, Display},
	marker::PhantomData,
	num::NonZeroI32,
};

use bon::Builder;
use itertools::Itertools;
use pindakaas::{
	ClauseDatabase, Lit as RawLit, Unsatisfiable,
	solver::{cadical::Cadical, propagation::ExternalPropagation},
};
use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;
use tracing::warn;

#[cfg(feature = "flatzinc")]
use crate::model::deserialize::flatzinc::{
	FlatZincError, FlatZincLowerData, FlatZincModelMeta, FlatZincSolverMeta,
};
use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, ConstructionActions, IntDecisionActions, IntInspectionActions,
		PostingActions, PropagationContext, ReasoningContext, ReasoningEngine, Trailed,
	},
	constraints::{
		BoxedConstraint, BoxedPropagator, Constraint, NO_REASON, Nogood,
		int_array_minimum::IntArrayMinimumBounds,
		int_div::IntDivBounds,
		int_linear::{IntEq, IntLinear, LinComparator},
		int_mul::IntMulBounds,
		int_pow::IntPowBounds,
	},
	helpers::{
		bytes::Bytes,
		overflow::{OverflowImpossible, OverflowMode, OverflowPossible},
	},
	model::{
		self, ConRef, Model,
		decision::{Tier, integer::Domain},
		deserialize::Goal,
		initilization_context::ModelInitContext,
		resolved::Resolved,
		view::integer::IntView,
	},
	solver::{
		self, IntLitMeaning, LiteralStrategy, Polarity, Solver, engine::Engine,
		view::boolean::BoolView,
	},
	views::LinearBoolView,
};

/// State of the breadth-first walk used to reconstruct the goal polarity in
/// [`GoalPolarity::process`].
#[derive(Debug, Default)]
struct GoalPolarity {
	/// The constraint currently being processed.
	current_con: Option<ConRef>,
	/// The queue of decisions still to be processed: the decision, the desired
	/// direction, and the constraint that enqueued it or `None` for the goal
	/// itself.
	queue: VecDeque<(Resolved<model::Decision<IntVal>>, Polarity, Option<ConRef>)>,
	/// The (decision, direction) pairs already enqueued.
	visited: FxHashSet<(Resolved<model::Decision<IntVal>>, Polarity)>,
}

/// Internal type to represent a complete [`Lowerer`] builder.
#[derive(Builder)]
#[builder(
	builder_type(
		name = Lowerer,
		vis = "pub",
		doc {
			/// A builder for the lowering process, which converts a high-level
			/// [`Model`] or a `FlatZinc` instance into a lower-level representation
			/// (typically a [`Solver`]).
			///
			/// This builder allows configuring various SAT solver options and preprocessing
			/// techniques before starting the lowering process.
		},
	),
	start_fn(name = builder_internal, vis = "pub(crate)"),
	finish_fn(name = finish_internal, vis = "")
)]
pub(crate) struct LowererComplete<Origin = ()> {
	/// A origin source from which the model was created, used to define wrapper
	/// methods for the lowering process.
	#[builder(start_fn)]
	origin: Origin,
	/// Whether to enable the globally blocked clause elimination (conditioning)
	#[builder(default = Lowerer::DEFAULT_CONDITIONING)]
	conditioning: bool,
	/// Whether to enable inprocessing in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_INPROCESSING)]
	inprocessing: bool,
	/// The maximum cardinality of the domain of an integer variable before its
	/// order encoding is created lazily.
	#[builder(default = Lowerer::DEFAULT_INT_EAGER_LIMIT)]
	int_eager_limit: usize,
	/// The number of preprocessing rounds in the SAT solver
	#[builder(default = Lowerer::DEFAULT_PREPROCESSING)]
	preprocessing: usize,
	/// Whether to enable CaDiCaL's light preprocessing.
	#[builder(default = Lowerer::DEFAULT_PREPROCESSING_LIGHT)]
	preprocessing_light: bool,
	/// Whether to enable the failed literal probing in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_PROBING)]
	probing: bool,
	/// The interval in terms of conflicts with the given `reduce_type` between
	/// clause-database reductions in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REDUCE_INTERVAL)]
	reduce_interval: usize,
	/// Type of method to compute the next size of the learned clause-database
	/// to trigger reduction in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REDUCE_TYPE)]
	reduce_type: ReduceType,
	/// Whether to enable restarts in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_RESTART)]
	restart: bool,
	/// Whether to enable the global forward subsumption in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_SUBSUMPTION)]
	subsumption: bool,
	/// Whether to enable asking reason eagerly in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REASON_EAGER)]
	reason_eager: bool,
	/// Whether to enable the bounded variable elimination in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_VARIABLE_ELIMINATION)]
	variable_elimination: bool,
	/// Whether to enable the vivification in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_VIVIFICATION)]
	vivification: bool,
	/// The (optional) intended objective, used to bias the polarity of the
	/// decision variables that compose it.
	///
	/// Use the [`positive_polarity`](Lowerer::positive_polarity) and
	/// [`negative_polarity`](Lowerer::negative_polarity) builder setters rather
	/// than setting this directly.
	objective: Option<Goal<model::View<IntVal>>>,
}

/// Actions that can be performed when reformulating a [`Model`] object into a
/// [`Solver`] object.
trait LoweringActions {
	/// Add a clause over Boolean views to the SAT solver.
	fn add_clause(
		&mut self,
		clause: Vec<solver::View<bool>>,
	) -> Result<(), Nogood<solver::Decision<bool>>>;

	/// Add a propagator to the solver.
	fn add_propagator(&mut self, propagator: BoxedPropagator);

	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn bool_val(&self, bv: solver::Decision<bool>) -> Option<bool>;

	/// Get the set of values from which the integer view is guaranteed to take
	/// a value.
	fn int_domain(&self, var: solver::Decision<IntVal>) -> IntSet;

	/// Check whether a given integer view can take a given value.
	fn int_in_domain(&self, var: solver::Decision<IntVal>, val: IntVal) -> bool;

	/// Get (or create) a literal for the given integer view with the given
	/// meaning.
	fn int_lit(
		&mut self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> solver::View<bool>;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` if it has no direct meaning.
	fn int_lit_meaning(
		&self,
		var: solver::Decision<IntVal>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning>;

	/// Get the maximum value that an integer view is guaranteed to take.
	fn int_max(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less than or equal to its current upper bound.
	fn int_max_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool>;

	/// Get the minimum value that an integer view is guaranteed to take.
	fn int_min(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater than or equal to its current lower bound.
	fn int_min_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool>;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn int_try_lit(
		&self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>>;

	/// Create a new trailed integer value that will be usable in the
	/// [`Solver`].
	fn new_trailed(&mut self, init: u64) -> Trailed<u64>;

	/// Create a fresh range of Boolean variables in the underlying SAT solver.
	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange;
}

/// Context object used during the lowering process that creates a
/// [`Solver`] object from a [`Model`].
pub struct LoweringContext<'a> {
	/// Actions that can be performed by the [`Solver`] object we are
	/// creating.
	///
	/// Note that this is not a [`Solver`] object itself, but rather a
	/// [`LoweringActions`] trait object to avoid generic parameters.
	slv: &'a mut dyn LoweringActions,
	/// The mapping from decision variables in the [`Model`] to the
	/// corresponding view in the [`Solver`].
	map: &'a LoweringMap,
	/// Error that captures the clause that caused methods to return
	/// [`Unsatisfiable`].
	pub(crate) error: Option<LoweringError>,
	/// The state of the trailed values in the source [`Model`] object.
	trail: &'a [[u8; 8]],
}

/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`Model`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringError {
	/// Error used when a conflict is found during the simplification process of
	/// the model.
	Simplification(Nogood<model::View<bool>>),
	/// Error used when a conflict is found by the SAT solver when lowering the
	/// problem.
	Lowering(Nogood<solver::Decision<bool>>),
}

/// A lowering helper that maps decisions in a [`Model`] object to the
/// [`solver::View`] that is used to represent it in a [`Solver`] object.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LoweringMap {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<solver::View<bool>>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<solver::View<IntVal>>,
}

/// Helper type to create a [`LoweringMap`] object.
///
/// This type is primarily meant to resolve the order of creation issue when
/// dealing with aliased variables.
pub(crate) struct LoweringMapBuilder {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<Option<solver::View<bool>>>,
	/// The (default) maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub(crate) int_eager_limit: usize,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<Option<solver::View<IntVal>>>,
}

/// The function CaDiCaL uses to compute the target size of the learned clause
/// database when it is reduced.
///
/// Each variant's discriminant is the integer value that is passed to CaDiCaL's
/// `reduceopt` option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReduceType {
	/// Percentage-based reduction target (CaDiCaL `reduceopt` value `0`).
	Percent = 0,
	/// Square-root-based reduction target (CaDiCaL `reduceopt` value `1`).
	Sqrt = 1,
	/// Logarithmic reduction target (CaDiCaL `reduceopt` value `2`).
	Log = 2,
}

impl GoalPolarity {
	/// Reconstruct the goal polarity (best-effort) from the intended
	/// optimization `goal`, recording objective-level evidence on the
	/// decisions that compose it.
	///
	/// Starting from the goal decision, it walks breadth-first over the
	/// constraints each visited decision is subscribed to (via
	/// [`Model::subscribed_constraints`]), recording the desired direction onto
	/// the other variables those constraints relate, which are in turn
	/// enqueued.
	///
	/// The relations considered are the (non-reified) linear (in)equalities and
	/// the monotone/antitone relationships of arithmetic constraints such as
	/// multiplication, division, exponentiation, and array minimum.
	fn process(
		model: &mut Model,
		constraints: &[Option<BoxedConstraint>],
		goal: Goal<model::View<IntVal>>,
	) {
		// Record the polarity of the objective itself, and seed the walk from
		// its underlying integer decision.
		let (obj, dir) = match goal {
			Goal::Maximize(obj) => (obj, Polarity::Positive),
			Goal::Minimize(obj) => (obj, Polarity::Negative),
		};
		model.observe_int_polarity(obj, Tier::Objective, dir);
		let IntView::Linear(lin) = obj.resolve_alias(model).into_inner().0 else {
			return;
		};
		let start = Resolved(lin.var);
		let start_dir = if lin.scale.get() < 0 { !dir } else { dir };
		let mut walk = GoalPolarity::default();
		let _ = walk.visited.insert((start.clone(), start_dir));
		walk.queue.push_back((start, start_dir, None));

		let mut con_refs: Vec<ConRef> = Vec::new();
		while let Some((input, input_polarity, discovering)) = walk.queue.pop_front() {
			// Collect the constraints the decision is involved in
			con_refs.clear();
			model.subscribed_constraints(input.0, |con| con_refs.push(con));
			con_refs.sort_unstable_by_key(|con| con.index());
			con_refs.dedup();
			for &con in &con_refs {
				// Never enqueue decisions from the constraint that enqueued this
				// decision
				if discovering == Some(con) {
					continue;
				}
				let Some(c) = constraints[con.index()].as_ref() else {
					continue;
				};
				let c: &dyn Constraint<Model> = c.as_ref();
				let c: &dyn Any = c;
				walk.current_con = Some(con);
				walk.process_constraint(model, c, &input, input_polarity);
			}
		}
	}

	/// Process the constraint `con` during the objective walk: derive the
	/// relations it implies and record the direction `input_polarity` of the
	/// visited decision `input` onto the other variables of those relations.
	fn process_constraint(
		&mut self,
		model: &mut Model,
		con: &dyn Any,
		input: &Resolved<model::Decision<IntVal>>,
		input_polarity: Polarity,
	) {
		/// Type alias to abbreviate the integer view type in the downcasts.
		type V = model::View<IntVal>;

		if let Some(lin) = con.downcast_ref::<IntLinear<OverflowImpossible>>() {
			if lin.reif.is_none() && lin.comparator != LinComparator::NotEqual {
				self.record_relation(model, &lin.terms, input, input_polarity);
			}
		} else if let Some(lin) = con.downcast_ref::<IntLinear<OverflowPossible>>() {
			if lin.reif.is_none() && lin.comparator != LinComparator::NotEqual {
				self.record_relation(model, &lin.terms, input, input_polarity);
			}
		} else if let Some(eq) = con.downcast_ref::<IntEq>() {
			// `a = b` expressed as the linear equality `a - b = 0`.
			self.record_relation(model, &[eq.vars[0], -eq.vars[1]], input, input_polarity);
		} else if let Some(mul) = con.downcast_ref::<IntMulBounds<OverflowImpossible, V, V, V>>() {
			self.record_mul(model, mul, input, input_polarity);
		} else if let Some(mul) = con.downcast_ref::<IntMulBounds<OverflowPossible, V, V, V>>() {
			self.record_mul(model, mul, input, input_polarity);
		} else if let Some(pow) = con.downcast_ref::<IntPowBounds<OverflowImpossible, V, V, V>>() {
			self.record_pow(model, pow, input, input_polarity);
		} else if let Some(pow) = con.downcast_ref::<IntPowBounds<OverflowPossible, V, V, V>>() {
			self.record_pow(model, pow, input, input_polarity);
		} else if let Some(div) = con.downcast_ref::<IntDivBounds<V, V, V>>() {
			self.record_div(model, div, input, input_polarity);
		} else if let Some(min) = con.downcast_ref::<IntArrayMinimumBounds<V, V>>() {
			// The minimum is monotone in every element of the array.
			for &el in &min.vars {
				self.record_relation(model, &[min.min, -el], input, input_polarity);
			}
		}
	}

	/// Record the polarity implied by `result = numerator / denominator` for
	/// the related variables of the visited decision.
	fn record_div(
		&mut self,
		model: &mut Model,
		div: &IntDivBounds<model::View<IntVal>, model::View<IntVal>, model::View<IntVal>>,
		input: &Resolved<model::Decision<IntVal>>,
		input_polarity: Polarity,
	) {
		// The denominator must be strictly positive or strictly negative for the
		// division to be monotone in either argument. The result follows the
		// numerator when the denominator is positive, and opposes it when the
		// denominator is negative.
		let (den_lb, den_ub) = div.denominator.bounds(model);
		if den_lb >= 1 {
			self.record_relation(model, &[div.result, -div.numerator], input, input_polarity);
		} else if den_ub <= -1 {
			self.record_relation(model, &[div.result, div.numerator], input, input_polarity);
		} else {
			return;
		}
		// Increasing the denominator moves the result toward zero, i.e. against
		// the sign of the numerator.
		let (num_lb, num_ub) = div.numerator.bounds(model);
		if num_lb >= 0 {
			self.record_relation(model, &[div.result, div.denominator], input, input_polarity);
		} else if num_ub <= 0 {
			self.record_relation(
				model,
				&[div.result, -div.denominator],
				input,
				input_polarity,
			);
		}
	}

	/// Record the polarity implied by `product = factor1 * factor2` for the
	/// related variables of the visited decision.
	///
	/// The product is monotone in a factor when the other factor is
	/// non-negative, and antitone when it is non-positive.
	fn record_mul<OM: OverflowMode>(
		&mut self,
		model: &mut Model,
		mul: &IntMulBounds<OM, model::View<IntVal>, model::View<IntVal>, model::View<IntVal>>,
		input: &Resolved<model::Decision<IntVal>>,
		input_polarity: Polarity,
	) {
		let (f2_lb, f2_ub) = mul.factor2.bounds(model);
		if f2_lb >= 0 {
			self.record_relation(model, &[mul.product, -mul.factor1], input, input_polarity);
		} else if f2_ub <= 0 {
			self.record_relation(model, &[mul.product, mul.factor1], input, input_polarity);
		}
		let (f1_lb, f1_ub) = mul.factor1.bounds(model);
		if f1_lb >= 0 {
			self.record_relation(model, &[mul.product, -mul.factor2], input, input_polarity);
		} else if f1_ub <= 0 {
			self.record_relation(model, &[mul.product, mul.factor2], input, input_polarity);
		}
	}

	/// Record the polarity implied by `result = base ^ exponent` for the
	/// related variables of the visited decision.
	fn record_pow<OM: OverflowMode>(
		&mut self,
		model: &mut Model,
		pow: &IntPowBounds<OM, model::View<IntVal>, model::View<IntVal>, model::View<IntVal>>,
		input: &Resolved<model::Decision<IntVal>>,
		input_polarity: Polarity,
	) {
		let (base_lb, base_ub) = pow.base.bounds(model);
		let (exp_lb, exp_ub) = pow.exponent.bounds(model);
		let fixed_exp = (exp_lb == exp_ub).then_some(exp_lb);

		// The result is monotone in the base for non-negative bases with
		// positive exponents, and for any fixed odd exponent; it is antitone in
		// the base for non-positive bases with a fixed even exponent.
		if (exp_lb >= 1 && base_lb >= 0) || fixed_exp.is_some_and(|k| k >= 1 && k % 2 == 1) {
			self.record_relation(model, &[pow.result, -pow.base], input, input_polarity);
		} else if base_ub <= 0 && fixed_exp.is_some_and(|k| k >= 2 && k % 2 == 0) {
			self.record_relation(model, &[pow.result, pow.base], input, input_polarity);
		}
		// The result is monotone in the exponent when the base is at least one.
		if base_lb >= 1 {
			self.record_relation(model, &[pow.result, -pow.exponent], input, input_polarity);
		}
	}

	/// Record the direction `input_polarity` of the visited decision `input`
	/// onto the other terms of a single relation, given as the terms of a
	/// linear equality (views with opposite coefficient signs are monotone,
	/// views with the same coefficient sign are antitone).
	///
	/// Every (non-`input`) term has a push recorded, so the score accumulates
	/// across all the relations that mention a decision. Integer decisions are
	/// additionally enqueued (once) so the walk continues through them.
	fn record_relation(
		&mut self,
		model: &mut Model,
		terms: &[model::View<IntVal>],
		input: &Resolved<model::Decision<IntVal>>,
		input_polarity: Polarity,
	) {
		// Whether `input`'s coefficient in this relation is negative.
		let Some(input_neg) =
			terms
				.iter()
				.find_map(|t| match t.resolve_alias(model).into_inner().0 {
					IntView::Linear(lin) if &Resolved(lin.var) == input => {
						Some(lin.scale.get() < 0)
					}
					_ => None,
				})
		else {
			return;
		};
		// To push `input` in `input_polarity`, the other terms must be pushed in
		// the opposite direction.
		let term_dir = if input_neg {
			input_polarity
		} else {
			!input_polarity
		};
		for &t in terms {
			match t.resolve_alias(model).into_inner().0 {
				IntView::Linear(lin) => {
					let w = Resolved(lin.var);
					if &w == input {
						continue;
					}
					model.observe_int_polarity(t, Tier::Objective, term_dir);
					// The direction wanted for `w` is `term_dir` folded by `w`'s scale.
					let w_dir = if lin.scale.get() < 0 {
						!term_dir
					} else {
						term_dir
					};
					if self.visited.insert((w.clone(), w_dir)) {
						self.queue.push_back((w, w_dir, self.current_con));
					}
				}
				// Boolean- and constant-backed terms are leaves of the walk.
				_ => model.observe_int_polarity(t, Tier::Objective, term_dir),
			}
		}
	}
}

impl Lowerer {
	/// The default value when [`conditioning`](Lowerer::conditioning) is not
	/// explicitly set.
	pub const DEFAULT_CONDITIONING: bool = false;
	/// The default value when [`inprocessing`](Lowerer::inprocessing) is not
	/// explicitly set.
	pub const DEFAULT_INPROCESSING: bool = false;
	/// The default value when [`int_eager_limit`](Lowerer::int_eager_limit) is
	/// not explicitly set.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;
	/// The default value when [`preprocessing`](Lowerer::preprocessing) is not
	/// explicitly set.
	pub const DEFAULT_PREPROCESSING: usize = 0;
	/// The default value when
	/// [`preprocessing_light`](Lowerer::preprocessing_light) is not explicitly
	/// set.
	pub const DEFAULT_PREPROCESSING_LIGHT: bool = false;
	/// The default value when [`probing`](Lowerer::probing) is not explicitly
	/// set.
	pub const DEFAULT_PROBING: bool = false;
	/// The default value when [`reason_eager`](Lowerer::reason_eager) is not
	/// explicitly set.
	pub const DEFAULT_REASON_EAGER: bool = false;
	/// The default value when [`reduce_interval`](Lowerer::reduce_interval) is
	/// not explicitly set.
	pub const DEFAULT_REDUCE_INTERVAL: usize = 100;
	/// The default value when [`reduce_type`](Lowerer::reduce_type) is not
	/// explicitly set.
	pub const DEFAULT_REDUCE_TYPE: ReduceType = ReduceType::Sqrt;
	/// The default value when [`restart`](Lowerer::restart) is not explicitly
	/// set.
	pub const DEFAULT_RESTART: bool = false;
	/// The default value when [`subsumption`](Lowerer::subsumption) is not
	/// explicitly set.
	pub const DEFAULT_SUBSUMPTION: bool = false;
	/// The default value when
	/// [`variable_elimination`](Lowerer::variable_elimination) is not
	/// explicitly set.
	pub const DEFAULT_VARIABLE_ELIMINATION: bool = false;
	/// The default value when [`vivification`](Lowerer::vivification) is not
	/// explicitly set.
	pub const DEFAULT_VIVIFICATION: bool = false;
}

impl<State: lowerer::State> Lowerer<&mut Model, State> {
	/// Lower the [`Model`] to a [`Solver`].
	///
	/// This method will simplify the model, create the mapping between model
	/// decisions and solver views, and then create the constraint data
	/// structures within the solver.
	pub fn to_solver<Sat>(self) -> Result<(Solver<Sat>, LoweringMap), LoweringError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
		State: lowerer::IsComplete,
	{
		self.finish_internal().into_solver_internal()
	}
}

impl<Origin, State: lowerer::State> Lowerer<Origin, State> {
	/// Indicate that the search should prefer smaller values for the given
	/// objective view (e.g. a minimization objective), biasing the polarity of
	/// the decision variables that compose it toward smaller values at
	/// objective priority.
	///
	/// This is mutually exclusive with
	/// [`positive_polarity`](Lowerer::positive_polarity): both set the same
	/// intended objective.
	pub fn negative_polarity(
		self,
		objective: model::View<IntVal>,
	) -> Lowerer<Origin, lowerer::SetObjective<State>>
	where
		State::Objective: lowerer::IsUnset,
	{
		self.objective(Goal::Minimize(objective))
	}

	/// Indicate that the search should prefer larger values for the given
	/// objective view (e.g. a maximization objective), biasing the polarity of
	/// the decision variables that compose it toward larger values at objective
	/// priority.
	///
	/// This is mutually exclusive with
	/// [`negative_polarity`](Lowerer::negative_polarity): both set the same
	/// intended objective.
	pub fn positive_polarity(
		self,
		objective: model::View<IntVal>,
	) -> Lowerer<Origin, lowerer::SetObjective<State>>
	where
		State::Objective: lowerer::IsUnset,
	{
		self.objective(Goal::Maximize(objective))
	}
}

#[cfg(feature = "flatzinc")]
impl<State: lowerer::State> Lowerer<Result<FlatZincLowerData, FlatZincError>, State> {
	/// Lower the [`FlatZinc`](flatzinc_serde::FlatZinc) instance to a
	/// [`Solver`].
	///
	/// This method will internally create a [`Model`] from the FlatZinc data
	/// and then lower that model to a [`Solver`].
	pub fn to_solver<Sat>(self) -> Result<(Solver<Sat>, FlatZincSolverMeta), FlatZincError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
	{
		let complete = self.finish_internal();
		let FlatZincLowerData { meta, mut model } = complete.origin?;

		let (mut slv, map) = LowererComplete {
			origin: &mut model,
			conditioning: complete.conditioning,
			inprocessing: complete.inprocessing,
			int_eager_limit: complete.int_eager_limit,
			preprocessing: complete.preprocessing,
			preprocessing_light: complete.preprocessing_light,
			probing: complete.probing,
			reduce_interval: complete.reduce_interval,
			reduce_type: complete.reduce_type,
			restart: complete.restart,
			subsumption: complete.subsumption,
			reason_eager: complete.reason_eager,
			variable_elimination: complete.variable_elimination,
			vivification: complete.vivification,
			// Use the parsed optimization goal to bias polarity, unless an
			// explicit objective was set on the builder.
			objective: complete.objective.or(meta.goal),
		}
		.into_solver_internal()?;
		if let Some(branching) = meta.branching {
			branching.to_solver(&mut slv, &map);
		}
		let names = meta
			.names
			.into_iter()
			.map(|(k, v)| (k, map.get_any(&mut slv, v)))
			.collect();
		let goal = meta.goal.map(|g| match g {
			Goal::Minimize(v) => Goal::Minimize(map.get(&mut slv, v)),
			Goal::Maximize(v) => Goal::Maximize(map.get(&mut slv, v)),
		});
		let assumptions = meta
			.assumptions
			.into_iter()
			.map(|(label, view)| (label, map.get(&mut slv, view)))
			.collect();
		Ok((
			slv,
			FlatZincSolverMeta {
				names,
				stats: meta.stats,
				goal,
				assumptions,
			},
		))
	}
}

#[cfg(feature = "flatzinc")]
impl Lowerer<Result<FlatZincLowerData, FlatZincError>, lowerer::Empty> {
	/// Lower the [`FlatZinc`](flatzinc_serde::FlatZinc) instance to a
	/// [`Model`] with accompanying [`FlatZincModelMeta`] data.
	pub fn to_model(self) -> Result<(Model, FlatZincModelMeta), FlatZincError> {
		self.origin.map(|data| (data.model, data.meta))
	}
}

impl LowererComplete<&mut Model> {
	/// Internal implementation for lowering a model to a solver.
	fn into_solver_internal<Sat>(self) -> Result<(Solver<Sat>, LoweringMap), LoweringError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
	{
		let LowererComplete {
			origin: model,
			conditioning,
			inprocessing,
			int_eager_limit,
			preprocessing,
			preprocessing_light,
			probing,
			reduce_interval,
			reduce_type,
			restart,
			subsumption,
			reason_eager,
			variable_elimination,
			vivification,
			objective,
		} = self;

		let mut slv = Solver::<Sat>::default();
		let any_slv: &mut dyn Any = &mut slv.sat;
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			// Set the solver options for preprocessing/inprocessing
			r.set_option("condition", conditioning as i32);
			r.set_option("elim", variable_elimination as i32);
			r.set_option("exteagerreasons", reason_eager as i32);
			r.set_option("inprocessing", inprocessing as i32);
			r.set_limit("preprocessing", preprocessing as i32);
			r.set_option("preprocesslight", preprocessing_light as i32);
			r.set_option("probe", probing as i32);
			r.set_option("reduceint", reduce_interval as i32);
			r.set_option("reduceopt", reduce_type as i32);
			r.set_option("subsume", subsumption as i32);
			r.set_option("vivify", vivification as i32);

			// Set the solver options for search configurations
			// Enable restart if the config is set to true or if there are no
			// user search heuristics are provided
			r.set_option("restart", restart as i32);
		} else {
			warn!(
				target: "solver",
				"ignore vivification and restart options for unknown solver"
			);
		}

		model.propagate()?;

		// Analyze each constraint to record its literal-encoding requirements
		// and polarity evidence onto the model's decision definitions, then
		// reconstruct the objective polarity. The constraints are temporarily
		// taken out of the model so the analyze stage can mutate the decision
		// definitions while iterating.
		let constraints = std::mem::take(&mut model.constraints);
		for (idx, c) in constraints.iter().enumerate() {
			if let Some(c) = c {
				let mut ctx = ModelInitContext::new(model, ConRef::new(idx));
				c.analyze(&mut ctx);
			}
		}
		if let Some(obj) = objective {
			GoalPolarity::process(model, &constraints, obj);
		}
		model.constraints = constraints;

		// Create the mapping between model decisions and solver views.
		let mut map_builder = LoweringMapBuilder {
			bool_map: vec![None; model.bool_vars.len()],
			int_eager_limit,
			int_map: vec![None; model.int_vars.len()],
		};

		// Ensure the creation of all integer variables.
		for (idx, _) in model.int_vars.iter().enumerate() {
			map_builder.get_or_create_int(model, &mut slv, model::Decision(idx as u32));
		}

		// Ensure the creation of all Boolean variables.
		for var in 1..=model.bool_vars.len() as u32 {
			let raw = RawLit::from_raw(NonZeroI32::new(var as i32).unwrap());
			map_builder.get_or_create_bool(model, &mut slv, model::Decision(raw).into());
		}

		// Finalize the reformulation map (all variables must be created by now)
		let map = map_builder.finalize();

		// Create constraint data structures within the solver
		let mut ctx = LoweringContext::new(&mut slv, &map, &model.trail);
		for c in model.constraints.iter().flatten() {
			c.to_solver(&mut ctx)?;
		}

		Ok((slv, map))
	}
}

impl<'a> LoweringContext<'a> {
	/// Add a new clause to the resulting [`Solver`].
	pub fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = impl Into<solver::View<bool>>>,
	) -> Result<(), LoweringError> {
		let clause: Result<Vec<_>, bool> = clause
			.into_iter()
			.filter_map(|lit| match lit.into().0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => Some(Err(true)),
				BoolView::Const(false) => None,
			})
			.collect();
		let clause = match clause {
			Err(false) => unreachable!(),
			Err(true) => return Ok(()),
			Ok(clause) if clause.is_empty() => {
				return Err(self.declare_conflict(NO_REASON).into());
			}
			Ok(clause) => clause,
		};
		debug_assert!(self.error.is_none());
		match self.add_clause_from_slice(&clause) {
			Err(Unsatisfiable) => Err(self.error.take().unwrap()),
			Ok(()) => Ok(()),
		}
	}

	/// Encode the given constraint into conjunctive normal form (CNF) using the
	/// given encoder, and add it to the resulting [`Solver`].
	pub fn cnf_encode<C, E>(&mut self, constraint: &C, encoder: &E) -> Result<(), LoweringError>
	where
		C: ?Sized,
		E: pindakaas::Encoder<Self, C> + ?Sized,
	{
		debug_assert!(self.error.is_none());
		let res = pindakaas::Encoder::encode(encoder, self, constraint);
		match res {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => Err(self.error.take().unwrap()),
		}
	}

	/// Declare a conflict with the given reason that was encountered during
	/// lowering.
	pub fn declare_conflict(
		&mut self,
		reason: impl FnOnce(&mut Self, &mut <Self as PropagationContext>::ReasonSink<'_>),
	) -> <Self as PropagationContext>::Conflict {
		let mut sink = Vec::new();
		reason(self, &mut sink);
		Nogood::from_solver_views(sink)
	}

	/// Read a trailed value from the [`Model`] trail.
	pub fn model_trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		T::from_bytes(self.trail[i.index as usize])
	}

	/// Create a lowering context for a solver, a mapping, and a trail snapshot.
	pub(crate) fn new<O: ExternalPropagation>(
		slv: &'a mut Solver<O>,
		map: &'a LoweringMap,
		trail: &'a [[u8; 8]],
	) -> Self {
		Self {
			slv,
			map,
			error: None,
			trail,
		}
	}

	/// Create a new Boolean decision for the [`Solver`].
	pub fn new_bool_decision(&mut self) -> solver::View<bool> {
		solver::Decision(self.slv.new_var_range(1).start().into()).into()
	}

	/// Map a [`model::View`] to its corresponding [`solver::View`].
	pub fn solver_view<T: solver::DefaultView + model::DefaultView>(
		&mut self,
		view: model::View<T>,
	) -> solver::View<T> {
		self.map.get(self.slv, view)
	}
}

impl ClauseDatabase for LoweringContext<'_> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		let clause = clause
			.iter()
			.map(|&l| solver::Decision(l).into())
			.collect_vec();

		match self.slv.add_clause(clause) {
			Ok(()) => Ok(()),
			Err(err) => {
				self.error = Some(err.into());
				Err(Unsatisfiable)
			}
		}
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.slv.new_var_range(len)
	}
}

impl ConstructionActions for LoweringContext<'_> {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		let bytes = init.to_bytes();
		let i = u64::from_bytes(bytes);
		let t = LoweringActions::new_trailed(self.slv, i);
		Trailed {
			index: t.index,
			ty: PhantomData,
		}
	}
}

impl Debug for LoweringContext<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let ptr: *const _ = &self.slv;
		f.debug_struct("LoweringContext")
			.field("slv", &ptr)
			.field("map", &self.map)
			.field("error", &self.error)
			.field("trail", &self.trail)
			.finish()
	}
}

impl PostingActions for LoweringContext<'_> {
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let clause = clause.into_iter().collect::<Vec<_>>();
		self.slv.add_clause(clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.slv.add_propagator(propagator);
	}
}

impl PropagationContext for LoweringContext<'_> {
	type Conflict = <Solver as PropagationContext>::Conflict;
	type ReasonSink<'a> = Vec<Self::Atom>;
}

impl ReasoningContext for LoweringContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
}

impl Display for LoweringError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Simplification(c) => {
				write!(f, "A conflict occurred during simplification: {c:?}")
			}
			Self::Lowering(e) => {
				write!(f, "An error occurred during solver conversion: {e:?}")
			}
		}
	}
}

impl Error for LoweringError {}

impl From<<Engine as ReasoningEngine>::Conflict> for LoweringError {
	fn from(value: <Engine as ReasoningEngine>::Conflict) -> Self {
		Self::Lowering(value.into_solver_nogood())
	}
}

impl From<<Model as ReasoningEngine>::Conflict> for LoweringError {
	fn from(value: <Model as ReasoningEngine>::Conflict) -> Self {
		Self::Simplification(value.into_model_nogood())
	}
}

impl From<Nogood<model::View<bool>>> for LoweringError {
	fn from(value: Nogood<model::View<bool>>) -> Self {
		Self::Simplification(value)
	}
}

impl From<Nogood<solver::Decision<bool>>> for LoweringError {
	fn from(value: Nogood<solver::Decision<bool>>) -> Self {
		Self::Lowering(value)
	}
}

impl LoweringMap {
	/// Lookup the [`solver::View`] to which the given model [`model::View`]
	/// maps.
	///
	/// Model views belong to the modelling layer. Use this method after
	/// [`Model::lower`](crate::model::Model::lower) to obtain the
	/// corresponding solver view before querying solution values.
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Status, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// let model_x = model.new_int_decision(1..=3);
	/// let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	///
	/// let solver_x = map.get(&mut solver, model_x);
	/// let status = solver
	/// 	.solve()
	/// 	.on_solution(|solution| {
	/// 		assert!((1..=3).contains(&solver_x.val(solution)));
	/// 	})
	/// 	.satisfy();
	/// assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn get<Ctx, T>(&self, ctx: &mut Ctx, view: model::View<T>) -> solver::View<T>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
		T: solver::DefaultView + model::DefaultView,
	{
		let any: &dyn Any = &view;
		if let Some(view) = any.downcast_ref::<model::View<bool>>() {
			let res: Box<dyn Any> = Box::new(self.get_bool(ctx, *view));
			let Ok(res) = res.downcast::<solver::View<T>>() else {
				unreachable!()
			};
			*res
		} else if let Some(view) = any.downcast_ref::<model::View<IntVal>>() {
			let res: Box<dyn Any> = Box::new(self.get_int(ctx, *view));
			let Ok(res) = res.downcast::<solver::View<T>>() else {
				unreachable!()
			};
			*res
		} else {
			unreachable!()
		}
	}

	/// Perform [`Self::get`] for the more general
	/// [`model::deserialize::AnyView`], resulting in a [`solver::AnyView`].
	///
	/// Note that it is generally recommended to use [`Self::get`] when
	/// possible. This method is generally only used when writing general
	/// purpose methods or in combination with deserialization.
	pub fn get_any<Ctx>(&self, ctx: &mut Ctx, view: model::deserialize::AnyView) -> solver::AnyView
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		match view {
			model::deserialize::AnyView::Bool(bv) => self.get_bool(ctx, bv).into(),
			model::deserialize::AnyView::Int(iv) => self.get_int(ctx, iv).into(),
		}
	}

	/// Internal method to which mapping `bool` variant views is dispatched.
	fn get_bool<Ctx>(&self, ctx: &mut Ctx, bv: model::View<bool>) -> solver::View<bool>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		use crate::model::view::boolean::BoolView::*;

		let int_lit = |slv: &mut Ctx, iv: model::Decision<IntVal>, lit_meaning: IntLitMeaning| {
			let iv = self.get_int(slv, model::View(IntView::Linear(iv.into())));
			iv.lit(slv, lit_meaning)
		};

		match bv.0 {
			Decision(l) => {
				let bv: solver::View<bool> = self.bool_map[l.idx()];
				if l.is_negated() { !bv } else { bv }
			}
			Const(c) => c.into(),
			IntEq(v, i) => int_lit(ctx, v, IntLitMeaning::Eq(i)),
			IntGreaterEq(v, i) => int_lit(ctx, v, IntLitMeaning::GreaterEq(i)),
			IntLess(v, i) => int_lit(ctx, v, IntLitMeaning::Less(i)),
			IntNotEq(v, i) => int_lit(ctx, v, IntLitMeaning::NotEq(i)),
		}
	}

	/// Lookup the solver [`IntView`] to which the given model [`int::IntView`]
	/// maps.
	fn get_int<Ctx>(&self, ctx: &mut Ctx, iv: model::View<IntVal>) -> solver::View<IntVal>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		use crate::model::view::integer::IntView::*;

		match iv.0 {
			Const(c) => (c).into(),
			Linear(lin) => self.int_map[lin.var.idx()] * lin.scale + lin.offset,
			Bool(lin) => {
				let bv = self.get_bool(ctx, lin.var);
				match bv.0 {
					BoolView::Lit(lit) => LinearBoolView::new(lin.scale, lin.offset, lit).into(),
					BoolView::Const(b) => lin.transform_val(b as IntVal).into(),
				}
			}
		}
	}
}

impl LoweringMapBuilder {
	/// Create the [`LoweringMap`] object ensuring that all variables have
	/// a representation in the [`Solver`].
	pub(crate) fn finalize(self) -> LoweringMap {
		LoweringMap {
			bool_map: self
				.bool_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
			int_map: self
				.int_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
		}
	}

	/// Get the representation of a Boolean decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (together with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_bool<Sat: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Sat>,
		bv: model::View<bool>,
	) -> solver::View<bool> {
		use crate::model::view::boolean::BoolView::*;

		match bv.0 {
			Decision(lit) => {
				let idx = lit.idx();
				if let Some(v) = self.bool_map[idx] {
					return if lit.is_negated() { !v } else { v };
				}
				let def = &model.bool_vars[idx];
				let view = match def.alias {
					Some(alias) => self.get_or_create_bool(model, slv, alias),
					None => {
						let dcn = slv.new_bool_decision();
						match def.polarity.resolve() {
							Some(Polarity::Positive) => slv.sat.phase(dcn.0),
							Some(Polarity::Negative) => slv.sat.phase(!dcn.0),
							None => {}
						};
						// Register the new solver literal based on a model Boolean
						// decision.
						tracing::trace!(
							target: "reverse_map",
							model = idx as u64,
							lit = i32::from(dcn.0),
							"register solver bool"
						);
						dcn.into()
					}
				};
				self.bool_map[idx] = Some(view);
				if lit.is_negated() { !view } else { view }
			}
			Const(b) => b.into(),
			IntEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::Eq(val))
			}
			IntGreaterEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::GreaterEq(val))
			}
			IntLess(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::Less(val))
			}
			IntNotEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::NotEq(val))
			}
		}
	}

	/// Get the representation of an integer decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (together with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_int<Sat: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Sat>,
		iv: model::Decision<IntVal>,
	) -> solver::View<IntVal> {
		use crate::model::view::integer::IntView::*;

		if let Some(v) = self.int_map[iv.idx()] {
			return v;
		}

		let r = iv.resolve_alias(model);
		let view = match r.into_inner().0 {
			Const(c) => c.into(),
			Linear(lin) => {
				let var = Resolved(lin.var);
				let base = match self.int_map[var.idx()] {
					Some(v) => v,
					None => {
						let def = &model.int_vars[var.idx()];
						let Domain::Domain(dom) = &def.domain else {
							unreachable!()
						};
						let direct_enc = if def.eager_direct {
							LiteralStrategy::Eager
						} else {
							LiteralStrategy::Lazy
						};
						let card = dom.card();
						let order_enc = if def.eager_order
							|| def.eager_direct || card.is_some()
							&& card.unwrap() <= self.int_eager_limit
						{
							LiteralStrategy::Eager
						} else {
							LiteralStrategy::Lazy
						};
						// Register solver integer decision based, before its
						// eager literals are created.
						match card {
							Some(1 | 2) => {}
							_ if tracing::enabled!(target: "reverse_map", tracing::Level::TRACE) => {
								let int_var = slv.engine.borrow().state.int_vars.len() as u64;
								tracing::trace!(
									target: "reverse_map",
									model = var.idx() as u64,
									int_var,
									"register solver int"
								);
							}
							_ => {}
						};
						let view = slv
							.new_int_decision(dom.clone())
							.order_literals(order_enc)
							.direct_literals(direct_enc)
							.maybe_polarity(def.polarity.resolve())
							.view();
						match view.0 {
							// Register solver Boolean decision used to represent a model integer
							// decision.
							solver::IntView::Bool(lin) if tracing::enabled!(target: "reverse_map", tracing::Level::TRACE) =>
							{
								tracing::trace!(
									target: "reverse_map",
									model = var.idx() as u64,
									lit = i32::from(lin.var.0),
									geq = lin.offset + lin.scale.get(),
									"register solver bool-backed int"
								);
							}
							_ => {}
						}
						self.int_map[var.idx()] = Some(view);
						view
					}
				};
				base * lin.scale + lin.offset
			}
			Bool(lin) => {
				let bv = self.get_or_create_bool(model, slv, lin.var);
				bv * lin.scale + lin.offset
			}
		};

		self.int_map[iv.idx()] = Some(view);
		view
	}
}

impl<Sat: ExternalPropagation> LoweringActions for Solver<Sat> {
	fn add_clause(
		&mut self,
		clause: Vec<solver::View<bool>>,
	) -> Result<(), <Solver as PropagationContext>::Conflict> {
		self.add_clause(clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.add_propagator(propagator, true);
	}

	fn bool_val(&self, bv: solver::Decision<bool>) -> Option<bool> {
		bv.val(self)
	}

	fn int_domain(&self, var: solver::Decision<IntVal>) -> IntSet {
		var.domain(self)
	}

	fn int_in_domain(&self, var: solver::Decision<IntVal>, val: IntVal) -> bool {
		var.in_domain(self, val)
	}

	fn int_lit(
		&mut self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> solver::View<bool> {
		var.lit(self, meaning)
	}

	fn int_lit_meaning(
		&self,
		var: solver::Decision<IntVal>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		var.lit_meaning(self, lit)
	}

	fn int_max(&self, var: solver::Decision<IntVal>) -> IntVal {
		var.max(self)
	}

	fn int_max_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool> {
		var.max_lit(self)
	}

	fn int_min(&self, var: solver::Decision<IntVal>) -> IntVal {
		var.min(self)
	}

	fn int_min_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool> {
		var.min_lit(self)
	}

	fn int_try_lit(
		&self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		var.try_lit(self, meaning)
	}

	fn new_trailed(&mut self, init: u64) -> Trailed<u64> {
		ConstructionActions::new_trailed(self, init)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.sat.new_var_range(len)
	}
}

impl PropagationContext for dyn LoweringActions + '_ {
	type Conflict = <Solver as PropagationContext>::Conflict;
	type ReasonSink<'a> = <Solver as PropagationContext>::ReasonSink<'a>;
}

impl ReasoningContext for dyn LoweringActions + '_ {
	type Atom = <Engine as ReasoningEngine>::Atom;
}

impl BoolInspectionActions<LoweringContext<'_>> for solver::Decision<bool> {
	fn val(&self, ctx: &LoweringContext<'_>) -> Option<bool> {
		ctx.slv.bool_val(*self)
	}
}

impl BoolInspectionActions<dyn LoweringActions + '_> for solver::Decision<bool> {
	fn val(&self, ctx: &dyn LoweringActions) -> Option<bool> {
		ctx.bool_val(*self)
	}
}

impl IntDecisionActions<LoweringContext<'_>> for solver::Decision<IntVal> {
	fn lit(&self, ctx: &mut LoweringContext<'_>, meaning: IntLitMeaning) -> solver::View<bool> {
		ctx.slv.int_lit(*self, meaning)
	}
}

impl IntDecisionActions<dyn LoweringActions + '_> for solver::Decision<IntVal> {
	fn lit(
		&self,
		ctx: &mut (dyn LoweringActions + '_),
		meaning: IntLitMeaning,
	) -> solver::View<bool> {
		ctx.int_lit(*self, meaning)
	}
}

impl IntInspectionActions<LoweringContext<'_>> for solver::Decision<IntVal> {
	fn bounds(&self, ctx: &LoweringContext<'_>) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &LoweringContext<'_>) -> IntSet {
		ctx.slv.int_domain(*self)
	}

	fn in_domain(&self, ctx: &LoweringContext<'_>, val: IntVal) -> bool {
		ctx.slv.int_in_domain(*self, val)
	}

	fn lit_meaning(
		&self,
		ctx: &LoweringContext<'_>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		ctx.slv.int_lit_meaning(*self, lit)
	}

	fn max(&self, ctx: &LoweringContext<'_>) -> IntVal {
		ctx.slv.int_max(*self)
	}

	fn max_lit(&self, ctx: &LoweringContext<'_>) -> solver::View<bool> {
		ctx.slv.int_max_lit(*self)
	}

	fn min(&self, ctx: &LoweringContext<'_>) -> IntVal {
		ctx.slv.int_min(*self)
	}

	fn min_lit(&self, ctx: &LoweringContext<'_>) -> solver::View<bool> {
		ctx.slv.int_min_lit(*self)
	}

	fn try_lit(
		&self,
		ctx: &LoweringContext<'_>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		ctx.slv.int_try_lit(*self, meaning)
	}

	fn val(&self, ctx: &LoweringContext<'_>) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

impl IntInspectionActions<dyn LoweringActions + '_> for solver::Decision<IntVal> {
	fn bounds(&self, ctx: &dyn LoweringActions) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &dyn LoweringActions) -> IntSet {
		ctx.int_domain(*self)
	}

	fn in_domain(&self, ctx: &dyn LoweringActions, val: IntVal) -> bool {
		ctx.int_in_domain(*self, val)
	}

	fn lit_meaning(
		&self,
		ctx: &dyn LoweringActions,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		ctx.int_lit_meaning(*self, lit)
	}

	fn max(&self, ctx: &dyn LoweringActions) -> IntVal {
		ctx.int_max(*self)
	}

	fn max_lit(&self, ctx: &dyn LoweringActions) -> solver::View<bool> {
		ctx.int_max_lit(*self)
	}

	fn min(&self, ctx: &dyn LoweringActions) -> IntVal {
		ctx.int_min(*self)
	}

	fn min_lit(&self, ctx: &dyn LoweringActions) -> solver::View<bool> {
		ctx.int_min_lit(*self)
	}

	fn try_lit(
		&self,
		ctx: &dyn LoweringActions,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		ctx.int_try_lit(*self, meaning)
	}

	fn val(&self, ctx: &dyn LoweringActions) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		IntVal,
		model::{
			Model, View,
			view::{boolean::BoolView, integer::IntView},
		},
		solver::{Polarity, Solver, Status, Valuation},
		views::LinearView,
	};

	/// Helper to find the model storage index of the integer decision backing
	/// the given (unscaled) model view.
	fn int_decision_index(v: View<IntVal>) -> usize {
		let IntView::Linear(LinearView { var, .. }) = v.0 else {
			panic!("expected a linear view")
		};
		var.idx()
	}

	/// `r -> (a + b <= 1)` is vacuously satisfied when `r` is false, so the
	/// constraint analysis prefers `r` to be false.
	#[test]
	fn polarity_halfreified_prefers_false() {
		let mut model = Model::default();
		let a = model.new_int_decision(0..=5);
		let b = model.new_int_decision(0..=5);
		let r = model.new_bool_decision();
		model.linear(a + b).le(1).implied_by(r).post().unwrap();

		let BoolView::Decision(l) = r.0 else {
			panic!("expected a Boolean decision view")
		};
		let ri = l.idx();
		let (_slv, _map): (Solver, _) = model.lower().to_solver().unwrap();
		assert_eq!(
			model.bool_vars[ri].polarity.resolve(),
			Some(Polarity::Negative)
		);
	}

	/// Minimizing `-x` should prefer larger `x`; the negative scale of the
	/// objective view must be folded so that `x` receives a positive polarity.
	#[test]
	fn polarity_objective_negative_scale() {
		let mut model = Model::default();
		let x = model.new_int_decision(1..=10);
		let (mut slv, map): (Solver, _) = model.lower().negative_polarity(-x).to_solver().unwrap();
		let sx = map.get(&mut slv, x);
		let mut found = None;
		let status = slv
			.solve()
			.on_solution(|sol| {
				found = Some(Valuation::val(&sx, sol));
			})
			.satisfy();
		assert_eq!(status, Status::Satisfied);
		assert_eq!(found, Some(10));
	}

	/// `a - b + c - x = 0` (relates x to a, b, c) and `d + e - c = 0` (relates
	/// c to d, e). Maximizing x (positive polarity) should prefer a, c, d and
	/// e large and b small, walking from x through c into d and e, and folding
	/// the negative coefficient of b. Posted as plain equalities (no
	/// `defines_var` / `.define()`) to exercise the variable-to-linear map on
	/// a user-built model.
	#[test]
	fn polarity_objective_recursive_reconstruction() {
		let mut model = Model::default();
		let a = model.new_int_decision(1..=5);
		let b = model.new_int_decision(1..=5);
		let c = model.new_int_decision(1..=8);
		let d = model.new_int_decision(1..=5);
		let e = model.new_int_decision(1..=5);
		let x = model.new_int_decision(-100..=100);
		model.linear(a - b + c - x).eq(0).post().unwrap();
		model.linear(d + e - c).eq(0).post().unwrap();

		// Resolve each view to its decision index before lowering borrows `model`.
		let idx = int_decision_index;
		let (ai, bi, ci, di, ei) = (idx(a), idx(b), idx(c), idx(d), idx(e));

		let (_slv, _map): (Solver, _) = model.lower().positive_polarity(x).to_solver().unwrap();

		let pol = |i: usize| model.int_vars[i].polarity.resolve();
		assert_eq!(pol(ai), Some(Polarity::Positive), "a");
		assert_eq!(pol(bi), Some(Polarity::Negative), "b");
		assert_eq!(pol(ci), Some(Polarity::Positive), "c");
		assert_eq!(pol(di), Some(Polarity::Positive), "d");
		assert_eq!(pol(ei), Some(Polarity::Positive), "e");
	}

	/// `a + b - z <= 0` (i.e. `a + b <= z`): increasing `a` or `b` forces
	/// `z` upward, so maximizing `z` prefers `a` and `b` large. Note that
	/// the objective-level signal dominates the constraint-level preference
	/// for smaller terms in the inequality.
	#[test]
	fn polarity_objective_through_leq() {
		let mut model = Model::default();
		let a = model.new_int_decision(1..=5);
		let b = model.new_int_decision(1..=5);
		let z = model.new_int_decision(1..=20);
		model.linear(a + b - z).le(0).post().unwrap();

		let (ai, bi) = (int_decision_index(a), int_decision_index(b));
		let (_slv, _map): (Solver, _) = model.lower().positive_polarity(z).to_solver().unwrap();

		let pol = |i: usize| model.int_vars[i].polarity.resolve();
		assert_eq!(pol(ai), Some(Polarity::Positive), "a");
		assert_eq!(pol(bi), Some(Polarity::Positive), "b");
	}

	/// `z = min(a, b)` is monotone in both elements of the array, so
	/// maximizing `z` prefers `a` and `b` large.
	#[test]
	fn polarity_objective_through_minimum() {
		let mut model = Model::default();
		let a = model.new_int_decision(1..=5);
		let b = model.new_int_decision(1..=5);
		let z = model.new_int_decision(1..=5);
		model.minimum(vec![a, b]).result(z).post().unwrap();

		let (ai, bi) = (int_decision_index(a), int_decision_index(b));
		let (_slv, _map): (Solver, _) = model.lower().positive_polarity(z).to_solver().unwrap();

		let pol = |i: usize| model.int_vars[i].polarity.resolve();
		assert_eq!(pol(ai), Some(Polarity::Positive), "a");
		assert_eq!(pol(bi), Some(Polarity::Positive), "b");
	}

	/// `m = a * b` with non-negative factors is monotone in both factors,
	/// so maximizing `m` prefers `a` and `b` large.
	#[test]
	fn polarity_objective_through_mul() {
		let mut model = Model::default();
		let a = model.new_int_decision(1..=5);
		let b = model.new_int_decision(1..=5);
		let m = model.new_int_decision(1..=25);
		model.mul(a, b).result(m).post().unwrap();

		let (ai, bi) = (int_decision_index(a), int_decision_index(b));
		let (_slv, _map): (Solver, _) = model.lower().positive_polarity(m).to_solver().unwrap();

		let pol = |i: usize| model.int_vars[i].polarity.resolve();
		assert_eq!(pol(ai), Some(Polarity::Positive), "a");
		assert_eq!(pol(bi), Some(Polarity::Positive), "b");
	}
}
