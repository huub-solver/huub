//! # Huub - A Modular and Maintainable Lazy Clause Generation Solver
//! Boolean variables and clauses.
//! Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and
//! maintainability in addition to speed. LCG solvers are a class of solvers
//! that can be used to solve decision and optimization problems. They are
//! characterized by their ability to dynamically add new Boolean variables and
//! clauses to a Boolean Satisfiability (SAT) solver during the search process.
//! This allows the solver exploit SAT solver's ability to learn from failures
//! during the search process, without having to encode the full problem into

#[macro_export]
/// General purpose helper for adding "relation" constraints to a Model.
///
/// Supported forms:
/// - `rel!(prb, const OP expr)` Use a constant left-hand side and an expression
///   right-hand side to build an integer linear comparison (e.g. `rel!(prb, 5
///   <= x + y)`).
/// - `rel!(prb, r -> ...)` or `rel!(prb, !r -> ...)` Post an integer linear
///   expression implied by (possibly negated) `r`.
/// - `rel!(prb, r <-> ...)` or `rel!(prb, !r <-> ...)` Post an integer linear
///   expression reified by (possibly negated) `r`.
macro_rules! rel {
	// Case for comparison operators where the left-hand side is a literal
	// and the right-hand side is an expression. Example:
	//   rel!(prb, 3 < x);
	($prb:expr, $lhs:literal $op:tt $rhs:expr) => {
		$prb.add_constraint(rel!(@make_lin $lhs $op $rhs))
	};
	// Implication: "r -> (lhs <op> rhs)".
	($prb:expr, $r:ident -> $lhs:literal $op:tt $rhs:expr) => {
		$prb.add_constraint(rel!(@make_lin $lhs $op $rhs).implied_by($r))
	};
	// Implication posting with a negated Boolean variable.
	($prb:expr, !$r:ident -> $lhs:literal $op:tt $rhs:expr) => {
		let neg = !($r);
		rel!($prb, neg -> $lhs $op $rhs);
	};
	// Fully reification: "r <-> (lhs <op> rhs)".
	($prb:expr, $r:ident <-> $lhs:literal $op:tt $rhs:expr) => {
		$prb.add_constraint(rel!(@make_lin $lhs $op $rhs).reified_by($r))
	};
	// Fully reification with a negated Boolean variable.
	($prb:expr, !$r:ident <-> $lhs:literal $op:tt $rhs:expr) => {
		let neg = !($r);
		rel!($prb, neg <-> $lhs $op $rhs);
	};
	// Internal helpers: dispatch to the appropriate comparison method.
	(@make_lin $lhs:literal < $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).gt($lhs)
	};
	(@make_lin $lhs:literal <= $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).geq($lhs)
	};
	(@make_lin $lhs:literal == $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).eq($lhs)
	};
	(@make_lin $lhs:literal != $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).ne($lhs)
	};
	(@make_lin $lhs:literal >= $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).leq($lhs)
	};
	(@make_lin $lhs:literal > $rhs:expr) => {
		$crate::IntLinExpr::from($rhs).lt($lhs)
	};
}

pub mod actions;
pub mod branchers;
pub mod constraints;
pub mod flatzinc;
pub(crate) mod helpers;
pub mod reformulate;
pub mod solver;
#[cfg(test)]
pub(crate) mod tests;
pub mod views;

use std::{
	any::Any,
	fmt::{Debug, Display},
	hash::Hash,
	iter::{Sum, repeat_n, repeat_with},
	mem,
	num::{NonZero, NonZeroI32},
	ops::{Add, AddAssign, Deref, Mul, Neg, Not, Sub},
};

use flatzinc_serde::FlatZinc;
use index_vec::{IndexVec, index_vec};
use itertools::Itertools;
pub use pindakaas::solver::TermSignal;
use pindakaas::{
	ClauseDatabase, ClauseDatabaseTools, Cnf, Lit as RawLit, Unsatisfiable, Var as RawVar,
	propositional_logic::Formula,
	solver::{cadical::Cadical, propagation::ExternalPropagation},
};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::warn;

use crate::{
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions,
		ConstructionActions, DecisionActions, InitActions, IntDecisionActions,
		IntExplanationActions, IntInitActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions, PropagationActions, ReasoningContext, ReasoningEngine,
		SimplificationActions, TrailingActions,
	},
	branchers::{BoolBrancher, IntBrancher, WarmStartBrancher},
	constraints::{
		BoxedConstraint, Conflict, Constraint, LazyReason, Reason, ReasonBuilder,
		SimplificationStatus,
		bool_array_element::BoolDecisionArrayElement,
		cumulative::CumulativeTimeTable,
		disjunctive_strict::{DisjunctiveStrict, DisjunctiveStrictPropagator},
		int_abs::IntAbsBounds,
		int_all_different::{IntAllDifferent, IntAllDifferentBounds},
		int_array_element::{IntArrayElementBounds, IntValArrayElement},
		int_array_minimum::IntArrayMinimumBounds,
		int_div::IntDivBounds,
		int_in_set::IntInSetReif,
		int_linear::{IntEq, IntLinear, LinOperator},
		int_pow::IntPowBounds,
		int_table::IntTable,
		int_times::IntTimesBounds,
		int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
	},
	flatzinc::{FlatZincError, FlatZincStatistics, FznModelBuilder},
	reformulate::{
		BoolDecisionDef, BoolDecisionInner, Domain, InitConfig, IntDecisionDef, IntDecisionIndex,
		IntDecisionInner, ReformulationContext, ReformulationError, ReformulationMap,
		ReformulationMapBuilder,
	},
	solver::{
		IntLitMeaning, Solver,
		activation_list::{ActivationAction, IntEvent, IntPropCond},
		queue::{PriorityLevel, PropagatorInfo, PropagatorQueue},
		trail::TrailedInt,
	},
	views::{LinearBoolView, LinearView},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A reference to a Boolean decision in the [`Model`].
///
/// Note that decisions only represent where the decision is kept
pub struct BoolDecision(BoolDecisionInner);

/// Type alias for the type used to represent propositional logic formulas that
/// can be used in [`Model`].
pub type BoolFormula = Formula<BoolDecision>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Strategy for making a search decisions to be added to a [`Model`].
///
/// Note that a [`Branching`] might be ignored (or used as only a suggestion) in
/// [`Solver`] depending on the configuration.
pub enum Branching {
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// Boolean decision variable, and then set its value by using the
	/// [`ValueSelection`].
	Bool(Vec<BoolDecision>, VariableSelection, ValueSelection),
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// integer decision variable, and then limit the domain of the variable by
	/// using the [`ValueSelection`].
	Int(Vec<IntDecision>, VariableSelection, ValueSelection),
	/// Search by sequentially applying the given branching strategies.
	Seq(Vec<Branching>),
	/// Search by enforcing the given Boolean expressions, but abandon the
	/// search when finding a conflict.
	WarmStart(Vec<BoolDecision>),
}

/// Type alias for a disjunction of literals (clause), used for internal type
/// documentation.
type Clause<L = RawLit> = Vec<L>;

/// Type alias for a conjunction of literals (clause), used for internal type
/// documentation.
type Conjunction<L = RawLit> = Vec<L>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Reference to a decision in a [`Model`].
pub enum Decision {
	/// Reference to a Boolean decision.
	Bool(BoolDecision),
	/// Reference to an integer decision.
	Int(IntDecision),
}

/// Helper trait used to create array element constraints for on collections of
/// different types.
pub trait ElementConstraint: Sized {
	/// The constraint type created and to be added to a [`Model`].
	type Constraint;
	/// The decision variable type to contain the selected element.
	type Result;

	/// Create a constraint that enforces that the `result` decision variables
	/// takes the same value as `array[index]`.
	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: IntDecision,
		result: Self::Result,
	) -> &mut Self::Constraint;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A reference to an integer value or its transformation in a [`Model`].
pub struct IntDecision(IntDecisionInner);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Object to help with the creation of integer linear constriants.
///
/// This object is generally created when [`IntExpr`] objects are added
/// together. Calling methods like [`Self::less_than`] or [`Self::equal_to`]
/// will create a [`IntLinear`] constriant object that can be added to a
/// [`Model`] object.
pub struct IntLinExpr {
	/// The (linear transformation of) integer decision variables that are added
	/// together.
	terms: Vec<IntDecision>,
}

/// Type alias for a set of integers parameter value.
pub type IntSetVal = RangeList<IntVal>;

/// Type alias for an parameter integer value.
pub type IntVal = i64;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Definition of how a constraint has requested to be advised at the model
/// level.
struct ModAdvisorDef {
	/// Reference to the constraint that has requested to be advised.
	con: ConRef,
	/// The data associated by the constraint with the advisor.
	data: u64,
	/// Whether lower and upper bound events must be swapped.
	negated: bool,
	/// Whether the advise on a Boolean must be advised as an integer event.
	bool2int: bool,
	/// The condition on the integer decision variable that must be decided
	/// before the constraint is advised.
	condition: Option<IntLitMeaning>,
}

#[derive(Clone, Debug, Default)]
/// A formulation of a problem instance in terms of decisions and constraints.
pub struct Model {
	/// A base [`Cnf`] object that contains pure Boolean parts of the problem.
	pub(crate) cnf: Cnf,
	/// An list of branching strategies that will be used by created [`Solver`]
	/// instances to be used in order to make search decisions.
	branchings: Vec<Branching>,
	/// A list of constraints that have been added to the model.
	constraints: IndexVec<ConRef, Option<BoxedConstraint>>,
	/// The definitions of the Boolean variables that have been created.
	bool_vars: Vec<BoolDecisionDef>,
	/// The definitions of the integer variables that have been created.
	int_vars: IndexVec<IntDecisionIndex, IntDecisionDef>,
	/// A queue of constraints that need to be propagated.
	propagator_queue: PropagatorQueue<ConRef>,
	/// Fake trailed storage
	trail: IndexVec<TrailedInt, IntVal>,
	/// Reference for the current propagator being executed.
	cur_prop: Option<ConRef>,
	/// Integer variable changes that occurred during the execution of the
	/// current propagator.
	int_events: FxHashMap<IntDecisionIndex, IntEvent>,
	/// Boolean variable changes that occurred during the execution of the
	/// current propagator.
	bool_events: Vec<RawVar>,

	/// Definitions of the advisors that are listening to the certain changes.
	advisors: IndexVec<ModAdvisor, ModAdvisorDef>,
}

#[derive(Debug)]
/// Wrapper around [`Model`] that knows the constraint being
/// initialized.
pub struct ModelInitContext<'a> {
	/// Index of the constraint being initialized.
	con: ConRef,
	/// Reference to the Model in which the constraint exists.
	model: &'a mut Model,
	/// The priority level at which the constraint will be enqueued.
	priority: PriorityLevel,
	/// Whether the subscriptions of the propagator would suggest the propagator
	/// should be enqueued.
	semantic_enqueue: bool,
	/// Whether the propagator explicitly requested to be enqueued or not
	/// enqueued.
	decision_enqueue: Option<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Strategy for limiting the domain of a selected decision variable as part of
/// a [`Branching`].
pub enum ValueSelection {
	/// Set the decision variable to its current lower bound value.
	IndomainMax,
	/// Set the decision variable to its current upper bound value.
	IndomainMin,
	/// Exclude the current upper bound value from the domain of the decision
	/// variable.
	OutdomainMax,
	/// Exclude the current lower bound value from the domain of the decision
	/// variable.
	OutdomainMin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Strategy of selecting the next decision variable from a list to make a
/// [`Branching`].
pub enum VariableSelection {
	/// Select the unfixed decision variable with the largest remaining domain
	/// size, using the order of the variables in case of a tie.
	AntiFirstFail,
	/// Select the unfixed decision variable with the smallest remaining domain
	/// size, using the order of the variables in case of a tie.
	FirstFail,
	/// Select the first unfixed decision variable in the list.
	InputOrder,
	/// Select the unfixed decision variable with the largest upper bound, using
	/// the order of the variables in case of a tie.
	Largest,
	/// Select the unfixed decision variable with the smallest lower bound,
	/// using the order of the variables in case of a tie.
	Smallest,
}

/// Create a constraint that enforces that the second integer decision variable
/// takes the absolute value of the first integer decision variable.
pub fn abs_int(prb: &mut Model, origin: IntDecision, abs: IntDecision) {
	prb.add_constraint(IntAbsBounds {
		origin,
		abs,
		origin_positive: origin.geq(0),
	});
}

/// Create a constraint that enforces that all the given integer decisions take
/// different values.
pub fn all_different_int<Iter>(prb: &mut Model, vars: Iter) -> &mut IntAllDifferent
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	prb.add_constraint(IntAllDifferent {
		prop: IntAllDifferentBounds::new(vars.into_iter().map_into().collect()),
		bounds_prop: None,
		value_prop: None,
	})
}

/// Create a constraint that enforces that a result decision variable takes the
/// value equal the element of the given array at the given index decision
/// variable.
pub fn array_element<E: ElementConstraint>(
	prb: &mut Model,
	array: Vec<E>,
	index: IntDecision,
	result: <E as ElementConstraint>::Result,
) -> &mut <E as ElementConstraint>::Constraint {
	<E as ElementConstraint>::element_constraint(prb, array, index, result)
}

/// Create a constraint that enforces that an integer decision variable takes
/// the minimum value of an array of integer decision variables.
pub fn array_maximum_int<Iter>(prb: &mut Model, vars: Iter, max: IntDecision)
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	array_minimum_int(prb, vars.into_iter().map(|v| -v.into()), -max);
}

/// Create a constraint that enforces that an integer decision variable takes
/// the minimum value of an array of integer decision variables.
pub fn array_minimum_int<Iter>(prb: &mut Model, vars: Iter, min: IntDecision)
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	prb.add_constraint(IntArrayMinimumBounds {
		vars: vars.into_iter().map_into().collect(),
		min,
	});
}

/// Create a constraint that enforces that the given a list of integer decision
/// variables representing the start times of tasks, a list of integer values
/// representing the durations of tasks, a list of integer values representing
/// the resource usages of tasks, and a resource capacity, the sum of the
/// resource usages of all tasks running at any time does not exceed the
/// resource capacity.
pub fn cumulative(
	prb: &mut Model,
	start_times: Vec<IntDecision>,
	durations: Vec<IntDecision>,
	usages: Vec<IntDecision>,
	capacity: IntDecision,
) {
	assert_eq!(
		start_times.len(),
		durations.len(),
		"cumulative must be given the same number of start times and durations."
	);
	assert_eq!(
		start_times.len(),
		usages.len(),
		"cumulative must be given the same number of start times and usages."
	);
	prb.add_constraint(CumulativeTimeTable::new(
		start_times,
		durations,
		usages,
		capacity,
	));
}

/// Create a constraint that enforces that the given a list of integer decision
/// variables representing the start times of tasks and a list of integer values
/// representing the durations of tasks, the tasks do not overlap in time.
pub fn disjunctive_strict(
	prb: &mut Model,
	start_times: Vec<IntDecision>,
	durations: Vec<IntVal>,
) -> &mut DisjunctiveStrict {
	assert_eq!(
		start_times.len(),
		durations.len(),
		"disjunctive_strict must be given the same number of start times and durations."
	);
	assert!(
		durations.iter().all(|&dur| dur >= 0),
		"disjunctive_strict cannot be given any negative durations."
	);
	let propagator =
		DisjunctiveStrictPropagator::new(prb, start_times, durations, true, true, true);
	prb.add_constraint(DisjunctiveStrict {
		propagator,
		edge_finding_prop: None,
		not_last_prop: None,
		detectable_precedence_prop: None,
	})
}

/// Create a constraint that enforces that a numerator decision integer variable
/// divided by a denominator integer decision variable is equal to a result
/// integer decision variable.
pub fn div_int(
	prb: &mut Model,
	numerator: IntDecision,
	denominator: IntDecision,
	result: IntDecision,
) {
	prb.add_constraint(IntDivBounds {
		numerator,
		denominator,
		result,
	});
}

/// Create constraint that enforces that the given Boolean variable takes the
/// value `true` if-and-only-if an integer variable is in a given set.
pub fn int_in_set_reif(prb: &mut Model, var: IntDecision, set: IntSetVal, reif: BoolDecision) {
	prb.add_constraint(IntInSetReif { var, set, reif });
}

/// Create a constraint that enforces that a base integer decision variable
/// exponentiation by an exponent integer decision variable is equal to a result
/// integer decision variable.
pub fn pow_int(prb: &mut Model, base: IntDecision, exponent: IntDecision, result: IntDecision) {
	prb.add_constraint(IntPowBounds {
		base,
		exponent,
		result,
	});
}

/// Create a sequential precede chain constraint that enforces that any integer
/// value `i`, larger than one, will only occur in a position after the first
/// occurrence of `i-1`.
pub fn seq_precede_chain_int<It>(prb: &mut Model, vars: impl IntoIterator<Item = It>)
where
	It: Into<IntDecision>,
{
	let con = IntSeqPrecedeChainBounds::new(prb, vars.into_iter().map_into().collect());
	prb.add_constraint(con);
}

/// Create a `table_int` constraint that enforces that given list of integer
/// views take their values according to one of the given lists of integer
/// values.
pub fn table_int(prb: &mut Model, vars: Vec<IntDecision>, table: Vec<Vec<IntVal>>) {
	assert!(
		table.iter().all(|tup| tup.len() == vars.len()),
		"The number of
values in each row of the table must be equal to the number of decision
variables."
	);
	prb.add_constraint(IntTable { vars, table });
}

/// Create a constraint that enforces that the product of the two integer
/// decision variables is equal to a third.
pub fn times_int(
	prb: &mut Model,
	factor1: IntDecision,
	factor2: IntDecision,
	product: IntDecision,
) {
	prb.add_constraint(IntTimesBounds {
		factor1,
		factor2,
		product,
	});
}

/// Create a value precede chain constraint that enforces that the first
/// occurrence of each value in `values` among the decisions `vars` happens in
/// the order of `values.
///
/// Note that `seq_precede_chain_int` is a special case of this constraint where
/// the values are consecutive integers starting from 1.
pub fn value_precede_chain_int<D, V>(
	prb: &mut Model,
	vars: impl IntoIterator<Item = D>,
	values: impl IntoIterator<Item = V>,
) where
	D: Into<IntDecision>,
	V: Into<IntVal>,
{
	let con = IntValuePrecedeChainValue::new(
		prb,
		values.into_iter().map_into().collect(),
		vars.into_iter().map_into().collect(),
	);
	prb.add_constraint(con);
}

impl BoolDecision {
	/// Resolve any aliasing in the BoolDecision, ensuring the result is a
	/// BoolDecision that if it is a `Lit`, then it is not an alias.
	fn resolve_alias(self, model: &Model) -> Self {
		use BoolDecisionInner::*;

		let mut result = self;
		// If the current Lit is an alias, then resolve it.
		while let Lit(lit) = result.0 {
			if let Some(alias) = model.bool_vars[i32::from(lit.var()) as usize - 1].alias {
				debug_assert_ne!(alias, result);
				debug_assert_ne!(alias, !result);
				result = if lit.is_negated() { !alias } else { alias };
			} else {
				break;
			}
		}
		// If the current Lit is a integer view, check whether it is already fixed.
		match result.0 {
			IntEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return BoolDecision(Const(false));
				} else if val == lb && val == ub {
					return BoolDecision(Const(true));
				}
			}
			IntGreaterEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if lb >= val {
					return BoolDecision(Const(true));
				} else if ub < val {
					return BoolDecision(Const(false));
				}
			}
			IntLess(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if ub < val {
					return BoolDecision(Const(true));
				} else if lb >= val {
					return BoolDecision(Const(false));
				}
			}
			IntNotEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return BoolDecision(Const(true));
				} else if val == lb && val == ub {
					return BoolDecision(Const(false));
				}
			}
			_ => {}
		}
		result
	}
}

impl Add<IntVal> for BoolDecision {
	type Output = IntDecision;

	fn add(self, rhs: IntVal) -> Self::Output {
		let me: IntDecision = self.into();
		me + rhs
	}
}

impl BoolInitActions<ModelInitContext<'_>> for BoolDecision {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		let var = self.resolve_alias(ctx.model);
		let (iv, cond, event) = match var.0 {
			BoolDecisionInner::Lit(lit) => {
				let adv = ctx.model.advisors.push(ModAdvisorDef {
					con: ctx.con,
					data,
					negated: false,
					bool2int: false,
					condition: None,
				});
				ctx.model.bool_vars[i32::from(lit.var()) as usize - 1]
					.constraints
					.push(ActivationAction::Advise(adv).into());
				return;
			}
			BoolDecisionInner::Const(_) => {
				// Value does not change, so no advisor will ever be called
				return;
			}
			BoolDecisionInner::IntEq(iv, v) => (iv, IntLitMeaning::Eq(v), IntPropCond::Domain),
			BoolDecisionInner::IntGreaterEq(iv, v) => {
				(iv, IntLitMeaning::GreaterEq(v), IntPropCond::Bounds)
			}
			BoolDecisionInner::IntLess(iv, v) => (iv, IntLitMeaning::Less(v), IntPropCond::Bounds),
			BoolDecisionInner::IntNotEq(iv, v) => {
				(iv, IntLitMeaning::NotEq(v), IntPropCond::Domain)
			}
		};
		let adv = ctx.model.advisors.push(ModAdvisorDef {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: Some(cond),
		});
		ctx.model.int_vars[iv]
			.constraints
			.add(ActivationAction::Advise(adv), event);
	}
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		let var = self.resolve_alias(ctx.model);
		match var.0 {
			BoolDecisionInner::Lit(lit) => ctx.model.bool_vars[i32::from(lit.var()) as usize - 1]
				.constraints
				.push(ActivationAction::Enqueue(ctx.con).into()),
			BoolDecisionInner::Const(_) => ctx.semantic_enqueue = true,
			// TODO: These definitions might enqueue when the boolean is not fixed. Use advisors
			// instead?
			BoolDecisionInner::IntEq(iv, _) | BoolDecisionInner::IntNotEq(iv, _) => {
				iv.enqueue_when(ctx, IntPropCond::Domain);
			}
			BoolDecisionInner::IntGreaterEq(iv, _) | BoolDecisionInner::IntLess(iv, _) => {
				iv.enqueue_when(ctx, IntPropCond::Bounds);
			}
		}
	}
}

impl BoolInspectionActions<Model> for BoolDecision {
	fn val(&self, ctx: &Model) -> Option<bool> {
		use BoolDecisionInner::*;

		let b = self.resolve_alias(ctx);
		match b.0 {
			Const(b) => Some(b),
			_ => None,
		}
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for BoolDecision {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl BoolPropagationActions<Model> for BoolDecision {
	fn set(
		&self,
		ctx: &mut Model,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		use BoolDecisionInner::*;

		let var = self.resolve_alias(ctx);
		match var.0 {
			Lit(l) => {
				let var = i32::from(l.var()) as usize - 1;
				let def = &mut ctx.bool_vars[var];
				debug_assert!(def.alias.is_none());
				def.alias = Some(BoolDecision(Const(!l.is_negated())));
				ctx.bool_events.push(l.var());
				Ok(())
			}
			Const(c) => c.set(ctx, reason),
			IntEq(iv, val) => {
				IntDecision(IntDecisionInner::Linear(iv.into())).set_val(ctx, val, reason)
			}
			IntGreaterEq(iv, val) => {
				IntDecision(IntDecisionInner::Linear(iv.into())).set_lower_bound(ctx, val, reason)
			}
			IntLess(iv, val) => IntDecision(IntDecisionInner::Linear(iv.into())).set_upper_bound(
				ctx,
				val - 1,
				reason,
			),
			IntNotEq(iv, val) => {
				IntDecision(IntDecisionInner::Linear(iv.into())).set_not_eq(ctx, val, reason)
			}
		}
	}

	fn set_val(
		&self,
		ctx: &mut Model,
		val: bool,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		let lit = if val { *self } else { !*self };
		lit.set(ctx, reason)
	}
}

impl BoolSimplificationActions<Model> for BoolDecision {
	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Conflict<BoolDecision>> {
		use BoolDecisionInner::*;

		let x = self.resolve_alias(ctx);
		let y = other.into().resolve_alias(ctx);

		match (x.0, y.0) {
			(x, y) if x == y => Ok(()),
			(Lit(xl), Lit(yl)) if xl.var() == yl.var() => Err(ctx.declare_conflict([x, y])),
			(Const(x), Const(y)) if x != y => Err(ctx.declare_conflict([])),
			(x, Const(b)) | (Const(b), x) => BoolDecision(x).set_val(ctx, b, []),
			(Lit(x), y) | (y, Lit(x)) => {
				let (x, y) = if let Lit(y) = y {
					if x.var() > y.var() {
						(x, BoolDecision(Lit(y)))
					} else {
						(y, BoolDecision(Lit(x)))
					}
				} else {
					(x, BoolDecision(y))
				};
				let store = &mut ctx.bool_vars[i32::from(x.var()) as usize - 1];
				debug_assert_eq!(store.alias, None);
				let idx = i32::from(x.var()) as usize - 1;
				ctx.bool_vars[idx].alias = Some(if x.is_negated() { !y } else { y });

				// Move subscriptions from aliased variable to the new primary variable
				let constraints = mem::take(&mut ctx.bool_vars[idx].constraints);
				match y.0 {
					// Move subscriptions to another Boolean decision
					Lit(lit) => {
						let jdx = i32::from(lit.var()) as usize - 1;
						ctx.bool_vars[jdx].constraints.extend(constraints);
					}
					// Move subscriptions to an integer decision
					IntEq(j, _) | IntGreaterEq(j, _) | IntLess(j, _) | IntNotEq(j, _) => {
						for act in constraints {
							let event = if matches!(y.0, IntEq(_, _) | IntNotEq(_, _)) {
								IntPropCond::Domain
							} else {
								IntPropCond::Bounds
							};
							match ActivationAction::<ModAdvisor, ConRef>::from(act) {
								ActivationAction::Advise(adv) => {
									let def: &mut ModAdvisorDef = &mut ctx.advisors[adv];
									def.condition = Some(match y.0 {
										IntEq(_, v) => IntLitMeaning::Eq(v),
										IntGreaterEq(_, v) => IntLitMeaning::GreaterEq(v),
										IntLess(_, v) => IntLitMeaning::Less(v),
										IntNotEq(_, v) => IntLitMeaning::NotEq(v),
										_ => unreachable!(),
									});
									ctx.int_vars[j]
										.constraints
										.add(ActivationAction::Advise(adv), event);
								}
								me @ ActivationAction::Enqueue(_) => {
									// TODO: This triggers even when the Boolean Condition does not
									// change value
									ctx.int_vars[j].constraints.add(me, event);
								}
							}
						}
					}
					Const(_) => unreachable!(),
				};
				Ok(())
			}
			(x, y) => {
				let x = BoolFormula::Atom(BoolDecision(x));
				let y = BoolFormula::Atom(BoolDecision(y));

				ctx.add_constraint(BoolFormula::Equiv(vec![x, y]));
				Ok(())
			}
		}
	}
}

impl ElementConstraint for BoolDecision {
	type Constraint = BoolDecisionArrayElement;
	type Result = BoolDecision;

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: IntDecision,
		result: Self::Result,
	) -> &mut Self::Constraint {
		prb.add_constraint(Self::Constraint {
			index,
			array,
			result,
		})
	}
}

impl From<bool> for BoolDecision {
	fn from(v: bool) -> Self {
		BoolDecision(BoolDecisionInner::Const(v))
	}
}

impl Mul<IntVal> for BoolDecision {
	type Output = IntDecision;

	fn mul(self, rhs: IntVal) -> Self::Output {
		let me: IntDecision = self.into();
		me * rhs
	}
}

impl Mul<NonZero<IntVal>> for BoolDecision {
	type Output = IntDecision;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		let me: IntDecision = self.into();
		me * rhs
	}
}

impl Not for BoolDecision {
	type Output = BoolDecision;

	fn not(self) -> Self::Output {
		use BoolDecisionInner::*;

		BoolDecision(match self.0 {
			Lit(l) => Lit(!l),
			Const(b) => Const(!b),
			IntEq(v, i) => IntNotEq(v, i),
			IntGreaterEq(v, i) => IntLess(v, i),
			IntLess(v, i) => IntGreaterEq(v, i),
			IntNotEq(v, i) => IntEq(v, i),
		})
	}
}

impl Sub<IntVal> for BoolDecision {
	type Output = IntDecision;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl From<BoolDecision> for BoolFormula {
	fn from(v: BoolDecision) -> Self {
		Self::Atom(v)
	}
}

impl Branching {
	/// Add a [`Brancher`] implementation to the solver that matches the
	/// branching strategy of the [`Branching`].
	pub(crate) fn to_solver<Oracle: ExternalPropagation>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &ReformulationMap,
	) {
		match self {
			Branching::Bool(vars, var_sel, val_sel) => {
				let vars = vars.iter().map(|v| map.get_bool(slv, *v)).collect();
				BoolBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Int(v, var_sel, val_sel) => {
				let vars: Vec<_> = v.iter().map(|v| map.get_int(slv, *v)).collect();
				IntBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Seq(branchings) => {
				for b in branchings {
					b.to_solver(slv, map);
				}
			}
			Branching::WarmStart(exprs) => {
				let decisions = exprs.iter().map(|v| map.get_bool(slv, *v)).collect();
				WarmStartBrancher::new_in(slv, decisions);
			}
		}
	}
}

impl From<BoolDecision> for Decision {
	fn from(value: BoolDecision) -> Self {
		Self::Bool(value)
	}
}

impl From<IntDecision> for Decision {
	fn from(value: IntDecision) -> Self {
		Self::Int(value)
	}
}

impl IntDecision {
	/// Get a Boolean view that represent whether the integer view is equal to
	/// the given value.
	pub fn eq(&self, v: IntVal) -> BoolDecision {
		use IntDecisionInner::*;

		match self.0 {
			Const(c) => (c == v).into(),
			Linear(lin) => match lin.reverse_meaning(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(val)) => BoolDecision(BoolDecisionInner::IntEq(lin.var, val)),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					false.into()
				}
				_ => unreachable!(),
			},
			Bool(lin) => match lin.reverse_meaning(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(1))  => lin.var,
				Ok(IntLitMeaning::Eq(0))  => !lin.var,
				Ok(IntLitMeaning::Eq(_)) /* if val != 0 */ => false.into(),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					false.into()
				}
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is greater
	/// than or equal to the given value.
	pub fn geq(&self, v: IntVal) -> BoolDecision {
		!self.lt(v)
	}

	/// Get a Boolean view that represent whether the integer view is greater
	/// than the given value.
	pub fn gt(&self, v: IntVal) -> BoolDecision {
		self.geq(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// or equal to the given value.
	pub fn leq(&self, v: IntVal) -> BoolDecision {
		self.lt(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// the given value.
	pub fn lt(&self, v: IntVal) -> BoolDecision {
		use IntDecisionInner::*;

		match self.0 {
			Const(c) => (c < v).into(),
			Linear(lin) => match lin.reverse_meaning(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(val)) => {
					BoolDecision(BoolDecisionInner::IntGreaterEq(lin.var, val))
				}
				Ok(IntLitMeaning::Less(val)) => {
					BoolDecision(BoolDecisionInner::IntLess(lin.var, val))
				}
				_ => unreachable!(),
			},
			Bool(lin) => match lin.reverse_meaning(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(1)) => lin.var,
				Ok(IntLitMeaning::GreaterEq(val)) if val > 1 => false.into(),
				Ok(IntLitMeaning::GreaterEq(_)) /* if val <= 0 */ => true.into(),
				Ok(IntLitMeaning::Less(1)) => !lin.var,
				Ok(IntLitMeaning::Less(val)) if val > 1 => true.into(),
				Ok(IntLitMeaning::Less(_)) /* if val <= 0 */ => false.into(),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is not equal
	/// to the given value.
	pub fn ne(&self, v: IntVal) -> BoolDecision {
		!self.eq(v)
	}

	/// Resolve any aliasing in the IntDecision, ensuring the result is a
	/// IntDecision that if it is a `Var` or `Linear`, then the domain is not an
	/// alias.
	fn resolve_alias(self, model: &Model) -> Self {
		use IntDecisionInner::*;

		let mut view = self;
		let mut scale = 1;
		let mut offset = 0;
		loop {
			match view.0 {
				Const(c) => {
					return IntDecision(Const(c * scale + offset));
				}
				_ if scale == 0 => {
					return IntDecision(Const(offset));
				}
				Linear(lin) => match model.int_vars[lin.var].domain {
					Domain::Domain(_) => {
						return IntDecision(Linear(lin * NonZero::new(scale).unwrap() + offset));
					}
					Domain::Alias(alias) => {
						view = alias;
						offset += scale * lin.offset;
						scale *= lin.scale.get();
					}
				},
				Bool(lin) => {
					let var = lin.var.resolve_alias(model);
					if let BoolDecisionInner::Const(b) = var.0 {
						return IntDecision(Const(lin.transform_val(b as IntVal) * scale + offset));
					}
					return IntDecision(Bool(lin * NonZero::new(scale).unwrap() + offset));
				}
			}
		}
	}
}

impl Add<IntDecision> for IntDecision {
	type Output = IntLinExpr;

	fn add(self, rhs: IntDecision) -> Self::Output {
		IntLinExpr {
			terms: vec![self, rhs],
		}
	}
}

impl Add<IntVal> for IntDecision {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		use IntDecisionInner::*;

		if rhs == 0 {
			return self;
		}
		IntDecision(match self.0 {
			Const(v) => Const(v + rhs),
			Linear(lin) => Linear(lin + rhs),
			Bool(lin) => Bool(lin + rhs),
		})
	}
}

impl ElementConstraint for IntDecision {
	type Constraint = IntArrayElementBounds<IntDecision, IntDecision, IntDecision>;
	type Result = IntDecision;

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: IntDecision,
		result: Self::Result,
	) -> &mut Self::Constraint {
		let con = IntArrayElementBounds::new(prb, array, index, result);
		prb.add_constraint(con)
	}
}

impl From<BoolDecision> for IntDecision {
	fn from(value: BoolDecision) -> Self {
		match value.0 {
			BoolDecisionInner::Const(b) => (b as IntVal).into(),
			_ => IntDecision(IntDecisionInner::Bool(value.into())),
		}
	}
}

impl From<i64> for IntDecision {
	fn from(value: i64) -> Self {
		IntDecision(IntDecisionInner::Const(value))
	}
}

impl IntDecisionActions<Model> for IntDecision {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> BoolDecision {
		IntInspectionActions::try_lit(self, ctx, meaning).unwrap()
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<BoolDecision> {
		let val = self.val(ctx)?;
		Some(Self::eq(self, val))
	}
}

impl IntExplanationActions<Model> for IntDecision {
	fn lit_relaxed(&self, ctx: &Model, meaning: IntLitMeaning) -> (BoolDecision, IntLitMeaning) {
		(self.try_lit(ctx, meaning).unwrap(), meaning)
	}
}

impl IntInitActions<ModelInitContext<'_>> for IntDecision {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		let var = self.resolve_alias(ctx.model);

		match var.0 {
			IntDecisionInner::Linear(lin) => {
				let negated = lin.scale.is_negative();
				let adv = ctx.model.advisors.push(ModAdvisorDef {
					con: ctx.con,
					data,
					negated,
					bool2int: false,
					condition: None,
				});
				ctx.model.int_vars[lin.var]
					.constraints
					.add(ActivationAction::Advise(adv), cond);
			}
			IntDecisionInner::Const(_) => ctx.semantic_enqueue = true,
			IntDecisionInner::Bool(lin) => {
				let var = lin.var.resolve_alias(ctx.model);
				let (iv, cond, event) = match var.0 {
					BoolDecisionInner::Lit(lit) => {
						let adv = ctx.model.advisors.push(ModAdvisorDef {
							con: ctx.con,
							data,
							negated: false,
							bool2int: true,
							condition: None,
						});
						ctx.model.bool_vars[i32::from(lit.var()) as usize - 1]
							.constraints
							.push(ActivationAction::Advise(adv).into());
						return;
					}
					BoolDecisionInner::Const(_) => {
						// Value does not change, so no advisor will ever be called
						return;
					}
					BoolDecisionInner::IntEq(iv, v) => {
						(iv, IntLitMeaning::Eq(v), IntPropCond::Domain)
					}
					BoolDecisionInner::IntGreaterEq(iv, v) => {
						(iv, IntLitMeaning::GreaterEq(v), IntPropCond::Bounds)
					}
					BoolDecisionInner::IntLess(iv, v) => {
						(iv, IntLitMeaning::Less(v), IntPropCond::Bounds)
					}
					BoolDecisionInner::IntNotEq(iv, v) => {
						(iv, IntLitMeaning::NotEq(v), IntPropCond::Domain)
					}
				};
				let adv = ctx.model.advisors.push(ModAdvisorDef {
					con: ctx.con,
					data,
					negated: false,
					bool2int: true,
					condition: Some(cond),
				});
				ctx.model.int_vars[iv]
					.constraints
					.add(ActivationAction::Advise(adv), event);
			}
		}
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		let var = self.resolve_alias(ctx.model);

		match var.0 {
			IntDecisionInner::Linear(lin) => {
				let condition = match condition {
					IntPropCond::LowerBound if lin.scale.is_negative() => IntPropCond::UpperBound,
					IntPropCond::UpperBound if lin.scale.is_negative() => IntPropCond::LowerBound,
					_ => condition,
				};
				lin.var.enqueue_when(ctx, condition);
			}
			IntDecisionInner::Const(_) => ctx.semantic_enqueue = true,
			IntDecisionInner::Bool(lin) => {
				if condition != IntPropCond::Fixed {
					ctx.semantic_enqueue = true;
				}
				lin.var.enqueue_when_fixed(ctx);
			}
		}
	}
}

impl IntInspectionActions<Model> for IntDecision {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => (v, v),
			IntDecisionInner::Linear(lin) => lin.bounds(ctx),
			IntDecisionInner::Bool(lin) => lin.bounds(ctx),
		}
	}

	fn domain(&self, ctx: &Model) -> IntSetVal {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(c) => (c..=c).into(),
			IntDecisionInner::Linear(lin) => lin.domain(ctx),
			IntDecisionInner::Bool(lin) => lin.domain(ctx),
		}
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v == val,
			IntDecisionInner::Linear(lin) => lin.in_domain(ctx, val),
			IntDecisionInner::Bool(lin) => lin.in_domain(ctx, val),
		}
	}

	fn lit_meaning(&self, ctx: &Model, lit: BoolDecision) -> Option<IntLitMeaning> {
		match self.0 {
			IntDecisionInner::Const(_) => None,
			IntDecisionInner::Linear(lin) => lin.lit_meaning(ctx, lit),
			IntDecisionInner::Bool(lin) => lin.lit_meaning(ctx, lit),
		}
	}

	fn lower_bound(&self, ctx: &Model) -> IntVal {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v,
			IntDecisionInner::Linear(lin) => lin.lower_bound(ctx),
			IntDecisionInner::Bool(lin) => lin.lower_bound(ctx),
		}
	}

	fn lower_bound_lit(&self, ctx: &Model) -> BoolDecision {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(_) => true.into(),
			IntDecisionInner::Linear(lin) => lin.lower_bound_lit(ctx),
			IntDecisionInner::Bool(lin) => lin.lower_bound_lit(ctx),
		}
	}

	fn try_lit(&self, _: &Model, meaning: IntLitMeaning) -> Option<BoolDecision> {
		Some(match meaning {
			IntLitMeaning::Eq(v) => self.eq(v),
			IntLitMeaning::NotEq(v) => self.ne(v),
			IntLitMeaning::GreaterEq(v) => self.geq(v),
			IntLitMeaning::Less(v) => self.lt(v),
		})
	}

	fn upper_bound(&self, ctx: &Model) -> IntVal {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v,
			IntDecisionInner::Linear(lin) => lin.upper_bound(ctx),
			IntDecisionInner::Bool(lin) => lin.upper_bound(ctx),
		}
	}

	fn upper_bound_lit(&self, ctx: &Model) -> BoolDecision {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(_) => true.into(),
			IntDecisionInner::Linear(lin) => lin.upper_bound_lit(ctx),
			IntDecisionInner::Bool(lin) => lin.upper_bound_lit(ctx),
		}
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => Some(v),
			IntDecisionInner::Linear(lin) => lin.val(ctx),
			IntDecisionInner::Bool(lin) => lin.val(ctx),
		}
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for IntDecision {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSetVal {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: BoolDecision) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn lower_bound(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.lower_bound(ctx.model)
	}

	fn lower_bound_lit(&self, ctx: &ModelInitContext<'_>) -> BoolDecision {
		self.lower_bound_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<BoolDecision> {
		self.try_lit(ctx.model, meaning)
	}

	fn upper_bound(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.upper_bound(ctx.model)
	}

	fn upper_bound_lit(&self, ctx: &ModelInitContext<'_>) -> BoolDecision {
		self.upper_bound_lit(ctx.model)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl IntPropagationActions<Model> for IntDecision {
	fn set_lower_bound(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_lower_bound(ctx, val, reason),
			IntDecisionInner::Linear(lin) => lin.set_lower_bound(ctx, val, reason),
			IntDecisionInner::Bool(lin) => lin.set_lower_bound(ctx, val, reason),
		}
	}

	fn set_not_eq(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_not_eq(ctx, val, reason),
			IntDecisionInner::Linear(lin) => lin.set_not_eq(ctx, val, reason),
			IntDecisionInner::Bool(lin) => lin.set_not_eq(ctx, val, reason),
		}
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Model,
		ub: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_upper_bound(ctx, ub, reason),
			IntDecisionInner::Linear(lin) => lin.set_upper_bound(ctx, ub, reason),
			IntDecisionInner::Bool(lin) => lin.set_upper_bound(ctx, ub, reason),
		}
	}

	fn set_val(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_val(ctx, val, reason),
			IntDecisionInner::Linear(lin) => lin.set_val(ctx, val, reason),
			IntDecisionInner::Bool(lin) => lin.set_val(ctx, val, reason),
		}
	}
}

impl IntSimplificationActions<Model> for IntDecision {
	fn set_domain(
		&self,
		ctx: &mut Model,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_domain(ctx, values, reason),
			IntDecisionInner::Linear(lin) => lin.set_domain(ctx, values, reason),
			IntDecisionInner::Bool(lin) => lin.set_domain(ctx, values, reason),
		}
	}

	fn set_not_in_set(
		&self,
		ctx: &mut Model,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		match self.resolve_alias(ctx).0 {
			IntDecisionInner::Const(v) => v.set_not_in_set(ctx, values, reason),
			IntDecisionInner::Linear(lin) => lin.set_not_in_set(ctx, values, reason),
			IntDecisionInner::Bool(lin) => lin.set_not_in_set(ctx, values, reason),
		}
	}
	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Conflict<BoolDecision>> {
		use IntDecisionInner::*;

		let x = self.resolve_alias(ctx);
		let y = other.into().resolve_alias(ctx);

		let (idx, target) = match (x.0, y.0) {
			(x, y) if x == y => return Ok(()),
			(Bool(x), Bool(y)) => return x.unify(ctx, y),
			(Const(x), Const(y)) if x != y => return Err(ctx.declare_conflict([])),
			(Const(y), x) | (x, Const(y)) => {
				let x = IntDecision(x);
				return x.set_val(ctx, y, []);
			}
			(Linear(lin_x), Linear(lin_y)) => {
				// Decide which variable to redefine based on the other.
				let can_define_x = lin_y.scale.get() % lin_x.scale.get() == 0
					&& (lin_y.offset - lin_x.offset) % lin_x.scale.get() == 0;
				let can_define_y = lin_x.scale.get() % lin_y.scale.get() == 0
					&& (lin_x.offset - lin_y.offset) % lin_y.scale.get() == 0;
				let (lin_x, lin_y) = if can_define_x && can_define_y && lin_x.var > lin_y.var {
					(lin_x, lin_y)
				} else if can_define_y {
					(lin_y, lin_x)
				} else if can_define_x {
					(lin_x, lin_y)
				} else {
					ctx.add_constraint(IntEq { vars: [x, y] });
					return Ok(());
				};

				// Perform the transformation and add the aliasing domain to x:
				// x_scale * x + x_scale = y_scale * y + y_offset
				// === x = (y_scale / x_scale) * y + ((y_offset - x_offset) / x_scale)
				let scale = NonZero::new(lin_y.scale.get() / lin_x.scale.get()).unwrap();
				let offset = (lin_y.offset - lin_x.offset) / lin_x.scale.get();
				let target = IntDecision(Linear(LinearView::new(scale, offset, lin_y.var)));
				(lin_x.var, target)
			}
			(Linear(lin), Bool(b)) | (Bool(b), Linear(lin)) => {
				let lb = b.transform_val(0);
				let ub = b.transform_val(1);

				let contains_lb = lin.in_domain(ctx, lb);
				let contains_ub = lin.in_domain(ctx, ub);

				match (contains_lb, contains_ub) {
					(false, false) => {
						return Err(ctx.declare_conflict(|ctx: &mut Model| {
							[
								lin.lit(ctx, IntLitMeaning::NotEq(lb)),
								lin.lit(ctx, IntLitMeaning::NotEq(ub)),
							]
						}));
					}
					(false, true) => {
						lin.set_val(ctx, ub, [])?;
						return b.var.set(ctx, |ctx: &mut Model| {
							[lin.lit(ctx, IntLitMeaning::NotEq(lb))]
						});
					}
					(true, false) => {
						lin.set_val(ctx, lb, [])?;
						return b.var.set_val(ctx, false, |ctx: &mut Model| {
							[lin.lit(ctx, IntLitMeaning::NotEq(ub))]
						});
					}
					(true, true) => {
						let Ok(IntLitMeaning::Eq(i_lb)) =
							lin.reverse_meaning(IntLitMeaning::Eq(lb))
						else {
							unreachable!()
						};
						let Ok(IntLitMeaning::Eq(i_ub)) =
							lin.reverse_meaning(IntLitMeaning::Eq(ub))
						else {
							unreachable!()
						};
						let target = IntDecision(Bool(LinearBoolView::new(
							NonZero::new(i_ub - i_lb).unwrap(),
							i_lb,
							b.var,
						)));

						(lin.var, target)
					}
				}
			}
		};

		idx.unify_internal(ctx, target)
	}
}

impl Mul<IntVal> for IntDecision {
	type Output = Self;

	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			0.into()
		} else {
			self.mul(NonZero::new(rhs).unwrap())
		}
	}
}

impl Mul<NonZero<IntVal>> for IntDecision {
	type Output = Self;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		use IntDecisionInner::*;

		IntDecision(match self.0 {
			Const(v) => Const(v * rhs.get()),
			Linear(lin) => Linear(lin * rhs),
			Bool(lin) => Bool(lin * rhs),
		})
	}
}

impl Neg for IntDecision {
	type Output = Self;

	fn neg(self) -> Self::Output {
		use IntDecisionInner::*;

		IntDecision(match self.0 {
			Const(v) => Const(-v),
			Linear(lin) => Linear(-lin),
			Bool(lin) => Bool(-lin),
		})
	}
}

impl Sub<IntDecision> for IntDecision {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntDecision) -> Self::Output {
		self + -rhs
	}
}

impl Sub<IntVal> for IntDecision {
	type Output = Self;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl IntDecisionIndex {
	/// Internal method performing unification under the assumption that the
	/// receiver is an integer decision index that is not already aliased, and
	/// that it can be aliased to directly point to `other`.
	fn unify_internal(
		&self,
		ctx: &mut Model,
		target: IntDecision,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		debug_assert!(matches!(
			ctx.int_vars[*self].domain,
			Domain::Domain(_) | Domain::Alias(IntDecision(IntDecisionInner::Const(_)))
		));

		// Set the domain on the variable to be aliased to trigger subscription
		// events.
		self.set_domain(ctx, &target.domain(ctx), [])?;
		// Change variable to point to the target
		match mem::replace(&mut ctx.int_vars[*self].domain, Domain::Alias(target)) {
			// Restrict the domain of the target variable using the variable domain
			// being aliased.
			Domain::Domain(dom) => target.set_domain(ctx, &dom, [])?,
			Domain::Alias(IntDecision(IntDecisionInner::Const(v))) => target.set_val(ctx, v, [])?,
			_ => unreachable!(),
		};
		// Transfer any constraints from the aliased variable to the target variable
		let constraints = mem::take(&mut ctx.int_vars[*self].constraints);
		// Move subscriptions to target decision variable
		match target.0 {
			IntDecisionInner::Linear(lin) => {
				ctx.int_vars[lin.var].constraints.extend(constraints);
			}
			IntDecisionInner::Bool(lin) => match lin.var.0 {
				inner @ (BoolDecisionInner::IntEq(j, _)
				| BoolDecisionInner::IntNotEq(j, _)
				| BoolDecisionInner::IntGreaterEq(j, _)
				| BoolDecisionInner::IntLess(j, _)) => {
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<ModAdvisor, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut ctx.advisors[adv];
								def.bool2int = true;
								def.condition = Some(match inner {
									BoolDecisionInner::IntEq(_, v) => IntLitMeaning::Eq(v),
									BoolDecisionInner::IntGreaterEq(_, v) => {
										IntLitMeaning::GreaterEq(v)
									}
									BoolDecisionInner::IntLess(_, v) => IntLitMeaning::Less(v),
									BoolDecisionInner::IntNotEq(_, v) => IntLitMeaning::NotEq(v),
									_ => unreachable!(),
								});
								def.negated = false;
							}
							let cond = if matches!(
								inner,
								BoolDecisionInner::IntEq(_, _) | BoolDecisionInner::IntNotEq(_, _)
							) {
								IntPropCond::Domain
							} else {
								IntPropCond::Bounds
							};
							ctx.int_vars[j].constraints.add(act, cond);
						},
					);
				}
				// Move subscription to Boolean decision
				BoolDecisionInner::Lit(l) => {
					let jdx = i32::from(l.var()) as usize - 1;
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<ModAdvisor, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut ctx.advisors[adv];
								def.bool2int = true;
								def.negated = false;
							}
							ctx.bool_vars[jdx].constraints.push(act.into());
						},
					);
				}
				BoolDecisionInner::Const(_) => unreachable!(),
			},
			IntDecisionInner::Const(_) => unreachable!(),
		};
		Ok(())
	}
}

impl IntDecisionActions<Model> for IntDecisionIndex {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> BoolDecision {
		IntInspectionActions::try_lit(self, ctx, meaning).unwrap()
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<BoolDecision> {
		let val = self.val(ctx)?;
		Some(BoolDecision(BoolDecisionInner::IntEq(*self, val)))
	}
}

impl IntInitActions<ModelInitContext<'_>> for IntDecisionIndex {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		let adv = ctx.model.advisors.push(ModAdvisorDef {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: None,
		});
		ctx.model.int_vars[*self]
			.constraints
			.add(ActivationAction::Advise(adv), cond);
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		if condition != IntPropCond::Fixed {
			ctx.semantic_enqueue = true;
		}
		ctx.model.int_vars[*self]
			.constraints
			.add(ActivationAction::Enqueue(ctx.con), condition);
	}
}

impl IntInspectionActions<Model> for IntDecisionIndex {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => (*d.lower_bound().unwrap(), *d.upper_bound().unwrap()),
			Domain::Alias(alias) => alias.bounds(ctx),
		}
	}

	fn domain(&self, ctx: &Model) -> IntSetVal {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => d.clone(),
			Domain::Alias(alias) => alias.domain(ctx),
		}
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => d.contains(&val),
			Domain::Alias(alias) => alias.in_domain(ctx, val),
		}
	}

	fn lit_meaning(
		&self,
		_: &Model,
		lit: <Model as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		match lit.0 {
			BoolDecisionInner::IntEq(idx, val) if idx == *self => Some(IntLitMeaning::Eq(val)),
			BoolDecisionInner::IntGreaterEq(idx, val) if idx == *self => {
				Some(IntLitMeaning::GreaterEq(val))
			}
			BoolDecisionInner::IntLess(idx, val) if idx == *self => Some(IntLitMeaning::Less(val)),
			BoolDecisionInner::IntNotEq(idx, val) if idx == *self => {
				Some(IntLitMeaning::NotEq(val))
			}
			_ => None,
		}
	}

	fn lower_bound(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => *d.lower_bound().unwrap(),
			Domain::Alias(alias) => alias.lower_bound(ctx),
		}
	}

	fn lower_bound_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => d
				.lower_bound()
				.map(|&val| BoolDecision(BoolDecisionInner::IntGreaterEq(*self, val)))
				.unwrap(),
			Domain::Alias(alias) => alias.lower_bound_lit(ctx),
		}
	}

	fn try_lit(
		&self,
		ctx: &Model,
		meaning: IntLitMeaning,
	) -> Option<<Model as ReasoningContext>::Atom> {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(_) => Some(BoolDecision(match meaning {
				IntLitMeaning::Eq(v) => BoolDecisionInner::IntEq(*self, v),
				IntLitMeaning::NotEq(v) => BoolDecisionInner::IntNotEq(*self, v),
				IntLitMeaning::GreaterEq(v) => BoolDecisionInner::IntGreaterEq(*self, v),
				IntLitMeaning::Less(v) => BoolDecisionInner::IntLess(*self, v),
			})),
			Domain::Alias(alias) => alias.try_lit(ctx, meaning),
		}
	}

	fn upper_bound(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => *d.upper_bound().unwrap(),
			Domain::Alias(alias) => alias.upper_bound(ctx),
		}
	}

	fn upper_bound_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => d
				.lower_bound()
				.map(|&val| BoolDecision(BoolDecisionInner::IntLess(*self, val + 1)))
				.unwrap(),
			Domain::Alias(alias) => alias.upper_bound_lit(ctx),
		}
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		match &ctx.int_vars[*self].domain {
			Domain::Domain(d) => {
				let (lb, ub) = (d.lower_bound().unwrap(), d.upper_bound().unwrap());
				if lb == ub { Some(*lb) } else { None }
			}
			Domain::Alias(alias) => alias.val(ctx),
		}
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for IntDecisionIndex {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSetVal {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: BoolDecision) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn lower_bound(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.lower_bound(ctx.model)
	}

	fn lower_bound_lit(&self, ctx: &ModelInitContext<'_>) -> BoolDecision {
		self.lower_bound_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<BoolDecision> {
		self.try_lit(ctx.model, meaning)
	}

	fn upper_bound(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.upper_bound(ctx.model)
	}

	fn upper_bound_lit(&self, ctx: &ModelInitContext<'_>) -> BoolDecision {
		self.upper_bound_lit(ctx.model)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl IntPropagationActions<Model> for IntDecisionIndex {
	fn set_lower_bound(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[*self];
		let Domain::Domain(dom) = &mut def.domain else {
			unreachable!()
		};
		if val <= *dom.lower_bound().unwrap() {
			return Ok(());
		} else if val > *dom.upper_bound().unwrap() {
			return Err(ctx.create_conflict(
				BoolDecision(BoolDecisionInner::IntGreaterEq(*self, val)),
				reason,
			));
		}
		if val != *dom.upper_bound().unwrap() {
			dom.set_lower_bound(val);
			ctx.int_events
				.entry(*self)
				.and_modify(|e| *e += IntEvent::LowerBound)
				.or_insert(IntEvent::LowerBound);
		} else {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(*self, IntEvent::Fixed);
		};
		Ok(())
	}

	fn set_not_eq(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		self.set_not_in_set(ctx, &(val..=val).into(), reason)
	}

	fn set_upper_bound(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[*self];
		let Domain::Domain(dom) = &mut def.domain else {
			unreachable!()
		};
		if val >= *dom.upper_bound().unwrap() {
			return Ok(());
		} else if val < *dom.lower_bound().unwrap() {
			return Err(ctx.create_conflict(
				BoolDecision(BoolDecisionInner::IntLess(*self, val + 1)),
				reason,
			));
		}
		if val != *dom.lower_bound().unwrap() {
			dom.set_upper_bound(val);
			ctx.int_events
				.entry(*self)
				.and_modify(|v| *v += IntEvent::UpperBound)
				.or_insert(IntEvent::UpperBound);
		} else {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(*self, IntEvent::Fixed);
		};
		Ok(())
	}

	fn set_val(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[*self];
		let Domain::Domain(dom) = &def.domain else {
			unreachable!()
		};
		if dom.contains(&val) {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(*self, IntEvent::Fixed);
			Ok(())
		} else {
			Err(ctx.create_conflict(BoolDecision(BoolDecisionInner::IntEq(*self, val)), reason))
		}
	}
}

impl IntSimplificationActions<Model> for IntDecisionIndex {
	fn set_domain(
		&self,
		ctx: &mut Model,
		domain: &IntSetVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let Domain::Domain(dom) = &ctx.int_vars[*self].domain else {
			unreachable!()
		};
		let intersect: RangeList<_> = dom.intersect(domain);
		if intersect.is_empty() {
			return Err(ctx.create_conflict(
				BoolDecision(BoolDecisionInner::IntNotEq(
					*self,
					*dom.lower_bound().unwrap(),
				)),
				reason,
			));
		} else if *dom == intersect {
			return Ok(());
		}
		if intersect.card() == Some(1) {
			let val = *intersect.lower_bound().unwrap();
			ctx.int_vars[*self].domain = Domain::Alias(val.into());
			ctx.int_events.insert(*self, IntEvent::Fixed);
		} else {
			let entry = ctx.int_events.entry(*self).or_insert(IntEvent::Domain);
			if dom.lower_bound().unwrap() == intersect.lower_bound().unwrap() {
				*entry += IntEvent::LowerBound;
			}
			if dom.upper_bound().unwrap() == intersect.upper_bound().unwrap() {
				*entry += IntEvent::UpperBound;
			}

			ctx.int_vars[*self].domain = Domain::Domain(intersect);
		}
		Ok(())
	}

	fn set_not_in_set(
		&self,
		ctx: &mut Model,
		values: &IntSetVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let Domain::Domain(dom) = &ctx.int_vars[*self].domain else {
			unreachable!()
		};
		let diff: RangeList<_> = dom.diff(values);
		if diff.is_empty() {
			return Err(ctx.create_conflict(
				BoolDecision(BoolDecisionInner::IntNotEq(
					*self,
					*values.lower_bound().unwrap(),
				)),
				reason,
			));
		}
		if *dom == diff {
			return Ok(());
		}
		if diff.card() == Some(1) {
			let val = *diff.lower_bound().unwrap();
			ctx.int_vars[*self].domain = Domain::Alias(val.into());
			ctx.int_events.insert(*self, IntEvent::Fixed);
		} else {
			let entry = ctx.int_events.entry(*self).or_insert(IntEvent::Domain);
			if dom.lower_bound().unwrap() == diff.lower_bound().unwrap() {
				*entry += IntEvent::LowerBound;
			}
			if dom.upper_bound().unwrap() == diff.upper_bound().unwrap() {
				*entry += IntEvent::UpperBound;
			}

			ctx.int_vars[*self].domain = Domain::Domain(diff);
		};
		Ok(())
	}

	fn unify(
		&self,
		ctx: &mut Model,
		other: impl Into<Self>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let other: IntDecisionIndex = other.into();
		IntDecision(IntDecisionInner::Linear((*self).into()))
			.unify(ctx, IntDecision(IntDecisionInner::Linear(other.into())))
	}
}

impl IntLinExpr {
	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is equal to the given value.
	pub fn eq(self, rhs: IntVal) -> IntLinear {
		IntLinear {
			terms: self.terms,
			operator: LinOperator::Equal,
			rhs,
			reif: None,
		}
	}

	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is greater than or equal to the given value.
	pub fn geq(mut self, rhs: IntVal) -> IntLinear {
		self.terms = self.terms.into_iter().map(|x| -x).collect();
		self.leq(-rhs)
	}

	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is greater than the given value.
	pub fn gt(self, rhs: IntVal) -> IntLinear {
		self.geq(rhs + 1)
	}

	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is less than the given value.
	pub fn leq(self, rhs: IntVal) -> IntLinear {
		IntLinear {
			terms: self.terms,
			operator: LinOperator::LessEq,
			rhs,
			reif: None,
		}
	}
	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is less than or equal to the given value.
	pub fn lt(self, rhs: IntVal) -> IntLinear {
		self.leq(rhs - 1)
	}
	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is not equal to the given value.
	pub fn ne(self, rhs: IntVal) -> IntLinear {
		IntLinear {
			terms: self.terms,
			operator: LinOperator::NotEqual,
			rhs,
			reif: None,
		}
	}
}

impl Add<IntDecision> for IntLinExpr {
	type Output = IntLinExpr;

	fn add(self, rhs: IntDecision) -> Self::Output {
		let mut terms = self.terms;
		terms.push(rhs);
		IntLinExpr { terms }
	}
}

impl Add<IntVal> for IntLinExpr {
	type Output = IntLinExpr;

	fn add(mut self, rhs: IntVal) -> Self::Output {
		self.terms[0] = self.terms[0] + rhs;
		self
	}
}

impl From<IntDecision> for IntLinExpr {
	fn from(decision: IntDecision) -> Self {
		IntLinExpr {
			terms: vec![decision],
		}
	}
}

impl From<IntVal> for IntLinExpr {
	fn from(v: IntVal) -> Self {
		IntLinExpr {
			terms: vec![v.into()],
		}
	}
}

impl Mul<IntVal> for IntLinExpr {
	type Output = IntLinExpr;

	fn mul(self, rhs: IntVal) -> Self::Output {
		IntLinExpr {
			terms: self.terms.into_iter().map(|x| x * rhs).collect(),
		}
	}
}

impl Sub<IntDecision> for IntLinExpr {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntDecision) -> Self::Output {
		self + -rhs
	}
}

impl Sub<IntVal> for IntLinExpr {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl Sum<IntDecision> for IntLinExpr {
	fn sum<I: Iterator<Item = IntDecision>>(iter: I) -> Self {
		IntLinExpr {
			terms: iter.collect(),
		}
	}
}

impl ElementConstraint for IntVal {
	type Constraint = IntValArrayElement<IntDecision, IntDecision>;
	type Result = IntDecision;

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: IntDecision,
		result: Self::Result,
	) -> &mut Self::Constraint {
		let con = IntValArrayElement(IntArrayElementBounds::new(prb, array, index, result));
		prb.add_constraint(con)
	}
}

impl IntInitActions<ModelInitContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut ModelInitContext<'_>, _: IntPropCond, _: u64) {
		// Value will never change, so no advisor will ever be called
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue = true;
	}
}

impl Model {
	/// Internal method to add a constraint to the model.
	///
	/// Note that users will use either the `+=` operator or the
	/// [`Self::add_custom_constraint`] method.
	pub fn add_constraint<C: Constraint<Self>>(&mut self, mut constraint: C) -> &mut C {
		let con = ConRef::new(self.constraints.len());
		let mut ctx = ModelInitContext::new(self, con);
		constraint.initialize(&mut ctx);
		let priority = ctx.priority;
		let enqueue = ctx.enqueue();
		let r = self.constraints.push(Some(Box::new(constraint)));
		debug_assert_eq!(r, con);
		let r = self.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(r, con);
		if enqueue {
			self.propagator_queue.enqueue_propagator(con);
		}

		// Retrieve the reference for the last constraint
		let c: &mut dyn Constraint<Model> = self
			.constraints
			.last_mut()
			.unwrap()
			.as_mut()
			.unwrap()
			.as_mut();
		let c: &mut dyn Any = c;
		c.downcast_mut::<C>().unwrap()
	}

	/// Create a [`ReasoningEngine::Conflict`] instance based on the failure to
	/// set `subject`, that must be set because of `reason`.
	fn create_conflict(
		&mut self,
		subject: BoolDecision,
		reason: impl ReasonBuilder<Self>,
	) -> <Self as ReasoningEngine>::Conflict {
		match reason.build_reason(self) {
			Ok(reason) => Conflict {
				subject: Some(subject),
				reason,
			},
			Err(true) => Conflict {
				subject: None,
				reason: Reason::Simple(!subject),
			},
			Err(false) => unreachable!("invalid reason"),
		}
	}

	/// Create a new [`Model`] instance from a [`FlatZinc`] instance.
	pub fn from_fzn<S, MapTy: FromIterator<(S, Decision)>>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, MapTy, FlatZincStatistics), FlatZincError>
	where
		S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
	{
		let mut builder = FznModelBuilder::new(fzn);
		builder.unify_variables()?;
		builder.extract_views()?;
		builder.post_constraints()?;
		builder.create_branchers()?;
		builder.ensure_output()?;

		let res = builder.finalize();
		Ok(res)
	}

	/// Create a new Boolean variable.
	pub fn new_bool_var(&mut self) -> BoolDecision {
		let var = self.cnf.new_var();
		self.bool_vars.push(BoolDecisionDef {
			alias: None,
			constraints: Vec::new(),
		});
		debug_assert_eq!(i32::from(var) as usize, self.bool_vars.len());
		BoolDecision(BoolDecisionInner::Lit(var.into()))
	}

	/// Create `len` new Boolean variables.
	pub fn new_bool_vars(&mut self, len: usize) -> Vec<BoolDecision> {
		repeat_with(|| self.new_bool_var()).take(len).collect()
	}

	/// Create a new integer variable with the given domain.
	pub fn new_int_var(&mut self, domain: impl Into<IntSetVal>) -> IntDecision {
		let domain = domain.into();
		match domain.card() {
			Some(0) => {
				unimplemented!("integer decision must have at least 1 value in their domain")
			}
			Some(1) => (*domain.lower_bound().unwrap()).into(),
			_ => IntDecision(IntDecisionInner::Linear(
				self.int_vars
					.push(IntDecisionDef::with_domain(domain))
					.into(),
			)),
		}
	}

	/// Create `len` new integer variables with the given domain.
	pub fn new_int_vars(&mut self, len: usize, domain: impl Into<IntSetVal>) -> Vec<IntDecision> {
		let domain = domain.into();
		repeat_n(IntDecisionDef::with_domain(domain), len)
			.map(|v| IntDecision(IntDecisionInner::Linear(self.int_vars.push(v).into())))
			.collect()
	}

	/// Propagate the constraint at index `con`, updating the domains of the
	/// variables and rewriting the constraint if necessary.
	pub(crate) fn propagate(&mut self, con: ConRef) -> Result<(), ReformulationError> {
		let Some(mut con_obj) = self.constraints[con].take() else {
			return Ok(());
		};
		self.cur_prop = Some(con);
		let mut status = con_obj.simplify(self);
		self.cur_prop = None;

		// Resolve lazy explanation if it is required.
		if let Err(Conflict {
			subject,
			reason: Reason::Lazy(r),
		}) = status
		{
			debug_assert_eq!(ConRef::from_raw(r.propagator), con);
			let conj = con_obj.explain(
				self,
				subject.unwrap_or(BoolDecision(BoolDecisionInner::Const(false))),
				r.data,
			);
			status = Err(Conflict {
				subject,
				reason: Reason::Eager(conj.into_boxed_slice()),
			});
		};

		match status? {
			SimplificationStatus::Subsumed => {
				// Constraint is known to be satisfied, no need to place back.
			}
			SimplificationStatus::NoFixpoint => {
				self.constraints[con] = Some(con_obj);
			}
		}
		// Notify propagators about all events that occurred
		let advise_of_int_change = |model: &mut Model, con: ConRef, data: u64, event| {
			if let Some(mut c) = model.constraints[con].take() {
				let ret = c.advise_of_int_change(model, data, event);
				model.constraints[con] = Some(c);
				ret
			} else {
				false
			}
		};
		let advise_of_bool_change = |model: &mut Model, con: ConRef, data: u64| {
			if let Some(mut c) = model.constraints[con].take() {
				let ret = c.advise_of_bool_change(model, data);
				model.constraints[con] = Some(c);
				ret
			} else {
				false
			}
		};
		let mut int_events = mem::take(&mut self.int_events);
		for (iv, event) in int_events.drain() {
			let constraints = mem::take(&mut self.int_vars[iv].constraints);
			constraints.for_each_activated_by(event, |act| match act {
				ActivationAction::Advise(adv) => {
					let x: &ModAdvisorDef = &self.advisors[adv];
					let ModAdvisorDef {
						con,
						data,
						negated,
						bool2int,
						condition,
					} = x.clone();
					let event = match event {
						IntEvent::LowerBound if negated => IntEvent::UpperBound,
						IntEvent::UpperBound if negated => IntEvent::LowerBound,
						_ => event,
					};
					let enqueue = if let Some(cond) = condition {
						let triggered = match cond {
							IntLitMeaning::Eq(v) | IntLitMeaning::NotEq(v) => {
								BoolDecision(BoolDecisionInner::IntEq(iv, v))
									.val(self)
									.is_some()
							}
							IntLitMeaning::GreaterEq(v) | IntLitMeaning::Less(v) => {
								BoolDecision(BoolDecisionInner::IntGreaterEq(iv, v))
									.val(self)
									.is_some()
							}
						};
						if triggered {
							if bool2int {
								advise_of_int_change(self, con, data, IntEvent::Fixed)
							} else {
								advise_of_bool_change(self, con, data)
							}
						} else {
							false
						}
					} else {
						advise_of_int_change(self, con, data, event)
					};
					if enqueue {
						self.propagator_queue.enqueue_propagator(con);
					}
				}
				ActivationAction::Enqueue(c) => self.propagator_queue.enqueue_propagator(c),
			});
			self.int_vars[iv].constraints = constraints;
		}
		self.int_events = int_events;
		let mut bool_events = mem::take(&mut self.bool_events);
		for bv in bool_events.drain(..) {
			for &act in self.bool_vars[i32::from(bv) as usize - 1]
				.constraints
				.clone()
				.iter()
			{
				match act.into() {
					ActivationAction::Advise(adv) => {
						let x: &ModAdvisorDef = &self.advisors[adv];
						let ModAdvisorDef {
							con,
							data,
							bool2int,
							..
						} = x.clone();
						let enqueue = if bool2int {
							advise_of_int_change(self, con, data, IntEvent::Fixed)
						} else {
							advise_of_bool_change(self, con, data)
						};
						if enqueue {
							self.propagator_queue.enqueue_propagator(con);
						}
					}
					ActivationAction::Enqueue(c) => self.propagator_queue.enqueue_propagator(c),
				}
			}
		}
		self.bool_events = bool_events;
		Ok(())
	}

	/// Process the model to create a [`Solver`] instance that can be used to
	/// solve it.
	///
	/// This method will return a [`Solver`] instance in addition to a
	/// [`VariableMap`], which can be used to map from [`ModelView`]
	/// to [`crate::SolverView`]. If an error occurs during the reformulation
	/// process, or if it is found to be trivially unsatisfiable, then an error
	/// will be returned.
	pub fn to_solver<Oracle>(
		&mut self,
		config: &InitConfig,
	) -> Result<(Solver<Oracle>, ReformulationMap), ReformulationError>
	where
		Solver<Oracle>: Default,
		Oracle: ExternalPropagation + 'static,
	{
		let mut slv = Solver::<Oracle>::default();
		let any_slv: &mut dyn Any = &mut slv.oracle;
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			// Set the solver options for preprocessing/inprocessing
			r.set_option("condition", config.conditioning() as i32);
			r.set_option("elim", config.variable_elimination() as i32);
			r.set_option("exteagerreasons", config.reason_eager() as i32);
			r.set_option("inprocessing", config.inprocessing() as i32);
			r.set_limit("preprocessing", config.preprocessing() as i32);
			r.set_option("probe", config.probing() as i32);
			r.set_option("subsume", config.subsumption() as i32);
			r.set_option("vivify", config.vivification() as i32);

			// Set the solver options for search configurations
			// Enable restart if the config is set to true or if there are no
			// user search heuristics are provided
			r.set_option(
				"restart",
				(config.restart() || self.branchings.is_empty()) as i32,
			);
		} else {
			warn!("unknown solver: vivification and restart options are ignored");
		}

		while let Some(con) = self.propagator_queue.pop() {
			self.propagate(con)?;
		}

		// Determine encoding types for integer variables
		let mut int_eager_direct = FxHashSet::<IntDecisionIndex>::default();
		let int_eager_order = FxHashSet::<IntDecisionIndex>::default();

		for c in self.constraints.iter().flatten() {
			let c: &dyn Constraint<Model> = c.as_ref();
			let c: &dyn Any = c;
			if let Some(c) = c.downcast_ref::<BoolDecisionArrayElement>() {
				let index = c.index.resolve_alias(self);
				if let IntDecisionInner::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			} else if let Some(c) = c.downcast_ref::<IntAllDifferent>() {
				for v in &c.prop.var {
					let v = v.resolve_alias(self);
					if let IntDecisionInner::Linear(lin) = v.0 {
						let Domain::Domain(dom) = &self.int_vars[lin.var].domain else {
							unreachable!()
						};
						if dom.card() <= Some(c.prop.var.len() * 100 / 80) {
							int_eager_direct.insert(lin.var);
						}
					}
				}
			} else if let Some(c) =
				c.downcast_ref::<IntArrayElementBounds<IntDecision, IntDecision, IntDecision>>()
			{
				let index = c.index.resolve_alias(self);
				if let IntDecisionInner::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			} else if let Some(c) = c.downcast_ref::<IntTable>() {
				for &v in &c.vars {
					let v = v.resolve_alias(self);
					if let IntDecisionInner::Linear(lin) = v.0 {
						int_eager_direct.insert(lin.var);
					}
				}
			} else if let Some(c) = c.downcast_ref::<IntValArrayElement<IntDecision, IntDecision>>()
			{
				let index = c.0.index.resolve_alias(self);
				if let IntDecisionInner::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			}
		}

		// Create the mapping between model decisions and solver views.
		let mut map_builder = ReformulationMapBuilder {
			bool_map: vec![None; self.bool_vars.len()],
			int_eager_direct,
			int_eager_limit: config.int_eager_limit(),
			int_eager_order,
			int_map: index_vec![None; self.int_vars.len()],
		};

		// Ensure the creation of all integer variables.
		for (idx, _) in self.int_vars.iter_enumerated() {
			map_builder.get_or_create_int(self, &mut slv, idx);
		}

		// Ensure the creation of all Boolean variables.
		for var in 1..=self.bool_vars.len() as u32 {
			let var = BoolDecision(BoolDecisionInner::Lit(RawLit::from_raw(
				NonZeroI32::new(var as i32).unwrap(),
			)));
			map_builder.get_or_create_bool(self, &mut slv, var);
		}

		// Finalize the reformulation map (all variables must be created by now)
		let map = map_builder.finalize();

		// Create constraint data structures within the solver
		for c in self.constraints.iter().flatten() {
			c.to_solver(&mut ReformulationContext {
				slv: &mut slv,
				map: &map,
			})?;
		}
		// Add branching data structures to the solver
		for b in self.branchings.iter() {
			b.to_solver(&mut slv, &map);
		}

		Ok((slv, map))
	}
}

impl AddAssign<Branching> for Model {
	fn add_assign(&mut self, rhs: Branching) {
		self.branchings.push(rhs);
	}
}

impl ClauseDatabase for Model {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		self.cnf.add_clause_from_slice(clause)
	}
	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.cnf.new_var_range(len)
	}
}

impl ConstructionActions for Model {
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.trail.push(init)
	}
}

impl DecisionActions for Model {
	fn num_conflicts(&self) -> u64 {
		0
	}
}

impl PropagationActions for Model {
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self>) -> Conflict<BoolDecision> {
		match reason.build_reason(self) {
			Ok(reason) => Conflict {
				subject: None,
				reason,
			},
			Err(false) => panic!("invalid reason"),
			Err(true) => Conflict {
				subject: None,
				reason: Reason::Eager(Box::new([])),
			},
		}
	}

	fn deferred_reason(&self, data: u64) -> LazyReason {
		LazyReason {
			propagator: self.cur_prop.unwrap().raw(),
			data,
		}
	}
}

impl ReasoningContext for Model {
	type Atom = <Self as ReasoningEngine>::Atom;
	type Conflict = <Self as ReasoningEngine>::Conflict;
}

impl ReasoningEngine for Model {
	type Atom = BoolDecision;

	type Conflict = Conflict<BoolDecision>;
	type ExplanationCtx<'a> = Self;
	type InitializationCtx<'a> = ModelInitContext<'a>;
	type NotificationCtx<'a> = Self;
	type PropagationCtx<'a> = Self;
}

impl SimplificationActions for Model {
	type Target = Model;

	fn add_constraint<C: Constraint<Model>>(&mut self, constraint: C) {
		self.add_constraint(constraint);
	}
}

impl TrailingActions for Model {
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal {
		mem::replace(&mut self.trail[i], v)
	}

	fn trailed_int(&self, i: TrailedInt) -> IntVal {
		self.trail[i]
	}
}

impl<'a> ModelInitContext<'a> {
	/// Returns whether to enqueue the propagator based on its explicit requests
	/// or otherwise the semantics of its subscriptions.
	pub(crate) fn enqueue(&self) -> bool {
		if let Some(enqueue) = self.decision_enqueue {
			enqueue
		} else {
			self.semantic_enqueue
		}
	}
	/// Creates a new [`ModelPostingContext`] for the given constraint
	/// reference.
	pub(crate) fn new(model: &'a mut Model, con: ConRef) -> Self {
		ModelInitContext {
			con,
			model,
			priority: PriorityLevel::Medium,
			semantic_enqueue: false,
			decision_enqueue: None,
		}
	}
}

impl InitActions for ModelInitContext<'_> {
	fn advise_on_backtrack(&mut self) {
		// Model does not backtrack, so no advisor is required.
	}

	fn enqueue_now(&mut self, option: bool) {
		self.decision_enqueue = Some(option);
	}

	fn set_priority(&mut self, priority: PriorityLevel) {
		self.priority = priority;
	}
}

impl ReasoningContext for ModelInitContext<'_> {
	type Atom = <Model as ReasoningEngine>::Atom;
	type Conflict = <Model as ReasoningEngine>::Conflict;
}

impl BoolInitActions<ModelInitContext<'_>> for bool {
	fn advise_when_fixed(&self, _: &mut ModelInitContext<'_>, _: u64) {
		// Value does not change, so no advisor will ever be called
	}
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		ctx.semantic_enqueue = true;
	}
}

impl BoolPropagationActions<Model> for bool {
	fn set_val(
		&self,
		ctx: &mut Model,
		val: bool,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<BoolDecision>> {
		if *self != val {
			return Err(ctx.declare_conflict(reason));
		}
		Ok(())
	}
}

impl ElementConstraint for bool {
	type Constraint = IntInSetReif;
	type Result = BoolDecision;

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: IntDecision,
		result: Self::Result,
	) -> &mut Self::Constraint {
		// Convert array of boolean values to a set literals of the indices where
		// the value is true
		let mut ranges = Vec::new();
		let mut start = None;
		for (i, b) in array.iter().enumerate() {
			match (b, start) {
				(true, None) => start = Some(i as IntVal),
				(false, Some(s)) => {
					ranges.push(s..=(i - 1) as IntVal);
					start = None;
				}
				(false, None) | (true, Some(_)) => {}
			}
		}
		if let Some(s) = start {
			ranges.push(s..=array.len() as IntVal);
		}
		assert_ne!(ranges.len(), 0, "unexpected empty range list");

		prb.add_constraint(Self::Constraint {
			var: index,
			set: RangeList::from_iter(ranges),
			reif: result,
		})
	}
}

index_vec::define_index_type! {
	/// Identifies an constraint in a [`Model`]
	pub(crate) struct ConRef = u32;
	// Allow storing as i32 in [`ActivationActionS`]
	MAX_INDEX = i32::MAX as usize;
}

index_vec::define_index_type! {
	/// Identifies an constraint in a [`Model`]
	pub(crate) struct ModAdvisor = u32;
	// Allow storing as i32 in [`ActivationActionS`]
	MAX_INDEX = i32::MAX as usize;
}
