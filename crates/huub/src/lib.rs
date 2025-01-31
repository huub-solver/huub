//! # Huub - A Modular and Maintainable Lazy Clause Generation Solver
//!
//! Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and
//! maintainability in addition to speed. LCG solvers are a class of solvers
//! that can be used to solve decision and optimization problems. They are
//! characterized by their ability to dynamically add new Boolean variables and
//! clauses to a Boolean Satisfiability (SAT) solver during the search process.
//! This allows the solver exploit SAT solver's ability to learn from failures
//! during the search process, without having to encode the full problem into
//! Boolean variables and clauses.

pub mod actions;
pub mod branchers;
pub mod constraints;
pub mod flatzinc;
pub(crate) mod helpers;
pub mod reformulate;
pub mod solver;
#[cfg(test)]
pub(crate) mod tests;

use std::{
	any::Any,
	collections::{HashSet, VecDeque},
	fmt::{Debug, Display},
	hash::Hash,
	iter::{repeat, Sum},
	num::NonZeroI64,
	ops::{Add, AddAssign, Deref, Mul, Neg, Not, Sub},
};

use flatzinc_serde::FlatZinc;
use index_vec::IndexVec;
use itertools::Itertools;
pub use pindakaas::solver::SlvTermSignal;
use pindakaas::{
	propositional_logic::Formula,
	solver::{cadical::Cadical, propagation::PropagatingSolver},
	ClauseDatabase, ClauseDatabaseTools, Cnf, Lit as RawLit, Unsatisfiable,
};
use rangelist::{IntervalIterator, RangeList};
use tracing::warn;

use crate::{
	actions::{ConstraintInitActions, SimplificationActions},
	branchers::{BoolBrancher, IntBrancher, WarmStartBrancher},
	constraints::{
		all_different_int::AllDifferentInt,
		array_int_element::ArrayIntElement,
		array_int_minimum::ArrayIntMinimum,
		array_var_bool_element::ArrayVarBoolElement,
		array_var_int_element::ArrayVarIntElement,
		disjunctive_strict::DisjunctiveStrict,
		int_abs::IntAbs,
		int_div::IntDiv,
		int_linear::{IntLinear, LinOperator},
		int_pow::IntPow,
		int_times::IntTimes,
		set_in_reif::SetInReif,
		table_int::TableInt,
		BoxedConstraint, Constraint, SimplificationStatus,
	},
	flatzinc::{FlatZincError, FlatZincStatistics, FznModelBuilder},
	helpers::linear_transform::LinearTransform,
	reformulate::{
		BoolDecisionInner, ConstraintStore, InitConfig, IntDecisionDef, IntDecisionIndex,
		IntDecisionInner, ReformulationError, ReformulationMap,
	},
	solver::{
		engine::Engine,
		int_var::{EncodingType, IntVar as SlvIntVar},
		BoolView, BoolViewInner, IntLitMeaning, IntView, Solver,
	},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
/// A reference to a Boolean decision in the [`Model`].
///
/// Note that decisions only represent where the decision is kept
pub struct BoolDecision(BoolDecisionInner);

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
	/// Search by enforcing the given Boolean expressions, but abandon the search
	/// when finding a conflict.
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

/// Type alias for the type used to represent logic formulas that can be used in
/// [`Model`].
pub type LogicFormula = Formula<BoolDecision>;

/// Type alias for a non-zero paremeter integer value.
pub type NonZeroIntVal = NonZeroI64;

#[derive(Clone, Debug, Default)]
/// A formulation of a problem instance in terms of decisions and constraints.
pub struct Model {
	/// A base [`Cnf`] object that contains pure Boolean parts of the problem.
	pub(crate) cnf: Cnf,
	/// An list of branching strategies that will be used by created [`Solver`]
	/// instances to be used in order to make search decisions.
	branchings: Vec<Branching>,
	/// A list of constraints that have been added to the model.
	constraints: Vec<Option<ConstraintStore>>,
	/// The definitions of the integer variables that have been created.
	int_vars: IndexVec<IntDecisionIndex, IntDecisionDef>,
	/// A queue of indexes of constraints that need to be propagated.
	prop_queue: VecDeque<usize>,
	/// A flag for each constraint whether it has been enqueued for propagation.
	enqueued: Vec<bool>,
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
	/// Select the unfixed decision variable with the smallest lower bound, using
	/// the order of the variables in case of a tie.
	Smallest,
}

/// Create a `all_different_int` constraint that enforces that all the given
/// integer decisions take different values.
pub fn all_different_int<Iter>(vars: Iter) -> AllDifferentInt
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	AllDifferentInt {
		vars: vars.into_iter().map_into().collect(),
	}
}

/// Create an `array_int_element` constraint that enforces that a result integer
/// decision variable takes the value equal the element of the given array of
/// integer values at the given index decision variable.
pub fn array_int_element(
	index: IntDecision,
	array: Vec<IntVal>,
	result: IntDecision,
) -> ArrayIntElement {
	ArrayIntElement {
		index,
		array,
		result,
	}
}

/// Create an `array_int_maximum` constraint that enforces that an integer
/// decision variable takes the minimum value of an array of integer decision
/// variables.
pub fn array_int_maximum<Iter>(vars: Iter, max: IntDecision) -> ArrayIntMinimum
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	array_int_minimum(vars.into_iter().map(|v| -v.into()), -max)
}

/// Create an `array_int_minimum` constraint that enforces that an integer
/// decision variable takes the minimum value of an array of integer decision
/// variables.
pub fn array_int_minimum<Iter>(vars: Iter, min: IntDecision) -> ArrayIntMinimum
where
	Iter: IntoIterator,
	Iter::Item: Into<IntDecision>,
{
	ArrayIntMinimum {
		vars: vars.into_iter().map_into().collect(),
		min,
	}
}

/// Create an `array_var_bool_element` constraint that enforces that a result
/// Boolean decision variable takes the value equal the element of the given
/// array of Boolean decision varaibles at the index given by the index integer
/// decision variable.
pub fn array_var_bool_element(
	index: IntDecision,
	array: Vec<BoolDecision>,
	result: BoolDecision,
) -> ArrayVarBoolElement {
	ArrayVarBoolElement {
		index,
		array,
		result,
	}
}

/// Create a `disjunctive_strict` constraint that enforces that the given a list
/// of integer decision variables representing the start times of tasks and a
/// list of integer values representing the durations of tasks, the tasks do not
/// overlap in time.
pub fn disjunctive_strict(
	start_times: Vec<IntDecision>,
	durations: Vec<IntVal>,
) -> DisjunctiveStrict {
	assert_eq!(
		start_times.len(),
		durations.len(),
		"disjunctive_strict must be given the same number of start times and durations."
	);
	assert!(
		durations.iter().all(|&dur| dur >= 0),
		"disjunctive_strict cannot be given any negative durations."
	);
	DisjunctiveStrict {
		start_times,
		durations,
	}
}

/// Create an `array_var_int_element` constraint that enforces that a result
/// integer decision variable takes the value equal the element of the given
/// array of integer decision variable at the given index decision variable.
pub fn array_var_int_element(
	index: IntDecision,
	array: Vec<IntDecision>,
	result: IntDecision,
) -> ArrayVarIntElement {
	ArrayVarIntElement {
		index,
		array,
		result,
	}
}

/// Create an `int_abs` constraint that enforces that the second integer
/// decision variable takes the absolute value of the first integer decision
/// variable.
pub fn int_abs(origin: IntDecision, abs: IntDecision) -> IntAbs {
	IntAbs { origin, abs }
}

/// Create an `int_div` constraint that enforces that a numerator decision
/// integer variable divided by a denominator integer decision variable is equal
/// to a result integer decision variable.
pub fn int_div(numerator: IntDecision, denominator: IntDecision, result: IntDecision) -> IntDiv {
	IntDiv {
		numerator,
		denominator,
		result,
	}
}

/// Create an `int_pow` constraint that enforces that a base integer decision
/// variable exponentiated by an exponent integer decision variable is equal to
/// a result integer decision variable.
pub fn int_pow(base: IntDecision, exponent: IntDecision, result: IntDecision) -> IntPow {
	IntPow {
		base,
		exponent,
		result,
	}
}

/// Create an `int_times` constraint that enforces that the product of the two
/// integer decision variables is equal to a third.
pub fn int_times(factor1: IntDecision, factor2: IntDecision, product: IntDecision) -> IntTimes {
	IntTimes {
		factor1,
		factor2,
		product,
	}
}

/// Create a `set_in_reif` constraint that enforces that the given Boolean
/// variable takes the value `true` if-and-only-if an integer variable is in a
/// given set.
pub fn set_in_reif(var: IntDecision, set: IntSetVal, reif: BoolDecision) -> SetInReif {
	SetInReif { var, set, reif }
}

/// Create a `table_int` constraint that enforces that given list of integer
/// views take their values according to one of the given lists of integer
/// values.
pub fn table_int(vars: Vec<IntDecision>, table: Vec<Vec<IntVal>>) -> TableInt {
	assert!(table.iter().all(|tup| tup.len() == vars.len()), "The number of values in each row of the table must be equal to the number of decision variables.");
	TableInt { vars, table }
}

impl From<bool> for BoolDecision {
	fn from(v: bool) -> Self {
		BoolDecision(BoolDecisionInner::Const(v))
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

impl Branching {
	/// Add a [`Brancher`] implementation to the solver that matches the branching
	/// strategy of the [`Branching`].
	pub(crate) fn to_solver<Oracle: PropagatingSolver<Engine>>(
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
	/// Get a Boolean view that represent whether the integer view is equal to the
	/// given value.
	pub fn eq(&self, v: IntVal) -> BoolDecision {
		use IntDecisionInner::*;

		match self.0 {
			Var(x) => BoolDecision(BoolDecisionInner::IntEq(x, v)),
			Const(c) => (c == v).into(),
			Linear(t, x) => match t.rev_transform_lit(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(val)) => BoolDecision(BoolDecisionInner::IntEq(x, val)),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					false.into()
				}
				_ => unreachable!(),
			},
			Bool(t, x) => match t.rev_transform_lit(IntLitMeaning::Eq(v)) {
				Ok(IntLitMeaning::Eq(1))  => x,
				Ok(IntLitMeaning::Eq(0))  => !x,
				Ok(IntLitMeaning::Eq(_)) /* if val != 0 */ => false.into(),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is greater than
	/// the given value.
	pub fn gt(&self, v: IntVal) -> BoolDecision {
		self.geq(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is greater than
	/// or equal to the given value.
	pub fn geq(&self, v: IntVal) -> BoolDecision {
		!self.lt(v)
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// the given value.
	pub fn lt(&self, v: IntVal) -> BoolDecision {
		use IntDecisionInner::*;

		match self.0 {
			Var(x) => BoolDecision(BoolDecisionInner::IntLess(x, v)),
			Const(c) => (c <= v).into(),
			Linear(t, x) => match t.rev_transform_lit(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(val)) => {
					BoolDecision(BoolDecisionInner::IntGreaterEq(x, val))
				}
				Ok(IntLitMeaning::Less(val)) => BoolDecision(BoolDecisionInner::IntLess(x, val)),
				_ => unreachable!(),
			},
			Bool(t, x) => match t.rev_transform_lit(IntLitMeaning::Less(v)) {
				Ok(IntLitMeaning::GreaterEq(1)) => x,
				Ok(IntLitMeaning::GreaterEq(val)) if val > 1 => false.into(),
				Ok(IntLitMeaning::GreaterEq(_)) /* if val <= 0 */ => true.into(),
				Ok(IntLitMeaning::Less(1)) => !x,
				Ok(IntLitMeaning::Less(val)) if val > 1 => true.into(),
				Ok(IntLitMeaning::Less(_)) /* if val <= 0 */ => false.into(),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is less than or
	/// equal to the given value.
	pub fn leq(&self, v: IntVal) -> BoolDecision {
		self.lt(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is not equal to
	/// the given value.
	pub fn ne(&self, v: IntVal) -> BoolDecision {
		!self.eq(v)
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
			Var(x) => Linear(LinearTransform::offset(rhs), x),
			Const(v) => Const(v + rhs),
			Linear(t, x) => {
				let t = t + rhs;
				if t.is_identity() {
					Var(x)
				} else {
					Linear(t, x)
				}
			}
			Bool(t, x) => Bool(t + rhs, x),
		})
	}
}

impl From<i64> for IntDecision {
	fn from(value: i64) -> Self {
		IntDecision(IntDecisionInner::Const(value))
	}
}

impl From<BoolDecision> for IntDecision {
	fn from(value: BoolDecision) -> Self {
		match value.0 {
			BoolDecisionInner::Const(b) => (b as IntVal).into(),
			_ => IntDecision(IntDecisionInner::Bool(LinearTransform::offset(0), value)),
		}
	}
}

impl Mul<IntVal> for IntDecision {
	type Output = Self;

	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			0.into()
		} else {
			self.mul(NonZeroIntVal::new(rhs).unwrap())
		}
	}
}

impl Mul<NonZeroIntVal> for IntDecision {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		use IntDecisionInner::*;

		IntDecision(match self.0 {
			Var(x) => Linear(LinearTransform::scaled(rhs), x),
			Const(v) => Const(v * rhs.get()),
			Linear(t, x) => Linear(t * rhs, x),
			Bool(t, x) => Bool(t * rhs, x),
		})
	}
}

impl Neg for IntDecision {
	type Output = Self;

	fn neg(self) -> Self::Output {
		use IntDecisionInner::*;

		IntDecision(match self.0 {
			Var(x) => Linear(LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()), x),
			Const(v) => Const(-v),
			Linear(t, x) => Linear(-t, x),
			Bool(t, x) => Bool(-t, x),
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

impl IntLinExpr {
	/// Create a new integer linear constraint that enforces that the sum of the
	/// expressions in the object is less than or equal to the given value.
	pub fn lt(self, rhs: IntVal) -> IntLinear {
		self.leq(rhs - 1)
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

impl From<BoolDecision> for LogicFormula {
	fn from(v: BoolDecision) -> Self {
		Self::Atom(v)
	}
}

impl Model {
	/// Internal method to add a constraint to the model.
	///
	/// Note that users will use either the `+=` operator or the
	/// [`Self::add_custom_constraint`] method.
	fn add_constraint(&mut self, constraint: ConstraintStore) {
		self.constraints.push(Some(constraint));
		self.enqueued.push(false);
		self.enqueue(self.constraints.len() - 1);
		self.subscribe(self.constraints.len() - 1);
	}

	/// Add a custom constraint to the model.
	pub fn add_custom_constraint(&mut self, _: IntVal) {
		todo!()
	}

	/// Enqueue constraint that has index `constraint` to the propagation queue.
	fn enqueue(&mut self, constraint: usize) {
		if !self.enqueued[constraint] {
			self.prop_queue.push_back(constraint);
			self.enqueued[constraint] = true;
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
		builder.extract_views()?;
		builder.unify_variables()?;
		builder.post_constraints()?;
		builder.create_branchers()?;
		builder.ensure_output()?;

		Ok(builder.finalize())
	}

	/// Create a new Boolean variable.
	pub fn new_bool_var(&mut self) -> BoolDecision {
		BoolDecision(BoolDecisionInner::Lit(self.cnf.new_lit()))
	}

	/// Create `len` new Boolean variables.
	pub fn new_bool_vars(&mut self, len: usize) -> Vec<BoolDecision> {
		self.cnf
			.new_var_range(len)
			.map(|v| BoolDecision(BoolDecisionInner::Lit(v.into())))
			.collect()
	}

	/// Create a new integer variable with the given domain.
	pub fn new_int_var(&mut self, domain: IntSetVal) -> IntDecision {
		IntDecision(IntDecisionInner::Var(
			self.int_vars.push(IntDecisionDef::with_domain(domain)),
		))
	}

	/// Create `len` new integer variables with the given domain.
	pub fn new_int_vars(&mut self, len: usize, domain: IntSetVal) -> Vec<IntDecision> {
		repeat(IntDecisionDef::with_domain(domain))
			.take(len)
			.map(|v| IntDecision(IntDecisionInner::Var(self.int_vars.push(v))))
			.collect()
	}

	/// Propagate the constraint at index `con`, updating the domains of the
	/// variables and rewriting the constraint if necessary.
	pub(crate) fn propagate(&mut self, con: usize) -> Result<(), ReformulationError> {
		let Some(mut con_obj) = self.constraints[con].take() else {
			return Ok(());
		};

		let status = match &mut con_obj {
			ConstraintStore::AllDifferentInt(c) => c.simplify(self),
			ConstraintStore::ArrayIntElement(c) => c.simplify(self),
			ConstraintStore::ArrayIntMinimum(c) => c.simplify(self),
			ConstraintStore::ArrayVarBoolElement(c) => c.simplify(self),
			ConstraintStore::ArrayVarIntElement(c) => c.simplify(self),
			ConstraintStore::DisjunctiveStrict(c) => c.simplify(self),
			ConstraintStore::IntAbs(c) => c.simplify(self),
			ConstraintStore::IntDiv(c) => c.simplify(self),
			ConstraintStore::IntLinear(c) => c.simplify(self),
			ConstraintStore::IntPow(c) => c.simplify(self),
			ConstraintStore::IntTimes(c) => c.simplify(self),
			ConstraintStore::PropLogic(exp) => exp.simplify(self),
			ConstraintStore::SetInReif(c) => c.simplify(self),
			ConstraintStore::TableInt(con) => con.simplify(self),
			ConstraintStore::UserCustom(con) => con.simplify(self),
		}?;
		match status {
			SimplificationStatus::Subsumed => {
				// Constraint is known to be satisfied, no need to place back.
			}
			SimplificationStatus::Fixpoint => {
				self.constraints[con] = Some(con_obj);
			}
		}
		Ok(())
	}

	/// Subscribe the constraint located at index `con` to changes in the
	/// variables it depends on.
	pub(crate) fn subscribe(&mut self, con: usize) {
		/// Wrapper around [`Model`] that knows the constraint being initialized.
		struct ConstraintInitContext<'a> {
			/// Index of the constraint being initialized.
			con: usize,
			/// Reference to the Model in which the constraint exists.
			model: &'a mut Model,
		}

		impl ConstraintInitActions for ConstraintInitContext<'_> {
			fn simplify_on_change_bool(&mut self, _var: BoolDecision) {
				// TODO: Implement Boolean domain tracking
			}

			fn simplify_on_change_int(&mut self, var: IntDecision) {
				use IntDecisionInner::*;
				match var.0 {
					Bool(_, v) => self.simplify_on_change_bool(v),
					Linear(_, v) | Var(v) => {
						self.model.int_vars[v].constraints.push(self.con);
					}
					Const(_) => {}
				}
			}
		}

		let con_store = self.constraints[con].take().unwrap();
		let mut ctx = ConstraintInitContext { con, model: self };
		match &con_store {
			ConstraintStore::AllDifferentInt(con) => {
				<AllDifferentInt as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::ArrayIntElement(con) => {
				<ArrayIntElement as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::ArrayIntMinimum(con) => {
				<ArrayIntMinimum as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::ArrayVarBoolElement(con) => {
				<ArrayVarBoolElement as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::ArrayVarIntElement(con) => {
				<ArrayVarIntElement as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::DisjunctiveStrict(con) => {
				<DisjunctiveStrict as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::IntAbs(con) => {
				<IntAbs as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::IntDiv(con) => {
				<IntDiv as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::IntLinear(con) => {
				<IntLinear as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::IntPow(con) => {
				<IntPow as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::IntTimes(con) => {
				<IntTimes as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::PropLogic(exp) => {
				<Formula<BoolDecision> as Constraint<Model>>::initialize(exp, &mut ctx);
			}
			ConstraintStore::SetInReif(con) => {
				<SetInReif as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::TableInt(con) => {
				<TableInt as Constraint<Model>>::initialize(con, &mut ctx);
			}
			ConstraintStore::UserCustom(con) => con.initialize(&mut ctx),
		}
		self.constraints[con] = Some(con_store);
	}

	/// Process the model to create a [`Solver`] instance that can be used to
	/// solve it.
	///
	/// This method will return a [`Solver`] instance in addition to a
	/// [`VariableMap`], which can be used to map from [`ModelView`]
	/// to [`crate::SolverView`]. If an error occurs during the reformulation
	/// process, or if it is found to be trivially unsatisfiable, then an error
	/// will be returned.
	pub fn to_solver<Oracle: PropagatingSolver<Engine>>(
		&mut self,
		config: &InitConfig,
	) -> Result<(Solver<Oracle>, ReformulationMap), ReformulationError>
	where
		Solver<Oracle>: for<'a> From<&'a Cnf>,
		Oracle::Slv: 'static,
	{
		// TODO: run SAT simplification
		let mut slv = Solver::<Oracle>::from(&self.cnf);
		let any_slv: &mut dyn Any = slv.oracle.solver_mut();
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			r.set_option("restart", config.restart() as i32);
			r.set_option("vivify", config.vivification() as i32);
		} else {
			warn!("unknown solver: vivification and restart options are ignored");
		}

		while let Some(con) = self.prop_queue.pop_front() {
			self.propagate(con)?;
			self.enqueued[con] = false;
		}

		// TODO: Detect Views From Model

		// Create
		let bool_map = slv
			.new_var_range(self.cnf.variables())
			.map(|v| BoolView(BoolViewInner::Lit(v.into())))
			.collect();

		// Determine encoding types for integer variables
		let eager_order = HashSet::<IntDecisionIndex>::new();
		let mut eager_direct = HashSet::<IntDecisionIndex>::new();

		for c in self.constraints.iter().flatten() {
			match c {
				ConstraintStore::AllDifferentInt(c) => {
					for v in &c.vars {
						if let IntDecisionInner::Var(iv) | IntDecisionInner::Linear(_, iv) = v.0 {
							if self.int_vars[iv].domain.card() <= (c.vars.len() * 100 / 80) {
								let _ = eager_direct.insert(iv);
							}
						}
					}
				}
				ConstraintStore::ArrayIntElement(c) => {
					if let IntDecisionInner::Var(iv) | IntDecisionInner::Linear(_, iv) = c.index.0 {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::ArrayVarBoolElement(c) => {
					if let IntDecisionInner::Var(iv) | IntDecisionInner::Linear(_, iv) = c.index.0 {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::ArrayVarIntElement(c) => {
					if let IntDecisionInner::Var(iv) | IntDecisionInner::Linear(_, iv) = c.index.0 {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::TableInt(con) => {
					for &v in &con.vars {
						if let IntDecisionInner::Var(iv) | IntDecisionInner::Linear(_, iv) = v.0 {
							let _ = eager_direct.insert(iv);
						}
					}
				}
				_ => {}
			}
		}

		// Create integer data structures within the solver
		let int_map: IndexVec<IntDecisionIndex, IntView> = self
			.int_vars
			.iter_enumerated()
			.map(|(i, var)| {
				let direct_enc = if eager_direct.contains(&i) {
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				let order_enc = if eager_order.contains(&i)
					|| eager_direct.contains(&i)
					|| var.domain.card() <= config.int_eager_limit()
				{
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				SlvIntVar::new_in(&mut slv, var.domain.clone(), order_enc, direct_enc)
			})
			.collect();

		// self.cnf.variables().map(|v| slv.new_lit()).collect();
		// for (i, var) in  {
		// 	let direct_enc = if eager_direct.contains(&i) {
		// 		EncodingType::Eager
		// 	} else {
		// 		EncodingType::Lazy
		// 	};
		// 	let order_enc = if eager_order.contains(&i)
		// 		|| eager_direct.contains(&i)
		// 		|| var.domain.card() <= config.int_eager_limit()
		// 	{
		// 		EncodingType::Eager
		// 	} else {
		// 		EncodingType::Lazy
		// 	};
		// 	let view = SlvIntVar::new_in(&mut slv, var.domain.clone(), order_enc, direct_enc);
		// 	map.insert_int(i, view);
		// }
		//
		let map = ReformulationMap { bool_map, int_map };

		// Create constraint data structures within the solver
		for c in self.constraints.iter().flatten() {
			c.to_solver(&mut slv, &map)?;
		}
		// Add branching data structures to the solver
		for b in self.branchings.iter() {
			b.to_solver(&mut slv, &map);
		}

		Ok((slv, map))
	}
}

impl AddAssign<AllDifferentInt> for Model {
	fn add_assign(&mut self, constraint: AllDifferentInt) {
		self.add_constraint(ConstraintStore::AllDifferentInt(constraint));
	}
}

impl AddAssign<ArrayIntElement> for Model {
	fn add_assign(&mut self, constraint: ArrayIntElement) {
		self.add_constraint(ConstraintStore::ArrayIntElement(constraint));
	}
}

impl AddAssign<ArrayIntMinimum> for Model {
	fn add_assign(&mut self, constraint: ArrayIntMinimum) {
		self.add_constraint(ConstraintStore::ArrayIntMinimum(constraint));
	}
}

impl AddAssign<ArrayVarBoolElement> for Model {
	fn add_assign(&mut self, constraint: ArrayVarBoolElement) {
		self.add_constraint(ConstraintStore::ArrayVarBoolElement(constraint));
	}
}

impl AddAssign<ArrayVarIntElement> for Model {
	fn add_assign(&mut self, constraint: ArrayVarIntElement) {
		self.add_constraint(ConstraintStore::ArrayVarIntElement(constraint));
	}
}

impl AddAssign<Formula<BoolDecision>> for Model {
	fn add_assign(&mut self, constraint: Formula<BoolDecision>) {
		self.add_constraint(ConstraintStore::PropLogic(constraint));
	}
}

impl AddAssign<Branching> for Model {
	fn add_assign(&mut self, rhs: Branching) {
		self.branchings.push(rhs);
	}
}

impl AddAssign<BoxedConstraint> for Model {
	fn add_assign(&mut self, constraint: BoxedConstraint) {
		self.add_constraint(ConstraintStore::UserCustom(constraint));
	}
}

impl AddAssign<DisjunctiveStrict> for Model {
	fn add_assign(&mut self, constraint: DisjunctiveStrict) {
		self.add_constraint(ConstraintStore::DisjunctiveStrict(constraint));
	}
}

impl AddAssign<IntAbs> for Model {
	fn add_assign(&mut self, constraint: IntAbs) {
		self.add_constraint(ConstraintStore::IntAbs(constraint));
	}
}

impl AddAssign<IntDiv> for Model {
	fn add_assign(&mut self, constraint: IntDiv) {
		self.add_constraint(ConstraintStore::IntDiv(constraint));
	}
}

impl AddAssign<IntLinear> for Model {
	fn add_assign(&mut self, constraint: IntLinear) {
		self.add_constraint(ConstraintStore::IntLinear(constraint));
	}
}

impl AddAssign<IntPow> for Model {
	fn add_assign(&mut self, constraint: IntPow) {
		self.add_constraint(ConstraintStore::IntPow(constraint));
	}
}

impl AddAssign<IntTimes> for Model {
	fn add_assign(&mut self, constraint: IntTimes) {
		self.add_constraint(ConstraintStore::IntTimes(constraint));
	}
}

impl AddAssign<SetInReif> for Model {
	fn add_assign(&mut self, constraint: SetInReif) {
		self.add_constraint(ConstraintStore::SetInReif(constraint));
	}
}

impl AddAssign<TableInt> for Model {
	fn add_assign(&mut self, constraint: TableInt) {
		self.add_constraint(ConstraintStore::TableInt(constraint));
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

impl SimplificationActions for Model {
	fn add_constraint<C>(&mut self, constraint: C)
	where
		Model: AddAssign<C>,
	{
		*self += constraint;
	}

	fn check_int_in_domain(&self, var: IntDecision, val: IntVal) -> bool {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => self.int_vars[v].domain.contains(&val),
			Const(v) => v == val,
			Linear(t, v) => match t.rev_transform_lit(IntLitMeaning::Eq(val)) {
				Ok(IntLitMeaning::Eq(val)) => self.int_vars[v].domain.contains(&val),
				Err(false) => false,
				_ => unreachable!(),
			},
			Bool(t, _) => match t.rev_transform_lit(IntLitMeaning::Eq(val)) {
				Ok(IntLitMeaning::Eq(val)) => val == 0 || val == 1,
				Err(false) => false,
				_ => unreachable!(),
			},
		}
	}

	fn get_bool_val(&self, _: BoolDecision) -> Option<bool> {
		None // TODO
	}

	fn get_int_lower_bound(&self, var: IntDecision) -> IntVal {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let def = &self.int_vars[v];
				*def.domain.lower_bound().unwrap()
			}
			Const(v) => v,
			Linear(t, v) => {
				let def = &self.int_vars[v];
				if t.positive_scale() {
					t.transform(*def.domain.lower_bound().unwrap())
				} else {
					t.transform(*def.domain.upper_bound().unwrap())
				}
			}
			Bool(t, bv) => {
				let val = self.get_bool_val(bv).unwrap_or(false) as IntVal;
				if t.positive_scale() {
					t.transform(val)
				} else {
					t.transform(1 - val)
				}
			}
		}
	}

	fn get_int_upper_bound(&self, var: IntDecision) -> IntVal {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let def = &self.int_vars[v];
				*def.domain.upper_bound().unwrap()
			}
			Const(v) => v,
			Linear(t, v) => {
				let def = &self.int_vars[v];
				if t.positive_scale() {
					t.transform(*def.domain.upper_bound().unwrap())
				} else {
					t.transform(*def.domain.lower_bound().unwrap())
				}
			}
			Bool(t, bv) => {
				let val = self.get_bool_val(bv).unwrap_or(true) as IntVal;
				if t.positive_scale() {
					t.transform(val)
				} else {
					t.transform(1 - val)
				}
			}
		}
	}

	fn set_bool(&mut self, var: BoolDecision) -> Result<(), ReformulationError> {
		use BoolDecisionInner::*;

		match var.0 {
			Lit(l) => Ok(self.cnf.add_clause([l])?),
			Const(true) => Ok(()),
			Const(false) => Err(ReformulationError::TrivialUnsatisfiable),
			IntEq(iv, val) => self.set_int_val(IntDecision(IntDecisionInner::Var(iv)), val),
			IntGreaterEq(iv, val) => {
				self.set_int_lower_bound(IntDecision(IntDecisionInner::Var(iv)), val)
			}
			IntLess(iv, val) => {
				self.set_int_upper_bound(IntDecision(IntDecisionInner::Var(iv)), val - 1)
			}
			IntNotEq(iv, val) => self.set_int_not_eq(IntDecision(IntDecisionInner::Var(iv)), val),
		}
	}

	fn set_int_in_set(
		&mut self,
		var: IntDecision,
		values: &IntSetVal,
	) -> Result<(), ReformulationError> {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let intersect: RangeList<_> = self.int_vars[v].domain.intersect(values);
				if intersect.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v].domain == intersect {
					return Ok(());
				}
				self.int_vars[v].domain = intersect;
				let constraints = self.int_vars[v].constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			Const(v) => {
				if !values.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			Linear(trans, iv) => {
				let values = trans.rev_transform_int_set(values);
				self.set_int_in_set(IntDecision(Var(iv)), &values)
			}
			Bool(trans, b) => {
				let values = trans.rev_transform_int_set(values);
				if !values.contains(&0) {
					self.set_bool(b)?;
				}
				if !values.contains(&1) {
					self.set_bool(!b)?;
				}
				Ok(())
			}
		}
	}

	fn set_int_lower_bound(
		&mut self,
		var: IntDecision,
		lb: IntVal,
	) -> Result<(), ReformulationError> {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let def = &mut self.int_vars[v];
				if lb <= *def.domain.lower_bound().unwrap() {
					return Ok(());
				} else if lb > *def.domain.upper_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if *r.end() < lb {
						None
					} else if *r.start() < lb {
						Some(lb..=*r.end())
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			Const(v) if v < lb => Err(ReformulationError::TrivialUnsatisfiable),
			Const(_) => Ok(()),
			Linear(trans, iv) => match trans.rev_transform_lit(IntLitMeaning::GreaterEq(lb)) {
				Ok(IntLitMeaning::GreaterEq(val)) => {
					self.set_int_lower_bound(IntDecision(Var(iv)), val)
				}
				Ok(IntLitMeaning::Less(val)) => {
					self.set_int_upper_bound(IntDecision(Var(iv)), val - 1)
				}
				_ => unreachable!(),
			},
			Bool(trans, b) => match trans.rev_transform_lit(IntLitMeaning::GreaterEq(lb)) {
				Ok(IntLitMeaning::GreaterEq(1)) => self.set_bool(b),
				Ok(IntLitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(IntLitMeaning::GreaterEq(_)) => Ok(()),
				Ok(IntLitMeaning::Less(1)) => self.set_bool(!b),
				Ok(IntLitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(IntLitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	fn set_int_upper_bound(
		&mut self,
		var: IntDecision,
		ub: IntVal,
	) -> Result<(), ReformulationError> {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let def = &mut self.int_vars[v];
				if ub >= *def.domain.upper_bound().unwrap() {
					return Ok(());
				} else if ub < *def.domain.lower_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if ub < *r.start() {
						None
					} else if ub < *r.end() {
						Some(*r.start()..=ub)
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			Const(v) if v > ub => Err(ReformulationError::TrivialUnsatisfiable),
			Const(_) => Ok(()),
			Linear(trans, iv) => match trans.rev_transform_lit(IntLitMeaning::Less(ub + 1)) {
				Ok(IntLitMeaning::GreaterEq(val)) => {
					self.set_int_lower_bound(IntDecision(Var(iv)), val)
				}
				Ok(IntLitMeaning::Less(val)) => {
					self.set_int_upper_bound(IntDecision(Var(iv)), val - 1)
				}
				_ => unreachable!(),
			},
			Bool(trans, b) => match trans.rev_transform_lit(IntLitMeaning::Less(ub + 1)) {
				Ok(IntLitMeaning::GreaterEq(1)) => self.set_bool(b),
				Ok(IntLitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(IntLitMeaning::GreaterEq(_)) => Ok(()),
				Ok(IntLitMeaning::Less(1)) => self.set_bool(!b),
				Ok(IntLitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(IntLitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	fn set_int_val(&mut self, var: IntDecision, val: IntVal) -> Result<(), ReformulationError> {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let def = &mut self.int_vars[v];
				if def.domain.contains(&val) {
					def.domain = RangeList::from(val..=val);
					let constraints = def.constraints.clone();
					for c in constraints {
						self.enqueue(c);
					}
					Ok(())
				} else {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
			}
			Const(i) if i == val => Ok(()),
			Const(_) => Err(ReformulationError::TrivialUnsatisfiable),
			Linear(trans, iv) => match trans.rev_transform_lit(IntLitMeaning::Eq(val)) {
				Ok(IntLitMeaning::Eq(val)) => self.set_int_val(IntDecision(Var(iv)), val),
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
			Bool(trans, b) => match trans.rev_transform_lit(IntLitMeaning::Eq(val)) {
				Ok(IntLitMeaning::Eq(val)) => match val {
					0 => self.set_bool(!b),
					1 => self.set_bool(b),
					_ => Err(ReformulationError::TrivialUnsatisfiable),
				},
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
		}
	}

	fn set_int_not_eq(&mut self, var: IntDecision, val: IntVal) -> Result<(), ReformulationError> {
		self.set_int_in_set(var, &(val..=val).into())
	}

	fn set_int_not_in_set(
		&mut self,
		var: IntDecision,
		values: &IntSetVal,
	) -> Result<(), ReformulationError> {
		use IntDecisionInner::*;

		match var.0 {
			Var(v) => {
				let diff: RangeList<_> = self.int_vars[v].domain.diff(values);
				if diff.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v].domain == diff {
					return Ok(());
				}
				self.int_vars[v].domain = diff;
				let constraints = self.int_vars[v].constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			Const(v) => {
				if values.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			Linear(trans, iv) => {
				let mask = trans.rev_transform_int_set(values);
				self.set_int_not_in_set(IntDecision(Var(iv)), &mask)
			}
			Bool(trans, b) => {
				let values = trans.rev_transform_int_set(values);
				if values.contains(&0) {
					self.set_bool(b)?;
				}
				if values.contains(&1) {
					self.set_bool(!b)?;
				}
				Ok(())
			}
		}
	}
}
