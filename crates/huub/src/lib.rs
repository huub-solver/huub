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
pub(crate) mod helpers;
pub(crate) mod model;
pub(crate) mod solver;
#[cfg(test)]
pub(crate) mod tests;

use std::{
	any::Any,
	collections::{HashSet, VecDeque},
	iter::{repeat, Sum},
	ops::{Add, AddAssign, Mul, Sub},
};

use index_vec::IndexVec;
use itertools::Itertools;
pub use pindakaas::solver::SlvTermSignal;
use pindakaas::{
	propositional_logic::Formula,
	solver::{cadical::Cadical, propagation::PropagatingSolver},
	ClauseDatabase, ClauseDatabaseTools, Cnf, Lit as RawLit, Unsatisfiable,
};
use rangelist::IntervalIterator;
use tracing::warn;

// TODO: Remove this re-export
pub(crate) use crate::model::constraint::ConstraintStore;
use crate::{
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
		BoxedConstraint,
	},
	model::{
		bool::BoolView as ModelBoolView,
		branching::Branching,
		int::{IntExpr, IntVar, IntVarDef},
		reformulate::VariableMap,
	},
	solver::{
		engine::Engine,
		int_var::{EncodingType, IntVar as SlvIntVar},
	},
};
pub use crate::{
	helpers::linear_transform::LinearTransform,
	model::{
		flatzinc::{FlatZincError, FlatZincStatistics},
		reformulate::{InitConfig, ReformulationError},
	},
	solver::{
		int_var::LitMeaning,
		value::{IntSetVal, IntVal, NonZeroIntVal, Valuation, Value},
		view::{IntView, SolverView},
		Goal, SolveResult, Solver,
	},
};

/// Type alias for a disjunction of literals (clause), used for internal type
/// documentation.
type Clause<L = RawLit> = Vec<L>;

/// Type alias for a conjunction of literals (clause), used for internal type
/// documentation.
type Conjunction<L = RawLit> = Vec<L>;

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
	terms: Vec<IntExpr>,
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
	constraints: Vec<Option<ConstraintStore>>,
	/// The definitions of the integer variables that have been created.
	int_vars: IndexVec<IntVar, IntVarDef>,
	/// A queue of indexes of constraints that need to be propagated.
	prop_queue: VecDeque<usize>,
	/// A flag for each constraint whether it has been enqueued for propagation.
	enqueued: Vec<bool>,
}

/// Create a `all_different_int` constraint that enforces that all the given
/// integer decisions take different values.
pub fn all_different_int<Iter>(vars: Iter) -> AllDifferentInt
where
	Iter: IntoIterator,
	Iter::Item: Into<IntExpr>,
{
	AllDifferentInt {
		vars: vars.into_iter().map_into().collect(),
	}
}

/// Create an `array_int_element` constraint that enforces that a result integer
/// decision variable takes the value equal the element of the given array of
/// integer values at the given index decision variable.
pub fn array_int_element(index: IntExpr, array: Vec<IntVal>, result: IntExpr) -> ArrayIntElement {
	ArrayIntElement {
		index,
		array,
		result,
	}
}

/// Create an `array_int_maximum` constraint that enforces that an integer
/// decision variable takes the minimum value of an array of integer decision
/// variables.
pub fn array_int_maximum<Iter>(vars: Iter, max: IntExpr) -> ArrayIntMinimum
where
	Iter: IntoIterator,
	Iter::Item: Into<IntExpr>,
{
	array_int_minimum(vars.into_iter().map(|v| -v.into()), -max)
}

/// Create an `array_int_minimum` constraint that enforces that an integer
/// decision variable takes the minimum value of an array of integer decision
/// variables.
pub fn array_int_minimum<Iter>(vars: Iter, min: IntExpr) -> ArrayIntMinimum
where
	Iter: IntoIterator,
	Iter::Item: Into<IntExpr>,
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
	index: IntExpr,
	array: Vec<ModelBoolView>,
	result: ModelBoolView,
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
pub fn disjunctive_strict(start_times: Vec<IntExpr>, durations: Vec<IntVal>) -> DisjunctiveStrict {
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
	index: IntExpr,
	array: Vec<IntExpr>,
	result: IntExpr,
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
pub fn int_abs(origin: IntExpr, abs: IntExpr) -> IntAbs {
	IntAbs { origin, abs }
}

/// Create an `int_div` constraint that enforces that a numerator decision
/// integer variable divided by a denominator integer decision variable is equal
/// to a result integer decision variable.
pub fn int_div(numerator: IntExpr, denominator: IntExpr, result: IntExpr) -> IntDiv {
	IntDiv {
		numerator,
		denominator,
		result,
	}
}

/// Create an `int_pow` constraint that enforces that a base integer decision
/// variable exponentiated by an exponent integer decision variable is equal to
/// a result integer decision variable.
pub fn int_pow(base: IntExpr, exponent: IntExpr, result: IntExpr) -> IntPow {
	IntPow {
		base,
		exponent,
		result,
	}
}

/// Create an `int_times` constraint that enforces that the product of the two
/// integer decision variables is equal to a third.
pub fn int_times(factor1: IntExpr, factor2: IntExpr, product: IntExpr) -> IntTimes {
	IntTimes {
		factor1,
		factor2,
		product,
	}
}

/// Create a `set_in_reif` constraint that enforces that the given Boolean
/// variable takes the value `true` if-and-only-if an integer variable is in a
/// given set.
pub fn set_in_reif(var: IntExpr, set: IntSetVal, reif: ModelBoolView) -> SetInReif {
	SetInReif { var, set, reif }
}

/// Create a `table_int` constraint that enforces that given list of integer
/// views take their values according to one of the given lists of integer
/// values.
pub fn table_int(vars: Vec<IntExpr>, table: Vec<Vec<IntVal>>) -> TableInt {
	assert!(table.iter().all(|tup| tup.len() == vars.len()), "The number of values in each row of the table must be equal to the number of decision variables.");
	TableInt { vars, table }
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

impl Add<IntExpr> for IntLinExpr {
	type Output = IntLinExpr;

	fn add(self, rhs: IntExpr) -> Self::Output {
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

impl Sub<IntExpr> for IntLinExpr {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntExpr) -> Self::Output {
		self + -rhs
	}
}

impl Sub<IntVal> for IntLinExpr {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl Sum<IntExpr> for IntLinExpr {
	fn sum<I: Iterator<Item = IntExpr>>(iter: I) -> Self {
		IntLinExpr {
			terms: iter.collect(),
		}
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

	/// Create a new Boolean variable.
	pub fn new_bool_var(&mut self) -> ModelBoolView {
		ModelBoolView::Lit(self.cnf.new_lit())
	}

	/// Create `len` new Boolean variables.
	pub fn new_bool_vars(&mut self, len: usize) -> Vec<ModelBoolView> {
		self.cnf
			.new_var_range(len)
			.map(|v| ModelBoolView::Lit(v.into()))
			.collect()
	}

	/// Create a new integer variable with the given domain.
	pub fn new_int_var(&mut self, domain: IntSetVal) -> IntExpr {
		IntExpr::Var(self.int_vars.push(IntVarDef::with_domain(domain)))
	}

	/// Create `len` new integer variables with the given domain.
	pub fn new_int_vars(&mut self, len: usize, domain: IntSetVal) -> Vec<IntVar> {
		repeat(IntVarDef::with_domain(domain))
			.take(len)
			.map(|v| self.int_vars.push(v))
			.collect()
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
	) -> Result<(Solver<Oracle>, VariableMap), ReformulationError>
	where
		Solver<Oracle>: for<'a> From<&'a Cnf>,
		Oracle::Slv: 'static,
	{
		let mut map = VariableMap::default();

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

		// Determine encoding types for integer variables
		let eager_order = HashSet::<IntVar>::new();
		let mut eager_direct = HashSet::<IntVar>::new();

		for c in self.constraints.iter().flatten() {
			match c {
				ConstraintStore::AllDifferentInt(c) => {
					for v in &c.vars {
						if let IntExpr::Var(iv) | IntExpr::Linear(_, iv) = v {
							if self.int_vars[*iv].domain.card() <= (c.vars.len() * 100 / 80) {
								let _ = eager_direct.insert(*iv);
							}
						}
					}
				}
				ConstraintStore::ArrayIntElement(c) => {
					if let IntExpr::Var(iv) | IntExpr::Linear(_, iv) = c.index {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::ArrayVarBoolElement(c) => {
					if let IntExpr::Var(iv) | IntExpr::Linear(_, iv) = c.index {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::ArrayVarIntElement(c) => {
					if let IntExpr::Var(iv) | IntExpr::Linear(_, iv) = c.index {
						let _ = eager_direct.insert(iv);
					}
				}
				ConstraintStore::TableInt(con) => {
					for &v in &con.vars {
						if let IntExpr::Var(iv) | IntExpr::Linear(_, iv) = v {
							let _ = eager_direct.insert(iv);
						}
					}
				}
				_ => {}
			}
		}

		// Create integer data structures within the solver
		for (i, var) in self.int_vars.iter_enumerated() {
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
			let view = SlvIntVar::new_in(&mut slv, var.domain.clone(), order_enc, direct_enc);
			map.insert_int(i, view);
		}

		// Create constraint data structures within the solver
		for c in self.constraints.iter().flatten() {
			c.to_solver(&mut slv, &mut map)?;
		}
		// Add branching data structures to the solver
		for b in self.branchings.iter() {
			b.to_solver(&mut slv, &mut map);
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

impl AddAssign<Formula<ModelBoolView>> for Model {
	fn add_assign(&mut self, constraint: Formula<ModelBoolView>) {
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
