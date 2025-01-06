//! Module containing the solution values that will be returned when when
//! inspecting a solution.

use std::{fmt::Display, num::NonZeroI64};

use pindakaas::solver::FailedAssumtions;
use rangelist::RangeList;

use crate::solver::{
	view::{BoolView, BoolViewInner},
	SolverView,
};

/// Trait implemented by the object given to the callback on detecting failure
pub trait AssumptionChecker {
	/// Check if the given assumption literal was used to prove the unsatisfiability
	/// of the formula under the assumptions used for the last SAT search.
	///
	/// Note that for literals 'bv' which are not assumption literals, the behavior
	/// of is not specified.
	fn fail(&self, bv: BoolView) -> bool;
}

/// Type alias for a set of integers parameter value.
pub type IntSetVal = RangeList<IntVal>;

/// Type alias for an parameter integer value.
pub type IntVal = i64;

/// An assumption checker that can be used when no assumptions are used.
///
/// Note that this checker will always return false.
pub(crate) struct NoAssumptions;

/// Type alias for a non-zero paremeter integer value.
pub type NonZeroIntVal = NonZeroI64;

/// A trait for a function that can be used to evaluate a `SolverView` to a
/// `Value`, which can be used when inspecting a solution.
pub trait Valuation: Fn(SolverView) -> Value {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(variant_size_differences, reason = "`Int` cannot be as smal as `Bool`")]
/// The general representation of a solution value in the solver.
pub enum Value {
	/// A Boolean value.
	Bool(bool),
	/// An integer value.
	Int(IntVal),
}

impl<A: FailedAssumtions> AssumptionChecker for A {
	fn fail(&self, bv: BoolView) -> bool {
		match bv {
			BoolView(BoolViewInner::Lit(lit)) => self.fail(lit),
			BoolView(BoolViewInner::Const(false)) => true,
			BoolView(BoolViewInner::Const(true)) => false,
		}
	}
}

impl<F: Fn(SolverView) -> Value> Valuation for F {}

impl AssumptionChecker for NoAssumptions {
	fn fail(&self, bv: BoolView) -> bool {
		matches!(bv, BoolView(BoolViewInner::Const(false)))
	}
}

impl Value {
	/// If the `Value` is a Boolean, represent it as bool. Returns None otherwise.
	pub fn as_bool(&self) -> Option<bool> {
		match self {
			Value::Bool(b) => Some(*b),
			_ => None,
		}
	}
	/// If the `Value` is an integer, represent it as `IntVal`. Returns None
	/// otherwise.
	pub fn as_int(&self) -> Option<IntVal> {
		match self {
			Value::Int(i) => Some(*i),
			_ => None,
		}
	}
}

impl Display for Value {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Value::Bool(b) => write!(f, "{b}"),
			Value::Int(i) => write!(f, "{i}"),
		}
	}
}
