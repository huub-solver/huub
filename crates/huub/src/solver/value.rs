use std::{fmt::Display, num::NonZeroI64};

use pindakaas::solver::FailedAssumtions;

use super::view::BoolViewInner;
use crate::{solver::SolverView, BoolView};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(variant_size_differences)]
pub enum Value {
	Bool(bool),
	Int(IntVal),
}

impl Value {
	/// If the `Value` is an integer, represent it as `IntVal`. Returns None otherwise.
	pub fn as_int(&self) -> Option<IntVal> {
		match self {
			Value::Int(i) => Some(*i),
			_ => None,
		}
	}
	/// If the `Value` is a Boolean, represent it as bool. Returns None otherwise.
	pub fn as_bool(&self) -> Option<bool> {
		match self {
			Value::Bool(b) => Some(*b),
			_ => None,
		}
	}
}

pub type IntVal = i64;
pub type NonZeroIntVal = NonZeroI64;

pub trait Valuation: Fn(SolverView) -> Option<Value> {}
impl<F: Fn(SolverView) -> Option<Value>> Valuation for F {}

impl Display for Value {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Value::Bool(b) => write!(f, "{b}"),
			Value::Int(i) => write!(f, "{i}"),
		}
	}
}

/// Trait implemented by the object given to the callback on detecting failure
pub trait AssumptionChecker {
	/// Check if the given assumption literal was used to prove the unsatisfiability
	/// of the formula under the assumptions used for the last SAT search.
	///
	/// Note that for literals 'bv' which are not assumption literals, the behavior
	/// of is not specified.
	fn fail(&self, bv: BoolView) -> bool;
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
pub(crate) struct ConstantFailure;
impl AssumptionChecker for ConstantFailure {
	fn fail(&self, bv: BoolView) -> bool {
		matches!(bv, BoolView(BoolViewInner::Const(false)))
	}
}
