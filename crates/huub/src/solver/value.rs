use std::{fmt::Display, num::NonZeroI64};

use crate::solver::SolverView;

#[derive(Debug, PartialEq, Eq, Hash)]
#[allow(variant_size_differences)]
pub enum Value {
	Bool(bool),
	Int(IntVal),
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
