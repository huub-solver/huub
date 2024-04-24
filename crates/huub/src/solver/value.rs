use std::fmt::Display;

use super::engine::int_var::IntVal;
use crate::solver::SolverView;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Value {
	Bool(bool),
	Int(IntVal),
}

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
