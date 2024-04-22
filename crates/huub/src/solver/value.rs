use super::engine::int_var::IntVal;
use crate::solver::SolverView;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Value {
	Bool(bool),
	Int(IntVal),
}

pub trait Valuation: Fn(SolverView) -> Option<Value> {}
impl<F: Fn(SolverView) -> Option<Value>> Valuation for F {}
