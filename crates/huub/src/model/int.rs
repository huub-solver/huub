use flatzinc_serde::RangeList;

use crate::{
	model::{reformulate::SimplifiedInt, ReifContext},
	solver::SatSolver,
	SimplifiedVariable, Solver, Variable, VariableMap,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntExpr {
	Var(IntVar),
	Val(i64),
}

impl IntExpr {
	pub(crate) fn to_arg<S: SatSolver>(
		&self,
		_ctx: ReifContext,
		_slv: &mut Solver<S>,
		map: &mut VariableMap,
	) -> SimplifiedInt {
		match self {
			IntExpr::Var(v) => {
				if let SimplifiedVariable::Int(i) = map.get(&Variable::Int(*v)) {
					i
				} else {
					unreachable!()
				}
			}
			IntExpr::Val(v) => SimplifiedInt::Val(*v),
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntVar(pub(crate) u32);

#[derive(Debug)]
pub(crate) struct IntVarDef {
	pub(crate) domain: RangeList<i64>,
}
