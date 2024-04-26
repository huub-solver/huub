use flatzinc_serde::RangeList;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use super::reformulate::{ReifContext, VariableMap};
use crate::{
	solver::{view::IntViewInner, SatSolver},
	IntView, Solver, SolverView, Variable,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntExpr {
	Var(IntVar),
	Val(i64),
}

impl IntExpr {
	pub(crate) fn to_arg<
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	>(
		&self,
		_ctx: ReifContext,
		_slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> IntView {
		match self {
			IntExpr::Var(v) => {
				if let SolverView::Int(i) = map.get(&Variable::Int(*v)) {
					i
				} else {
					unreachable!()
				}
			}
			IntExpr::Val(v) => IntView(IntViewInner::Const(*v)),
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntVar(pub(crate) u32);

#[derive(Debug)]
pub(crate) struct IntVarDef {
	pub(crate) domain: RangeList<i64>,
}
