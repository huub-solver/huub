use flatzinc_serde::RangeList;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use super::reformulate::{ReifContext, VariableMap};
use crate::{
	solver::{
		view::{IntView, IntViewInner, SolverView},
		SatSolver,
	},
	IntVal, Solver, Variable,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntExpr {
	Var(IntVar),
	Val(IntVal),
}

impl IntExpr {
	pub(crate) fn to_arg<Sol, Sat>(
		&self,
		_ctx: ReifContext,
		_slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> IntView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
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
	pub(crate) domain: RangeList<IntVal>,
}
