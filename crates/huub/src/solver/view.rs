use pindakaas::Lit as RawLit;

use crate::solver::engine::int_var::IntVarRef;

pub enum SolverView {
	Bool(BoolView),
	Int(IntView),
}

impl From<BoolView> for SolverView {
	fn from(value: BoolView) -> Self {
		Self::Bool(value)
	}
}
impl From<&BoolView> for SolverView {
	fn from(value: &BoolView) -> Self {
		Self::Bool(*value)
	}
}
impl From<IntView> for SolverView {
	fn from(value: IntView) -> Self {
		Self::Int(value)
	}
}
impl From<&IntView> for SolverView {
	fn from(value: &IntView) -> Self {
		Self::Int(*value)
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolView(pub(crate) RawLit);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntView(pub(crate) IntViewInner);

impl IntView {
	// pub fn lower_bound(&self, x: &impl State) {}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum IntViewInner {
	VarRef(IntVarRef),
}
