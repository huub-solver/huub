use std::num::NonZeroI32;

use pindakaas::Lit as RawLit;

use crate::{solver::engine::int_var::IntVarRef, solver::SatSolver, Solver};

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

impl BoolView {
	pub fn add_to_reverse_map<M: Extend<(NonZeroI32, String)>>(&self, map: &mut M, name: &str) {
		let i: NonZeroI32 = self.0.into();
		map.extend([(i, name.to_string()), (-i, format!("not {name}"))])
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntView(pub(crate) IntViewInner);

impl IntView {
	pub fn add_to_lit_reverse_map<Sat: SatSolver, M: Extend<(NonZeroI32, String)>>(
		&self,
		slv: &Solver<Sat>,
		map: &mut M,
		name: &str,
	) {
		match self.0 {
			IntViewInner::VarRef(v) => {
				let var = &slv.engine().int_vars[v];
				// eprintln!("one_hot: {:?}", var.one_hot);
				// eprintln!("dom: {:?}", var.orig_domain);
				for (lit, val) in var
					.one_hot
					.clone()
					.zip(var.orig_domain.clone().into_iter().flatten())
				{
					let i: NonZeroI32 = lit.into();
					map.extend([(i, format!("{name}={val}")), (-i, format!("{name}!={val}"))])
				}
			}
		}
	}
	pub fn add_to_int_reverse_map<M: Extend<(usize, String)>>(&self, map: &mut M, name: &str) {
		match self.0 {
			IntViewInner::VarRef(v) => map.extend([(v.into(), name.to_string())]),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum IntViewInner {
	VarRef(IntVarRef),
}
