use std::num::NonZeroI32;

use pindakaas::Lit as RawLit;

use crate::{
	solver::{engine::int_var::IntVarRef, SatSolver},
	Solver,
};

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
				let mut var_iter = var.vars.clone().into_iter();

				let mut val_iter = var.orig_domain.clone().into_iter().flatten();
				val_iter.next().unwrap();
				while let Some(val) = val_iter.next() {
					let lit = var_iter.next().unwrap();
					let i: NonZeroI32 = lit.into();
					map.extend([(i, format!("{name}>={val}")), (-i, format!("{name}<{val}"))])
				}

				if var.has_direct && var.orig_domain_len > 2 {
					let mut val_iter = var.orig_domain.clone().into_iter().flatten();
					val_iter.next().unwrap();
					val_iter.next_back().unwrap();
					while let Some(val) = val_iter.next() {
						let lit = var_iter.next().unwrap();
						let i: NonZeroI32 = lit.into();
						map.extend([(i, format!("{name}={val}")), (-i, format!("{name}!={val}"))])
					}
				}

				debug_assert!(var_iter.next().is_none());
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
