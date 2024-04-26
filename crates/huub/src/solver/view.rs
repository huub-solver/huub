use std::num::NonZeroI32;

use pindakaas::Lit as RawLit;

use super::engine::int_var::{IntVal, LitMeaning};
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
	pub fn add_to_reverse_map<S: Clone, M: Extend<(NonZeroI32, (S, bool))>>(
		&self,
		map: &mut M,
		name: S,
	) {
		let i: NonZeroI32 = self.0.into();
		map.extend([(i, (name.clone(), true)), (-i, (name, false))])
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntView(pub(crate) IntViewInner);

impl IntView {
	pub fn add_to_lit_reverse_map<Sat: SatSolver, M: Extend<(NonZeroI32, (usize, LitMeaning))>>(
		&self,
		slv: &Solver<Sat>,
		map: &mut M,
	) {
		match self.0 {
			IntViewInner::VarRef(v) => {
				let var = &slv.engine().int_vars[v];
				let mut var_iter = var.vars.clone();
				let pos = v.into();

				let mut val_iter = var.orig_domain.clone().into_iter().flatten();
				val_iter.next().unwrap();
				for val in val_iter {
					let lit = var_iter.next().unwrap();
					let i: NonZeroI32 = lit.into();
					map.extend([
						(i, (pos, LitMeaning::GreaterEq(val))),
						(-i, (pos, LitMeaning::Less(val))),
					])
				}

				if var.has_direct && var.orig_domain_len > 2 {
					let mut val_iter = var.orig_domain.clone().into_iter().flatten();
					val_iter.next().unwrap();
					val_iter.next_back().unwrap();
					for val in val_iter {
						let lit = var_iter.next().unwrap();
						let i: NonZeroI32 = lit.into();
						map.extend([
							(i, (pos, LitMeaning::Eq(val))),
							(-i, (pos, LitMeaning::NotEq(val))),
						])
					}
				}

				debug_assert!(var_iter.next().is_none());
			}
			IntViewInner::Const(_) => {}
		}
	}

	pub fn add_to_int_reverse_map<E>(&self, map: &mut [E], name: E) {
		match self.0 {
			IntViewInner::VarRef(v) => {
				let pos: usize = v.into();
				map[pos] = name;
			}
			IntViewInner::Const(_) => {}
		}
	}
}

impl From<IntVal> for IntView {
	fn from(value: IntVal) -> Self {
		Self(IntViewInner::Const(value))
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum IntViewInner {
	VarRef(IntVarRef),
	Const(IntVal),
}
