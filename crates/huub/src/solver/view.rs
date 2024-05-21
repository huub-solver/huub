use std::{
	num::NonZeroI32,
	ops::{Add, Mul, Neg, Not},
};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Lit as RawLit, Valuation as SatValuation,
};

use super::{engine::int_var::LitMeaning, value::NonZeroIntVal};
use crate::{
	helpers::linear_transform::LinearTransform,
	solver::{engine::int_var::IntVarRef, SatSolver},
	IntVal, Solver,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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
pub struct BoolView(pub(crate) BoolViewInner);

impl BoolView {
	pub fn add_to_reverse_map<S: Clone, M: Extend<(NonZeroI32, (S, bool))>>(
		&self,
		map: &mut M,
		name: S,
	) {
		match self.0 {
			BoolViewInner::Lit(v) => {
				let i: NonZeroI32 = v.into();
				map.extend([(i, (name.clone(), true)), (-i, (name, false))])
			}
			BoolViewInner::Const(_) => {}
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(variant_size_differences)]
pub(crate) enum BoolViewInner {
	Lit(RawLit),
	Const(bool),
}

impl Not for BoolView {
	type Output = Self;

	fn not(self) -> Self::Output {
		match self.0 {
			BoolViewInner::Lit(l) => BoolView(BoolViewInner::Lit(!l)),
			BoolViewInner::Const(b) => BoolView(BoolViewInner::Const(!b)),
		}
	}
}
impl Not for &BoolView {
	type Output = BoolView;

	fn not(self) -> Self::Output {
		match self.0 {
			BoolViewInner::Lit(l) => BoolView(BoolViewInner::Lit(!l)),
			BoolViewInner::Const(b) => BoolView(BoolViewInner::Const(!b)),
		}
	}
}

impl From<bool> for BoolView {
	fn from(value: bool) -> Self {
		BoolView(BoolViewInner::Const(value))
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntView(pub(crate) IntViewInner);

impl IntView {
	pub fn add_to_lit_reverse_map<Sol, Sat, M>(&self, slv: &Solver<Sat>, map: &mut M)
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
		M: Extend<(NonZeroI32, (usize, LitMeaning))>,
	{
		if let IntViewInner::VarRef(v) = self.0 {
			let var = &slv.engine().state.int_vars[v];
			let mut var_iter = var.vars.clone();
			let pos = v.into();

			let mut val_iter = var.orig_domain.clone().into_iter().flatten();
			let _ = val_iter.next();
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
				let _ = val_iter.next();
				let _ = val_iter.next_back();
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
	}

	pub fn add_to_int_reverse_map<E>(&self, map: &mut [E], name: E) {
		if let IntViewInner::VarRef(v) = self.0 {
			let pos: usize = v.into();
			map[pos] = name;
		}
	}
}

impl From<IntVal> for IntView {
	fn from(value: IntVal) -> Self {
		Self(IntViewInner::Const(value))
	}
}
impl From<BoolView> for IntView {
	fn from(value: BoolView) -> Self {
		Self(match value.0 {
			BoolViewInner::Lit(l) => IntViewInner::Bool {
				transformer: LinearTransform::offset(0),
				lit: l,
			},
			BoolViewInner::Const(c) => IntViewInner::Const(c as IntVal),
		})
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum IntViewInner {
	/// (Raw) Integer Variable
	/// Reference to location in the Engine's State
	VarRef(IntVarRef),
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear {
		transformer: LinearTransform,
		var: IntVarRef,
	},
	/// Linear View of an Boolean Literal
	Bool {
		transformer: LinearTransform,
		lit: RawLit,
	},
}

impl Neg for IntView {
	type Output = Self;
	fn neg(self) -> Self::Output {
		Self(match self.0 {
			IntViewInner::VarRef(var) => IntViewInner::Linear {
				transformer: LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()),
				var,
			},
			IntViewInner::Const(i) => IntViewInner::Const(-i),
			IntViewInner::Linear {
				transformer: transform,
				var,
			} => IntViewInner::Linear {
				transformer: -transform,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: -transformer,
				lit,
			},
		})
	}
}

impl Add<IntVal> for IntView {
	type Output = Self;
	fn add(self, rhs: IntVal) -> Self::Output {
		Self(match self.0 {
			IntViewInner::VarRef(var) => IntViewInner::Linear {
				transformer: LinearTransform::offset(rhs),
				var,
			},
			IntViewInner::Const(i) => IntViewInner::Const(i + rhs),
			IntViewInner::Linear {
				transformer: transform,
				var,
			} => IntViewInner::Linear {
				transformer: transform + rhs,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: transformer + rhs,
				lit,
			},
		})
	}
}

impl Mul<NonZeroIntVal> for IntView {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		Self(match self.0 {
			IntViewInner::VarRef(iv) => IntViewInner::Linear {
				transformer: LinearTransform::scaled(rhs),
				var: iv,
			},
			IntViewInner::Const(c) => IntViewInner::Const(c * rhs.get()),
			IntViewInner::Linear { transformer, var } => IntViewInner::Linear {
				transformer: transformer * rhs,
				var,
			},
			IntViewInner::Bool { transformer, lit } => IntViewInner::Bool {
				transformer: transformer * rhs,
				lit,
			},
		})
	}
}
