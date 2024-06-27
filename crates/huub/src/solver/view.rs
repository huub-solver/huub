use std::{
	num::NonZeroI32,
	ops::{Add, Mul, Neg, Not},
};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Lit as RawLit, Valuation as SatValuation,
};

use crate::{
	helpers::linear_transform::LinearTransform,
	solver::{
		engine::int_var::{DirectStorage, IntVarRef, LitMeaning, OrderStorage},
		value::NonZeroIntVal,
		SatSolver,
	},
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
	pub fn reverse_map_info(&self) -> Option<NonZeroI32> {
		match self.0 {
			BoolViewInner::Lit(v) => Some(v.into()),
			BoolViewInner::Const(_) => None,
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
	pub fn lit_reverse_map_info<Sol, Sat>(&self, slv: &Solver<Sat>) -> Vec<(NonZeroI32, LitMeaning)>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let transformer = match self.0 {
			IntViewInner::Bool { transformer, .. } | IntViewInner::Linear { transformer, .. } => {
				transformer
			}
			_ => LinearTransform::default(),
		};
		match self.0 {
			IntViewInner::VarRef(v) | IntViewInner::Linear { var: v, .. } => {
				let var = &slv.engine().state.int_vars[v];
				let mut lits = Vec::new();

				if let OrderStorage::Eager { storage, .. } = &var.order_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					let _ = val_iter.next();
					for (lit, val) in storage.clone().zip(val_iter) {
						let i: NonZeroI32 = lit.into();
						let geq = LitMeaning::GreaterEq(transformer.transform(val));
						let lt = LitMeaning::Less(transformer.transform(val));
						lits.extend([(i, geq), (-i, lt)])
					}
				}

				if let DirectStorage::Eager(vars) = &var.direct_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					let _ = val_iter.next();
					let _ = val_iter.next_back();
					for (lit, val) in vars.clone().zip(val_iter) {
						let i: NonZeroI32 = lit.into();
						let eq = LitMeaning::Eq(transformer.transform(val));
						let ne = LitMeaning::NotEq(transformer.transform(val));
						lits.extend([(i, eq), (-i, ne)])
					}
				}
				lits
			}
			IntViewInner::Bool { lit, .. } => {
				let i: NonZeroI32 = lit.into();
				let lb = LitMeaning::Eq(transformer.transform(0));
				let ub = LitMeaning::Eq(transformer.transform(1));
				vec![(i, ub), (-i, lb)]
			}
			_ => Vec::new(),
		}
	}

	pub fn int_reverse_map_info(&self) -> (Option<usize>, bool) {
		match self.0 {
			IntViewInner::VarRef(v) => (Some(v.into()), false),
			IntViewInner::Bool { .. } => (None, true),
			IntViewInner::Linear { var, .. } => (Some(var.into()), true),
			_ => (None, true),
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
