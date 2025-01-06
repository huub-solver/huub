//! The view module contains the types that are used to reference values in the
//! solver that can be expected as part of a solution, and are used internally
//! in branchers and propagators.

use std::{
	num::NonZeroI32,
	ops::{Add, Mul, Neg, Not},
};

use pindakaas::{solver::propagation::PropagatingSolver, BoolVal, Lit as RawLit, Var as RawVar};

use crate::{
	helpers::linear_transform::LinearTransform,
	solver::{
		engine::Engine,
		int_var::{DirectStorage, IntVarRef, LitMeaning, OrderStorage},
		value::NonZeroIntVal,
	},
	IntVal, Solver,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to a Boolean type value in the solver that can be expected as
/// part of a solution.
pub struct BoolView(pub(crate) BoolViewInner);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(variant_size_differences, reason = "`Lit` cannot be as smal as `bool`")]
/// The internal representation of a [`BoolView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub(crate) enum BoolViewInner {
	/// A Boolean literal in the solver.
	Lit(RawLit),
	/// A constant boolean value.
	Const(bool),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to a integer type value in the solver that can be expected as
/// part of a solution.
pub struct IntView(pub(crate) IntViewInner);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// The internal representation of [`IntView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub(crate) enum IntViewInner {
	/// (Raw) Integer Variable
	/// Reference to location in the Engine's State
	VarRef(IntVarRef),
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear {
		/// Linear transformation on the integer value of the variable.
		transformer: LinearTransform,
		/// Reference to an integer variable.
		var: IntVarRef,
	},
	/// Linear View of an Boolean Literal.
	Bool {
		/// Linear transformation on the integer value of the Boolean literal.
		transformer: LinearTransform,
		/// The Boolean literal that is being treated as an integer (`false` -> `0`
		/// and `true` -> `1`).
		lit: RawLit,
	},
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to a value in the solver that can be expected as part of a
/// solution.
pub enum SolverView {
	/// A Boolean type value.
	Bool(BoolView),
	/// An integer type value.
	Int(IntView),
}

impl BoolView {
	/// Return an integers that can used to identify the literal, if there is one.
	pub fn reverse_map_info(&self) -> Option<NonZeroI32> {
		match self.0 {
			BoolViewInner::Lit(v) => Some(v.into()),
			BoolViewInner::Const(_) => None,
		}
	}
}

impl From<bool> for BoolView {
	fn from(value: bool) -> Self {
		BoolView(BoolViewInner::Const(value))
	}
}

impl From<RawLit> for BoolView {
	fn from(value: RawLit) -> Self {
		BoolView(BoolViewInner::Lit(value))
	}
}

impl From<RawVar> for BoolView {
	fn from(value: RawVar) -> Self {
		BoolView(BoolViewInner::Lit(value.into()))
	}
}

impl Into<BoolVal> for BoolView {
	fn into(self) -> BoolVal {
		match self.0 {
			BoolViewInner::Lit(l) => l.into(),
			BoolViewInner::Const(b) => b.into(),
		}
	}
}

impl Not for BoolView {
	type Output = Self;

	fn not(self) -> Self::Output {
		match self.0 {
			BoolViewInner::Lit(l) => (!l).into(),
			BoolViewInner::Const(b) => BoolView(BoolViewInner::Const(!b)),
		}
	}
}
impl Not for &BoolView {
	type Output = BoolView;

	fn not(self) -> Self::Output {
		match self.0 {
			BoolViewInner::Lit(l) => (!l).into(),
			BoolViewInner::Const(b) => BoolView(BoolViewInner::Const(!b)),
		}
	}
}

impl IntView {
	/// Returns an integer that can be used to identify the associated integer
	/// decision variable and whether the int view is a view on another decision
	/// variable.
	pub fn int_reverse_map_info(&self) -> (Option<usize>, bool) {
		match self.0 {
			IntViewInner::VarRef(v) => (Some(v.into()), false),
			IntViewInner::Bool { .. } => (None, true),
			IntViewInner::Linear { var, .. } => (Some(var.into()), true),
			_ => (None, true),
		}
	}
	/// Return a list of integers that can used to identify the literals that are
	/// associated to an integer view, and the meaning of those literals.
	pub fn lit_reverse_map_info<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &Solver<Oracle>,
	) -> Vec<(NonZeroI32, LitMeaning)> {
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
						let orig = LitMeaning::Less(val);
						let lt = transformer.transform_lit(orig);
						let geq = !lt.clone();
						lits.extend([(i, lt), (-i, geq)]);
					}
				}

				if let DirectStorage::Eager(vars) = &var.direct_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					let _ = val_iter.next();
					let _ = val_iter.next_back();
					for (lit, val) in vars.clone().zip(val_iter) {
						let i: NonZeroI32 = lit.into();
						let orig = LitMeaning::Eq(val);
						let eq = transformer.transform_lit(orig);
						let ne = !eq.clone();
						lits.extend([(i, eq), (-i, ne)]);
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

impl From<IntVal> for IntView {
	fn from(value: IntVal) -> Self {
		Self(IntViewInner::Const(value))
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

impl From<BoolView> for SolverView {
	fn from(value: BoolView) -> Self {
		Self::Bool(value)
	}
}

impl From<IntView> for SolverView {
	fn from(value: IntView) -> Self {
		Self::Int(value)
	}
}
