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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntView(pub(crate) IntViewInner);

impl IntView {
	pub fn add_to_lit_reverse_map<Sol, Sat, M>(&self, slv: &Solver<Sat>, map: &mut M)
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
		M: Extend<(NonZeroI32, (usize, LitMeaning))>,
	{
		match self.0 {
			IntViewInner::VarRef(v) => {
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
			IntViewInner::Const(_) => {}
			IntViewInner::Linear { var, .. } => {
				IntView(IntViewInner::VarRef(var)).add_to_lit_reverse_map(slv, map);
			}
		}
	}

	pub fn add_to_int_reverse_map<E>(&self, map: &mut [E], name: E) {
		match self.0 {
			IntViewInner::VarRef(v) => {
				let pos: usize = v.into();
				map[pos] = name;
			}
			IntViewInner::Const(_) => {}
			IntViewInner::Linear { var, .. } => {
				let pos: usize = var.into();
				map[pos] = name;
			}
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
}

impl Neg for IntView {
	type Output = Self;
	fn neg(self) -> Self::Output {
		match self.0 {
			IntViewInner::VarRef(var) => IntView(IntViewInner::Linear {
				transformer: LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()),
				var,
			}),
			IntViewInner::Const(i) => IntView(IntViewInner::Const(-i)),
			IntViewInner::Linear {
				transformer: transform,
				var,
			} => IntView(IntViewInner::Linear {
				transformer: -transform,
				var,
			}),
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
		})
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LinearTransform {
	scale: NonZeroIntVal,
	offset: IntVal,
}

impl LinearTransform {
	/// Creates a new linear transformation with the given scale and offset.
	#[allow(dead_code)] // TODO!
	pub(crate) fn new(scale: NonZeroIntVal, offset: IntVal) -> Self {
		Self { scale, offset }
	}
	/// Creates a new linear transformation with the given scale and no offset.
	pub(crate) fn scaled(scale: NonZeroIntVal) -> Self {
		Self { scale, offset: 0 }
	}
	/// Creates a new linear transformation with the given offset and no scale.
	pub(crate) fn offset(offset: IntVal) -> Self {
		Self {
			scale: NonZeroIntVal::new(1).unwrap(),
			offset,
		}
	}

	pub(crate) fn positive_scale(&self) -> bool {
		self.scale.get() > 0
	}

	/// Perform the linear transformation on a value.
	pub(crate) fn transform(&self, val: IntVal) -> IntVal {
		(val * self.scale.get()) + self.offset
	}

	/// Perform the reverse linear transformation on a value.
	pub(crate) fn rev_transform(&self, val: IntVal) -> IntVal {
		(val - self.offset) / self.scale.get()
	}

	/// Returns whether a value remains an integer after reversing the transformation.
	pub(crate) fn rev_remains_integer(&self, val: IntVal) -> bool {
		(val - self.offset) % self.scale.get() == 0
	}

	/// Perform the reverse linear tranformation for a LitMeanning request.
	///
	/// Note that this performs the correct rounding to maintain the meaning of the literal. When
	/// equality literals are requested, None is returned when no such integer value exists.
	pub(crate) fn rev_transform_lit(&self, mut lit: LitMeaning) -> Option<LitMeaning> {
		let mut transformer = *self;
		if !self.positive_scale() {
			// Make positive by doing `*-1` on lit meaning and transformer
			(lit, transformer) = match lit {
				// -x >= i === x <= -i === x < -i + 1
				LitMeaning::GreaterEq(i) => (LitMeaning::Less(-i + 1), -transformer),
				// -x < i === x > -i === x >= -i + 1
				LitMeaning::Less(i) => (LitMeaning::GreaterEq(-i + 1), -transformer),
				_ => (lit, transformer),
			};
		}

		match lit {
			LitMeaning::Eq(i) => {
				if transformer.rev_remains_integer(i) {
					Some(LitMeaning::Eq(transformer.rev_transform(i)))
				} else {
					None
				}
			}
			LitMeaning::NotEq(i) => {
				if transformer.rev_remains_integer(i) {
					Some(LitMeaning::NotEq(transformer.rev_transform(i)))
				} else {
					None
				}
			}
			LitMeaning::GreaterEq(i) => Some(LitMeaning::GreaterEq(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
			LitMeaning::Less(i) => Some(LitMeaning::Less(div_ceil(
				i - transformer.offset,
				transformer.scale,
			))),
		}
	}
}

#[inline]
fn div_ceil(a: IntVal, b: NonZeroIntVal) -> IntVal {
	a / b.get() + (0 != a % b.get()) as IntVal
}

impl Neg for LinearTransform {
	type Output = Self;
	fn neg(self) -> Self::Output {
		Self {
			scale: NonZeroIntVal::new(-self.scale.get()).unwrap(),
			offset: -self.offset,
		}
	}
}

impl Add<IntVal> for LinearTransform {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		LinearTransform {
			scale: self.scale,
			offset: self.offset + rhs,
		}
	}
}

impl Mul<NonZeroIntVal> for LinearTransform {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		LinearTransform {
			scale: NonZeroIntVal::new(self.scale.get() * rhs.get()).unwrap(),
			offset: self.offset * rhs.get(),
		}
	}
}
