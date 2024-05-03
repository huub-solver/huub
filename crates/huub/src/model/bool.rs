use std::{
	fmt::{self, Display},
	num::NonZeroI32,
	ops::Not,
};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Lit as RawLit, Valuation as SatValuation, Var as RawVar,
};

use super::reformulate::{ReifContext, VariableMap};
use crate::{
	solver::{
		view::{BoolView, BoolViewInner},
		SatSolver,
	},
	Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolExpr {
	Not(Box<BoolExpr>),
	Lit(Literal),
	Val(bool),
}

impl BoolExpr {
	pub(crate) fn to_arg<
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> BoolView {
		match self {
			BoolExpr::Not(b) => b.to_negated_arg(ctx, slv, map),
			BoolExpr::Lit(l) => BoolView(BoolViewInner::Lit(l.0)),
			BoolExpr::Val(v) => BoolView(BoolViewInner::Const(*v)),
		}
	}

	fn to_negated_arg<
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> BoolView {
		match self {
			BoolExpr::Not(v) => v.to_arg(ctx, slv, map),
			BoolExpr::Lit(v) => BoolView(BoolViewInner::Lit((!v).0)),
			BoolExpr::Val(v) => BoolView(BoolViewInner::Const(!v)),
		}
	}
}

impl Not for BoolExpr {
	type Output = BoolExpr;
	fn not(self) -> Self::Output {
		match self {
			BoolExpr::Lit(l) => BoolExpr::Lit(!l),
			BoolExpr::Val(v) => BoolExpr::Val(!v),
			BoolExpr::Not(e) => *e,
		}
	}
}

impl Not for &BoolExpr {
	type Output = BoolExpr;
	fn not(self) -> Self::Output {
		match self {
			BoolExpr::Lit(l) => BoolExpr::Lit(!*l),
			BoolExpr::Val(v) => BoolExpr::Val(!*v),
			BoolExpr::Not(e) => (**e).clone(),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoolVar(pub(crate) RawVar);

impl Not for BoolVar {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!Literal::from(self)
	}
}
impl Not for &BoolVar {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!*self
	}
}

impl Display for BoolVar {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}

impl From<BoolVar> for NonZeroI32 {
	fn from(val: BoolVar) -> Self {
		val.0.into()
	}
}
impl From<BoolVar> for i32 {
	fn from(val: BoolVar) -> Self {
		val.0.into()
	}
}
impl From<BoolVar> for BoolExpr {
	fn from(value: BoolVar) -> Self {
		BoolExpr::Lit(value.into())
	}
}

/// Literal is type that can be use to represent Boolean decision variables and
/// their negations
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal(pub(crate) RawLit);

impl Literal {
	pub fn var(&self) -> BoolVar {
		BoolVar(self.0.var())
	}
	pub fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
}

impl Not for Literal {
	type Output = Literal;
	fn not(self) -> Self::Output {
		Literal(!self.0)
	}
}
impl Not for &Literal {
	type Output = Literal;
	fn not(self) -> Self::Output {
		!(*self)
	}
}

impl From<BoolVar> for Literal {
	fn from(value: BoolVar) -> Self {
		Literal(value.0.into())
	}
}
impl From<Literal> for NonZeroI32 {
	fn from(val: Literal) -> Self {
		val.0.into()
	}
}
impl From<Literal> for i32 {
	fn from(val: Literal) -> Self {
		val.0.into()
	}
}
impl From<Literal> for BoolExpr {
	fn from(value: Literal) -> Self {
		BoolExpr::Lit(value)
	}
}

impl Display for Literal {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}
