mod flatzinc;
mod reformulate;

use std::{
	fmt::{self, Display},
	num::NonZeroI32,
	ops::{AddAssign, Not},
};

use pindakaas::{ClauseDatabase, Cnf, Lit as RawLit, Var as RawVar};
pub use reformulate::{ReifContext, SimplifiedBool, SimplifiedVariable, VariableMap};

use crate::{
	solver::{PropagationLayer, SatSolver},
	Solver,
};

#[derive(Debug, Default)]
pub struct Model {
	pub(crate) cnf: Cnf,
	constraints: Vec<Constraint>,
}

impl Model {
	pub fn new_bool_var(&mut self) -> BoolVar {
		BoolVar(self.cnf.new_var())
	}

	pub fn to_solver<S: SatSolver + From<Cnf>>(&self) -> (Solver<S>, VariableMap) {
		let mut map = VariableMap::default();

		// TODO: run SAT simplification

		let mut slv: Solver<S> = Solver {
			engine: self.cnf.clone().into(),
		};
		let prop_layer = PropagationLayer::default();

		for c in self.constraints.iter() {
			c.to_solver(&mut slv, &mut map)
		}

		slv.engine
			.set_external_propagator(Some(Box::new(prop_layer)));
		(slv, map)
	}
}

impl AddAssign<Constraint> for Model {
	fn add_assign(&mut self, rhs: Constraint) {
		self.constraints.push(rhs)
	}
}

impl ClauseDatabase for Model {
	fn new_var(&mut self) -> RawVar {
		self.cnf.new_var()
	}

	fn add_clause<I: IntoIterator<Item = pindakaas::Lit>>(&mut self, cl: I) -> pindakaas::Result {
		self.cnf.add_clause(cl)
	}
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
	Clause(Vec<BoolExpr>),
}

impl Constraint {
	fn to_solver<S: SatSolver>(&self, slv: &mut Solver<S>, map: &mut VariableMap) {
		struct Satisfied;
		match self {
			Constraint::Clause(v) => {
				let lits: Result<Vec<Literal>, Satisfied> = v
					.iter()
					.filter_map(|x| match x.to_arg(ReifContext::Pos, slv, map) {
						SimplifiedBool::Lit(l) => Some(Ok(l)),
						SimplifiedBool::Val(true) => Some(Err(Satisfied)),
						SimplifiedBool::Val(false) => None,
					})
					.collect();
				if let Ok(lits) = lits {
					// TOOD: early unsat detection?
					let _ = slv.engine.add_clause(lits.into_iter().map(|l| l.0));
				}
			}
		}
	}
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BoolExpr {
	Not(Box<BoolExpr>),
	Lit(Literal),
	Val(bool),
}

impl BoolExpr {
	fn to_arg<S: SatSolver>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<S>,
		map: &mut VariableMap,
	) -> SimplifiedBool {
		match self {
			BoolExpr::Not(b) => b.to_negated_arg(ctx, slv, map),
			BoolExpr::Lit(l) => SimplifiedBool::Lit(*l),
			BoolExpr::Val(v) => SimplifiedBool::Val(*v),
		}
	}

	fn to_negated_arg<S: SatSolver>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<S>,
		map: &mut VariableMap,
	) -> SimplifiedBool {
		match self {
			BoolExpr::Not(v) => v.to_arg(ctx, slv, map),
			BoolExpr::Lit(v) => SimplifiedBool::Lit(!v),
			BoolExpr::Val(v) => SimplifiedBool::Val(!v),
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
