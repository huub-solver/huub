use std::{
	fmt::{self, Display},
	num::NonZeroI32,
	ops::Not,
};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Formula, Lit as RawLit, TseitinEncoder, Valuation as SatValuation, Var as RawVar,
};

use super::reformulate::{ReformulationError, ReifContext, VariableMap};
use crate::{
	solver::{
		view::{BoolView, BoolViewInner},
		SatSolver,
	},
	Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolExpr {
	Val(bool),
	Lit(Literal),
	Not(Box<BoolExpr>),
	Or(Vec<BoolExpr>),
	And(Vec<BoolExpr>),
	Implies(Box<BoolExpr>, Box<BoolExpr>),
	Equiv(Vec<BoolExpr>),
	Xor(Vec<BoolExpr>),
	IfThenElse {
		cond: Box<BoolExpr>,
		then: Box<BoolExpr>,
		els: Box<BoolExpr>,
	},
}

impl BoolExpr {
	pub(crate) fn constrain<Sol, Sat>(
		&self,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> Result<(), ReformulationError>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match self {
			BoolExpr::Val(false) => Err(ReformulationError::TrivialUnsatisfiable),
			BoolExpr::Val(true) => Ok(()),
			BoolExpr::Lit(l) => {
				let v = map.get_lit(l);
				match v.0 {
					BoolViewInner::Const(true) => Ok(()),
					BoolViewInner::Const(false) => Err(ReformulationError::TrivialUnsatisfiable),
					BoolViewInner::Lit(l) => slv
						.oracle
						.add_clause([l])
						.map_err(|_| ReformulationError::TrivialUnsatisfiable),
				}
			}
			BoolExpr::Not(x) => (!*x.clone()).constrain(slv, map),
			BoolExpr::Or(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(ReifContext::Pos, slv, map, None)?.0 {
						BoolViewInner::Const(false) => {}
						BoolViewInner::Const(true) => return Ok(()),
						BoolViewInner::Lit(l) => lits.push(l),
					}
				}
				slv.oracle
					.add_clause(lits)
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)
			}
			BoolExpr::And(es) => {
				for e in es {
					match e.to_arg(ReifContext::Pos, slv, map, None)?.0 {
						BoolViewInner::Const(false) => {
							return Err(ReformulationError::TrivialUnsatisfiable)
						}
						BoolViewInner::Const(true) => {}
						BoolViewInner::Lit(l) => slv
							.oracle
							.add_clause([l])
							.map_err(|_| ReformulationError::TrivialUnsatisfiable)?,
					}
				}
				Ok(())
			}
			BoolExpr::Implies(a, b) => {
				let a = match a.to_arg(ReifContext::Neg, slv, map, None)?.0 {
					BoolViewInner::Const(true) => {
						return b.constrain(slv, map);
					}
					BoolViewInner::Const(false) => {
						return Ok(());
					}
					BoolViewInner::Lit(l) => l,
				};

				// TODO: Conditional Compilation
				match b.to_arg(ReifContext::Pos, slv, map, None)?.0 {
					BoolViewInner::Const(true) => Ok(()),
					BoolViewInner::Const(false) => slv
						.oracle
						.add_clause([!a])
						.map_err(|_| ReformulationError::TrivialUnsatisfiable),
					BoolViewInner::Lit(b) => slv
						.oracle
						.add_clause([!a, b])
						.map_err(|_| ReformulationError::TrivialUnsatisfiable),
				}
			}
			BoolExpr::Equiv(es) => {
				// Try and find some constant or literal to start binding to
				let mut res = es
					.iter()
					.find_map(|e| {
						if let BoolExpr::Val(b) = e {
							Some(BoolView(BoolViewInner::Const(*b)))
						} else {
							None
						}
					})
					.or_else(|| {
						es.iter().find_map(|e| {
							if let BoolExpr::Lit(l) = e {
								Some(map.get_lit(l))
							} else {
								None
							}
						})
					});
				for e in es {
					match res {
						Some(BoolView(BoolViewInner::Const(false))) => {
							(!e).constrain(slv, map)?;
						}
						Some(BoolView(BoolViewInner::Const(true))) => {
							e.constrain(slv, map)?;
						}
						Some(BoolView(BoolViewInner::Lit(name))) => {
							res = Some(e.to_arg(ReifContext::Mixed, slv, map, Some(name))?);
						}
						None => res = Some(e.to_arg(ReifContext::Mixed, slv, map, None)?),
					}
				}
				Ok(())
			}
			BoolExpr::Xor(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut count = 0;
				for e in es {
					match e.to_arg(ReifContext::Mixed, slv, map, None)?.0 {
						BoolViewInner::Const(true) => count += 1,
						BoolViewInner::Const(false) => {}
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let mut formula = Formula::Xor(lits);
				if count % 2 == 1 {
					formula = !formula;
				}
				slv.oracle
					.encode(&formula, &TseitinEncoder)
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)
			}
			BoolExpr::IfThenElse { cond, then, els } => {
				match cond.to_arg(ReifContext::Mixed, slv, map, None)?.0 {
					BoolViewInner::Const(true) => then.constrain(slv, map),
					BoolViewInner::Const(false) => els.constrain(slv, map),
					BoolViewInner::Lit(_) => BoolExpr::And(vec![
						BoolExpr::Or(vec![!*cond.clone(), *then.clone()]),
						BoolExpr::Or(vec![*cond.clone(), *els.clone()]),
					])
					.constrain(slv, map),
				}
			}
		}
	}

	pub(crate) fn to_arg<Sol, Sat>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
		name: Option<RawLit>,
	) -> Result<BoolView, ReformulationError>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let bind_lit = |oracle: &mut Sat, lit| {
			Ok(BoolView(BoolViewInner::Lit(if let Some(name) = name {
				oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), Formula::Atom(lit)]),
						&TseitinEncoder,
					)
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)?;
				name
			} else {
				lit
			})))
		};
		let bind_const = |oracle: &mut Sat, val| {
			if let Some(name) = name {
				oracle
					.add_clause([if val { name } else { !name }])
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)?;
			}
			Ok(BoolView(BoolViewInner::Const(val)))
		};
		match self {
			BoolExpr::Not(b) => b.to_negated_arg(ctx, slv, map, name),
			BoolExpr::Lit(l) => bind_lit(&mut slv.oracle, l.0),
			BoolExpr::Val(v) => bind_const(&mut slv.oracle, *v),
			BoolExpr::Or(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(ReifContext::Pos, slv, map, None)?.0 {
						BoolViewInner::Const(false) => {}
						BoolViewInner::Const(true) => return bind_const(&mut slv.oracle, true),
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let r = name.unwrap_or_else(|| slv.oracle.new_var().into());
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(r), Formula::Or(lits)]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(BoolView(BoolViewInner::Lit(r)))
			}
			BoolExpr::And(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(ReifContext::Pos, slv, map, None)?.0 {
						BoolViewInner::Const(true) => {}
						BoolViewInner::Const(false) => return bind_const(&mut slv.oracle, false),
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_var().into());
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), Formula::And(lits)]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::Implies(a, b) => {
				let a = match a.to_arg(ReifContext::Neg, slv, map, None)?.0 {
					BoolViewInner::Const(true) => return b.to_arg(ctx, slv, map, name),
					BoolViewInner::Const(false) => return bind_const(&mut slv.oracle, true),
					BoolViewInner::Lit(l) => l,
				};

				// TODO: Conditional encoding
				match b.to_arg(ctx, slv, map, None)?.0 {
					BoolViewInner::Const(true) => bind_const(&mut slv.oracle, true),
					BoolViewInner::Const(false) => bind_lit(&mut slv.oracle, !a),
					BoolViewInner::Lit(b) => {
						let name = name.unwrap_or_else(|| slv.oracle.new_var().into());
						slv.oracle
							.encode(
								&Formula::Equiv(vec![
									Formula::Atom(name),
									Formula::Implies(
										Box::new(Formula::Atom(a)),
										Box::new(Formula::Atom(b)),
									),
								]),
								&TseitinEncoder,
							)
							.unwrap();
						Ok(BoolView(BoolViewInner::Lit(name)))
					}
				}
			}
			BoolExpr::Equiv(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut res = None;
				for e in es {
					match e.to_arg(ReifContext::Mixed, slv, map, None)?.0 {
						BoolViewInner::Const(b) => match res {
							None => res = Some(b),
							Some(b2) if b != b2 => {
								return bind_const(&mut slv.oracle, false);
							}
							Some(_) => {}
						},
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_var().into());
				let f = match res {
					Some(b) => {
						Formula::And(lits.into_iter().map(|e| if b { e } else { !e }).collect())
					}
					None => Formula::Equiv(lits),
				};
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), f]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::Xor(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut count = 0;
				for e in es {
					match e.to_arg(ReifContext::Mixed, slv, map, None)?.0 {
						BoolViewInner::Const(true) => count += 1,
						BoolViewInner::Const(false) => {}
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_var().into());
				let mut formula = Formula::Xor(lits);
				if count % 2 == 1 {
					formula = !formula;
				}
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), formula]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::IfThenElse { cond, then, els } => {
				match cond.to_arg(ReifContext::Mixed, slv, map, None)?.0 {
					BoolViewInner::Const(true) => then.to_arg(ctx, slv, map, name),
					BoolViewInner::Const(false) => then.to_arg(ctx, slv, map, name),
					// TODO: Conditional encoding
					BoolViewInner::Lit(_) => BoolExpr::And(vec![
						BoolExpr::Or(vec![!*cond.clone(), *then.clone()]),
						BoolExpr::Or(vec![*cond.clone(), *els.clone()]),
					])
					.to_arg(ctx, slv, map, name),
				}
			}
		}
	}

	fn to_negated_arg<Sol, Sat>(
		&self,
		ctx: ReifContext,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
		name: Option<RawLit>,
	) -> Result<BoolView, ReformulationError>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match self {
			BoolExpr::Not(v) => v.to_arg(!ctx, slv, map, name),
			BoolExpr::Lit(v) => Ok(BoolView(BoolViewInner::Lit((!v).0))),
			BoolExpr::Val(v) => Ok(BoolView(BoolViewInner::Const(!v))),
			BoolExpr::Or(_)
			| BoolExpr::And(_)
			| BoolExpr::Implies(_, _)
			| BoolExpr::IfThenElse {
				cond: _,
				then: _,
				els: _,
			} => (!self).to_arg(ctx, slv, map, name),
			_ => {
				let r = self.to_arg(ReifContext::Mixed, slv, map, name)?;
				Ok(!r)
			}
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
			BoolExpr::Or(es) => BoolExpr::And(es.into_iter().map(|e| !e).collect()),
			BoolExpr::And(es) => BoolExpr::Or(es.into_iter().map(|e| !e).collect()),
			BoolExpr::Implies(a, b) => BoolExpr::And(vec![*a, !*b]),
			BoolExpr::IfThenElse { cond, then, els } => BoolExpr::IfThenElse {
				cond,
				then: Box::new(!*then),
				els: Box::new(!*els),
			},
			_ => BoolExpr::Not(Box::new(self)),
		}
	}
}

impl Not for &BoolExpr {
	type Output = BoolExpr;
	fn not(self) -> Self::Output {
		!self.clone()
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

#[cfg(test)]
mod tests {
	use itertools::Itertools;

	use crate::{BoolExpr, Model, SolveResult, Solver, Value};

	#[test]
	fn test_bool_and() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_var_range(3);

		m += BoolExpr::And(b.iter().copied().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver().unwrap();
		assert_eq!(
			slv.solve(|sol| {
				for &l in &b {
					assert_eq!(sol(map.get(&l.into())), Some(Value::Bool(true)));
				}
			}),
			SolveResult::Satisfied
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_var_range(3);

		m += BoolExpr::And(b.iter().copied().map_into().collect());
		m += BoolExpr::from(!b[0]);
		let (mut slv, _): (Solver, _) = m.to_solver().unwrap();
		assert_eq!(
			slv.solve(|_| { unreachable!("expected unsatisfiable") }),
			SolveResult::Unsatisfiable
		);
	}

	#[test]
	fn test_bool_or() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_var_range(3);

		m += BoolExpr::Or(b.iter().copied().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver().unwrap();
		assert_eq!(
			slv.solve(|sol| {
				assert!(b
					.iter()
					.any(|&l| sol(map.get(&l.into())) == Some(Value::Bool(true))));
			}),
			SolveResult::Satisfied
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_var_range(3);

		m += BoolExpr::Or(b.iter().copied().map_into().collect());
		m += BoolExpr::And(b.iter().copied().map(|l| (!l).into()).collect());
		let (mut slv, _): (Solver, _) = m.to_solver().unwrap();
		assert_eq!(
			slv.solve(|_| { unreachable!("expected unsatisfiable") }),
			SolveResult::Unsatisfiable
		);
	}
}
