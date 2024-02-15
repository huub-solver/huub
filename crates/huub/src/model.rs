mod bool;
mod flatzinc;
mod int;
mod reformulate;

use std::ops::AddAssign;

use flatzinc_serde::RangeList;
use pindakaas::{ClauseDatabase, Cnf, Var as RawVar};

pub use self::{
	bool::{BoolExpr, BoolVar, Literal},
	int::{IntExpr, IntVar},
	reformulate::{ReifContext, SimplifiedBool, SimplifiedInt, SimplifiedVariable, VariableMap},
};
use crate::{
	model::int::IntVarDef,
	propagator::all_different::AllDifferentValue,
	solver::{engine::int_var::IntVar as SlvIntVar, BoolView},
	Solver,
};

#[derive(Debug, Default)]
pub struct Model {
	pub(crate) cnf: Cnf,
	constraints: Vec<Constraint>,
	int_vars: Vec<IntVarDef>,
}

impl Model {
	pub fn new_bool_var(&mut self) -> BoolVar {
		BoolVar(self.cnf.new_var())
	}

	pub fn new_int_var(&mut self, domain: RangeList<i64>) -> IntVar {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars.push(IntVarDef { domain });
		iv
	}

	// TODO: Make generic on Solver again (need var range trait)
	pub fn to_solver(&self) -> (Solver, VariableMap) {
		let mut map = VariableMap::default();

		// TODO: run SAT simplification
		let mut slv = self.cnf.clone().into();

		// TODO: Find Views
		// TODO: Analyse/Choose Integer encodings

		// Create integer data structures within the solver
		for i in 0..self.int_vars.len() {
			let var = &self.int_vars[i];
			let view = SlvIntVar::new_in(&mut slv, var.domain.clone());
			map.insert(
				Variable::Int(IntVar(i as u32)),
				SimplifiedVariable::Int(SimplifiedInt::Var(view)),
			);
		}

		// Create constraint data structures within the solve
		for c in self.constraints.iter() {
			c.to_solver(&mut slv, &mut map)
		}

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

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
	Clause(Vec<BoolExpr>),
	AllDifferent(Vec<IntExpr>),
}

impl Constraint {
	fn to_solver(&self, slv: &mut Solver, map: &mut VariableMap) {
		struct Satisfied;
		match self {
			Constraint::Clause(v) => {
				let lits: Result<Vec<BoolView>, Satisfied> = v
					.iter()
					.filter_map(|x| match x.to_arg(ReifContext::Pos, slv, map) {
						SimplifiedBool::Lit(l) => Some(Ok(l)),
						SimplifiedBool::Val(true) => Some(Err(Satisfied)),
						SimplifiedBool::Val(false) => None,
					})
					.collect();
				if let Ok(lits) = lits {
					// TODO: early unsat detection?
					let _ = slv.core.add_clause(lits.into_iter().map(|l| l.0));
				}
			}
			Constraint::AllDifferent(v) => {
				let (vars, vals): (Vec<_>, _) = v
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.partition(|x| matches!(x, SimplifiedInt::Var(_)));
				if !vals.is_empty() {
					todo!()
				}
				slv.add_propagator(Box::new(AllDifferentValue::new(vars.into_iter().map(
					|v| {
						let SimplifiedInt::Var(v) = v else {
							unreachable!()
						};
						v
					},
				))))
			}
		}
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Variable {
	Bool(BoolVar),
	Int(IntVar),
}
impl From<BoolVar> for Variable {
	fn from(value: BoolVar) -> Self {
		Self::Bool(value)
	}
}
