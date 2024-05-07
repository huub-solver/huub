pub(crate) mod bool;
pub(crate) mod flatzinc;
pub(crate) mod int;
pub(crate) mod reformulate;

use std::ops::AddAssign;

use flatzinc_serde::RangeList;
use itertools::Itertools;
use pindakaas::{
	solver::{NextVarRange, PropagatorAccess, Solver as SolverTrait},
	ClauseDatabase, Cnf, ConditionalDatabase, Lit as RawLit, Valuation as SatValuation,
	Var as RawVar,
};

use self::{
	bool::{BoolExpr, BoolVar},
	int::{IntExpr, IntVar},
	reformulate::{ReformulationError, VariableMap},
};
use crate::{
	model::{int::IntVarDef, reformulate::ReifContext},
	propagator::{all_different::AllDifferentValue, int_lin_le::LinearLE},
	solver::{engine::int_var::IntVar as SlvIntVar, view::SolverView, SatSolver},
	IntVal, Solver,
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

	pub fn new_bool_var_range(&mut self, len: usize) -> Vec<BoolVar> {
		self.cnf.next_var_range(len).unwrap().map(BoolVar).collect()
	}

	pub fn new_int_var(&mut self, domain: RangeList<i64>) -> IntVar {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars.push(IntVarDef { domain });
		iv
	}

	pub fn to_solver<
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	>(
		&self,
	) -> Result<(Solver<Sat>, VariableMap), ReformulationError> {
		let mut map = VariableMap::default();

		// TODO: run SAT simplification
		let mut slv = self.cnf.clone().into();

		// TODO: Find Views
		// TODO: Analyse/Choose Integer encodings

		// Create integer data structures within the solver
		for i in 0..self.int_vars.len() {
			let var = &self.int_vars[i];
			let view = SlvIntVar::new_in(&mut slv, var.domain.clone(), true); // TODO!
			map.insert(Variable::Int(IntVar(i as u32)), SolverView::Int(view));
		}

		// Create constraint data structures within the solve
		for c in self.constraints.iter() {
			c.to_solver(&mut slv, &mut map)?;
		}

		Ok((slv, map))
	}
}

impl AddAssign<Constraint> for Model {
	fn add_assign(&mut self, rhs: Constraint) {
		self.constraints.push(rhs)
	}
}
impl AddAssign<BoolExpr> for Model {
	fn add_assign(&mut self, rhs: BoolExpr) {
		self.constraints.push(Constraint::SimpleBool(rhs))
	}
}

impl ClauseDatabase for Model {
	fn new_var(&mut self) -> RawVar {
		self.cnf.new_var()
	}

	fn add_clause<I: IntoIterator<Item = RawLit>>(&mut self, cl: I) -> pindakaas::Result {
		self.cnf.add_clause(cl)
	}

	type CondDB = Model;
	fn with_conditions(&mut self, conditions: Vec<RawLit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase::new(self, conditions)
	}
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
	SimpleBool(BoolExpr),
	AllDifferent(Vec<IntExpr>),
	IntLinLessEq(Vec<IntVal>, Vec<IntExpr>, IntVal),
	IntLinEq(Vec<IntVal>, Vec<IntExpr>, IntVal),
}

impl Constraint {
	fn to_solver<Sol, Sat>(
		&self,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> Result<(), ReformulationError>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match self {
			Constraint::SimpleBool(exp) => exp.constrain(slv, map),
			Constraint::AllDifferent(v) => {
				let vars: Vec<_> = v
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				slv.add_propagator(AllDifferentValue::new(vars));
				Ok(())
			}
			Constraint::IntLinLessEq(coeffs, vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.zip_eq(coeffs.iter())
					.map(|(v, &c)| {
						v.to_arg(
							if c >= 0 {
								ReifContext::Pos
							} else {
								ReifContext::Neg
							},
							slv,
							map,
						)
					})
					.collect();
				slv.add_propagator(LinearLE::new(coeffs, vars, *c));
				Ok(())
			}
			Constraint::IntLinEq(coeffs, vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				// coeffs * vars <= c
				slv.add_propagator(LinearLE::new(coeffs, vars.clone(), *c));
				// coeffs * vars >= c <=>  -coeffs * vars <= -c
				slv.add_propagator(LinearLE::new(
					&coeffs.iter().map(|c| -c).collect_vec(),
					vars,
					-c,
				));
				Ok(())
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
