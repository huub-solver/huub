pub(crate) mod bool;
pub(crate) mod constraint;
pub(crate) mod flatzinc;
pub(crate) mod int;
pub(crate) mod reformulate;

use std::{collections::VecDeque, iter::repeat, ops::AddAssign};

use flatzinc_serde::RangeList;
use pindakaas::{
	solver::{NextVarRange, PropagatorAccess, Solver as SolverTrait},
	ClauseDatabase, Cnf, ConditionalDatabase, Lit as RawLit, Valuation as SatValuation,
	Var as RawVar,
};

use self::{
	bool::{BoolExpr, BoolView},
	int::{IntVar, IntView},
	reformulate::{ReformulationError, VariableMap},
};
use crate::{
	model::int::IntVarDef,
	solver::{engine::int_var::IntVar as SlvIntVar, SatSolver},
	Constraint, Solver,
};

#[derive(Debug, Default)]
pub struct Model {
	pub(crate) cnf: Cnf,
	constraints: Vec<Constraint>,
	int_vars: Vec<IntVarDef>,
	prop_queue: VecDeque<usize>,
	enqueued: Vec<bool>,
}

impl Model {
	pub fn new_bool_var(&mut self) -> BoolView {
		BoolView::Lit(self.cnf.new_var().into())
	}

	pub fn new_bool_vars(&mut self, len: usize) -> Vec<BoolView> {
		self.cnf
			.next_var_range(len)
			.unwrap()
			.map(|v| BoolView::Lit(v.into()))
			.collect()
	}

	pub fn new_int_var(&mut self, domain: RangeList<i64>) -> IntView {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars.push(IntVarDef::with_domain(domain));
		IntView::Var(iv)
	}

	pub fn new_int_vars(&mut self, len: usize, domain: RangeList<i64>) -> Vec<IntVar> {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars
			.extend(repeat(IntVarDef::with_domain(domain)).take(len - 1));
		(0..len).map(|i| IntVar(iv.0 + i as u32)).collect()
	}

	pub fn to_solver<
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	>(
		&mut self,
	) -> Result<(Solver<Sat>, VariableMap), ReformulationError> {
		let mut map = VariableMap::default();

		// TODO: run SAT simplification
		let mut slv = self.cnf.clone().into();

		while let Some(con) = self.prop_queue.pop_front() {
			self.propagate(con)?;
			self.enqueued[con] = false;
		}

		// TODO: Find Views
		// TODO: Analyse/Choose Integer encodings

		// Create integer data structures within the solver
		for i in 0..self.int_vars.len() {
			let var = &self.int_vars[i];
			let view = SlvIntVar::new_in(&mut slv, var.domain.clone(), true); // TODO!
			map.insert_int(IntVar(i as u32), view);
		}

		// Create constraint data structures within the solve
		for c in self.constraints.iter() {
			c.to_solver(&mut slv, &mut map)?;
		}

		Ok((slv, map))
	}

	fn enqueue(&mut self, constraint: usize) {
		if !self.enqueued[constraint] {
			self.prop_queue.push_back(constraint);
			self.enqueued[constraint] = true;
		}
	}
}

impl AddAssign<Constraint> for Model {
	fn add_assign(&mut self, rhs: Constraint) {
		self.constraints.push(rhs);
		self.enqueued.push(false);
		self.enqueue(self.constraints.len() - 1);
		self.subscribe(self.constraints.len() - 1);
	}
}
impl AddAssign<BoolExpr> for Model {
	fn add_assign(&mut self, rhs: BoolExpr) {
		self.add_assign(Constraint::PropLogic(rhs))
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ModelView {
	Bool(BoolView),
	Int(IntView),
}
impl From<IntView> for ModelView {
	fn from(value: IntView) -> Self {
		Self::Int(value)
	}
}
impl From<BoolView> for ModelView {
	fn from(value: BoolView) -> Self {
		Self::Bool(value)
	}
}
