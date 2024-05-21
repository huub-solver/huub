use std::{collections::HashMap, ops::Not};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation, Var as RawVar,
};
use thiserror::Error;

use super::{bool, int, int::IntVar, ModelView};
use crate::{
	propagator::ExplainActions,
	solver::{
		view::{BoolView, BoolViewInner, IntViewInner, SolverView},
		SatSolver,
	},
	IntVal, IntView, LitMeaning, Solver,
};

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: HashMap<Variable, SolverView>,
}

impl VariableMap {
	pub fn get<Sat, Sol>(&self, slv: &Solver<Sat>, index: &ModelView) -> SolverView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match index {
			ModelView::Bool(b) => SolverView::Bool(self.get_bool(slv, b)),
			ModelView::Int(i) => SolverView::Int(self.get_int(slv, i)),
		}
	}

	pub fn get_bool<Sat, Sol>(&self, slv: &Solver<Sat>, bv: &bool::BoolView) -> BoolView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let get_int_lit = |slv: &Solver<Sat>, iv: &int::IntView, lit_meaning: LitMeaning| {
			let iv = self.get_int(slv, iv);
			slv.engine().state.get_int_lit(iv, lit_meaning)
		};

		match bv {
			bool::BoolView::Lit(l) => {
				let SolverView::Bool(bv) = self
					.map
					.get(&Variable::Bool(l.var()))
					.cloned()
					.unwrap_or_else(|| {
						SolverView::Bool(BoolView(BoolViewInner::Lit(l.var().into())))
					})
				else {
					unreachable!()
				};
				if l.is_negated() {
					!bv
				} else {
					bv
				}
			}
			bool::BoolView::Const(c) => (*c).into(),
			bool::BoolView::IntEq(v, i) => get_int_lit(slv, v, LitMeaning::Eq(*i)),
			bool::BoolView::IntGreater(v, i) => get_int_lit(slv, v, LitMeaning::GreaterEq(i + 1)),
			bool::BoolView::IntGreaterEq(v, i) => get_int_lit(slv, v, LitMeaning::GreaterEq(*i)),
			bool::BoolView::IntLess(v, i) => get_int_lit(slv, v, LitMeaning::Less(*i)),
			bool::BoolView::IntLessEq(v, i) => get_int_lit(slv, v, LitMeaning::Less(i - 1)),
			bool::BoolView::IntNotEq(v, i) => get_int_lit(slv, v, LitMeaning::NotEq(*i)),
		}
	}

	pub fn get_int<Sat, Sol>(&self, slv: &Solver<Sat>, iv: &int::IntView) -> IntView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let get_int_var = |v: &IntVar| {
			let SolverView::Int(i) = self.map.get(&Variable::Int(*v)).cloned().unwrap() else {
				unreachable!()
			};
			i
		};

		match iv {
			int::IntView::Var(i) => get_int_var(i),
			int::IntView::Const(c) => (*c).into(),
			int::IntView::Linear(t, i) => get_int_var(i) * t.scale + t.offset,
			int::IntView::Bool(t, bv) => {
				let bv = self.get_bool(slv, bv);
				match bv.0 {
					BoolViewInner::Lit(lit) => IntView(IntViewInner::Bool {
						transformer: *t,
						lit,
					}),
					BoolViewInner::Const(b) => t.transform(b as IntVal).into(),
				}
			}
		}
	}

	pub(crate) fn insert_int(&mut self, index: IntVar, elem: IntView) {
		let _ = self.map.insert(index.into(), elem.into());
	}

	#[allow(dead_code)] // TODO
	pub(crate) fn insert_bool(&mut self, index: RawVar, elem: BoolView) {
		let _ = self.map.insert(index.into(), elem.into());
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ReifContext {
	Pos,
	#[allow(dead_code)]
	Neg,
	#[allow(dead_code)]
	Mixed,
}

impl Not for ReifContext {
	type Output = Self;
	fn not(self) -> Self::Output {
		match self {
			ReifContext::Pos => ReifContext::Neg,
			ReifContext::Neg => ReifContext::Pos,
			ReifContext::Mixed => ReifContext::Mixed,
		}
	}
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum ReformulationError {
	#[error("The expression is trivially unsatisfiable")]
	TrivialUnsatisfiable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Variable {
	Bool(RawVar),
	Int(IntVar),
}
impl From<RawVar> for Variable {
	fn from(value: RawVar) -> Self {
		Self::Bool(value)
	}
}
impl From<IntVar> for Variable {
	fn from(value: IntVar) -> Self {
		Self::Int(value)
	}
}
