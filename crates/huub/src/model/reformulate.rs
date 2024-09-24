use std::collections::HashMap;

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation, Var as RawVar,
};
use thiserror::Error;

use crate::{
	actions::decision::DecisionActions,
	model::{
		bool,
		int::{self, IntVar},
		ModelView,
	},
	solver::{
		view::{BoolView, BoolViewInner, IntViewInner, SolverView},
		SatSolver,
	},
	IntVal, IntView, LitMeaning, Solver,
};

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct InitConfig {
	/// The maximum cardinality of the domain of an integer variable before its order encoding is created lazily.
	int_eager_limit: Option<usize>,
	/// Whether to enable restarts in the oracle solver.
	restart: bool,
	/// Whether to enable the vivification in the oracle solver.
	vivification: bool,
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

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: HashMap<Variable, SolverView>,
}

impl InitConfig {
	/// The default maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;

	/// Get the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn int_eager_limit(&self) -> usize {
		self.int_eager_limit
			.unwrap_or(Self::DEFAULT_INT_EAGER_LIMIT)
	}

	/// Get whether to enable restarts in the oracle solver.
	pub fn restart(&self) -> bool {
		self.restart
	}

	/// Get whether to enable the vivification in the oracle solver.
	pub fn vivification(&self) -> bool {
		self.vivification
	}

	/// Change the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn with_int_eager_limit(mut self, limit: usize) -> Self {
		self.int_eager_limit = Some(limit);
		self
	}

	/// Change whether to enable restarts in the oracle solver.
	pub fn with_restart(mut self, restart: bool) -> Self {
		self.restart = restart;
		self
	}

	/// Change whether to enable the vivification in the oracle solver.
	pub fn with_vivification(mut self, vivification: bool) -> Self {
		self.vivification = vivification;
		self
	}
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

impl VariableMap {
	pub fn get<Sat, Sol>(&self, slv: &mut Solver<Sat>, index: &ModelView) -> SolverView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match index {
			ModelView::Bool(b) => SolverView::Bool(self.get_bool(slv, b)),
			ModelView::Int(i) => SolverView::Int(self.get_int(slv, i)),
		}
	}

	pub fn get_bool<Sat, Sol>(&self, slv: &mut Solver<Sat>, bv: &bool::BoolView) -> BoolView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let get_int_lit = |slv: &mut Solver<Sat>, iv: &int::IntView, lit_meaning: LitMeaning| {
			let iv = self.get_int(slv, iv);
			slv.get_int_lit(iv, lit_meaning)
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
			bool::BoolView::IntLessEq(v, i) => get_int_lit(slv, v, LitMeaning::Less(i + 1)),
			bool::BoolView::IntNotEq(v, i) => get_int_lit(slv, v, LitMeaning::NotEq(*i)),
		}
	}

	pub fn get_int<Sat, Sol>(&self, slv: &mut Solver<Sat>, iv: &int::IntView) -> IntView
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

	#[expect(
		dead_code,
		reason = "TODO: investigate whether this can be used for SAT rewriting"
	)]
	pub(crate) fn insert_bool(&mut self, index: RawVar, elem: BoolView) {
		let _ = self.map.insert(index.into(), elem.into());
	}
}
