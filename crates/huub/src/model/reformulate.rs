use std::{collections::HashMap, ops::Not};

use pindakaas::Var as RawVar;
use thiserror::Error;

use super::{bool, int, int::IntVar, ModelView};
use crate::{
	solver::view::{BoolView, BoolViewInner, SolverView},
	IntView,
};

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: HashMap<Variable, SolverView>,
}

impl VariableMap {
	pub fn get(&self, index: &ModelView) -> SolverView {
		let i = match index {
			ModelView::Bool(bool::BoolView::Const(l)) => {
				return SolverView::Bool(BoolView(BoolViewInner::Const(*l)))
			}
			ModelView::Bool(bool::BoolView::Lit(l)) => Variable::Bool(l.var()),
			ModelView::Int(int::IntView::Const(v)) => return SolverView::Int((*v).into()),
			ModelView::Int(int::IntView::Var(v)) | ModelView::Int(int::IntView::Linear(_, v)) => {
				Variable::Int(*v)
			}
		};

		let view = self.map.get(&i).cloned().unwrap_or_else(|| match i {
			Variable::Bool(x) => SolverView::Bool(BoolView(BoolViewInner::Lit(x.into()))),
			Variable::Int(_) => unreachable!(),
		});
		match index {
			ModelView::Bool(bool::BoolView::Lit(l)) if l.is_negated() => {
				let SolverView::Bool(bv) = view else {
					unreachable!()
				};
				SolverView::Bool(!bv)
			}
			ModelView::Int(int::IntView::Linear(t, _)) => {
				let SolverView::Int(iv) = view else {
					unreachable!()
				};
				SolverView::Int(iv * t.scale + t.offset)
			}
			_ => view,
		}
	}

	pub fn get_bool(&self, bv: bool::BoolView) -> BoolView {
		let SolverView::Bool(v) = self.get(&ModelView::Bool(bv)) else {
			unreachable!()
		};
		v
	}

	pub fn get_int(&self, iv: &int::IntView) -> IntView {
		let SolverView::Int(v) = self.get(&ModelView::Int(iv.clone())) else {
			unreachable!()
		};
		v
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
