use std::collections::HashMap;

use crate::{
	model::Variable,
	solver::{view::BoolViewInner, BoolView, SolverView},
};

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: HashMap<Variable, SolverView>,
}

impl VariableMap {
	pub fn get(&self, index: &Variable) -> SolverView {
		self.map.get(index).cloned().unwrap_or_else(|| match index {
			Variable::Bool(x) => SolverView::Bool(BoolView(BoolViewInner::Lit(x.0.into()))),
			Variable::Int(_) => unreachable!(),
		})
	}

	pub fn insert(&mut self, index: Variable, elem: SolverView) {
		let _ = self.map.insert(index, elem);
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
