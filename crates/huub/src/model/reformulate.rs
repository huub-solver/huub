use std::collections::HashMap;

use crate::{
	model::Variable,
	solver::{BoolView, IntView},
};

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: HashMap<Variable, SimplifiedVariable>,
}

impl VariableMap {
	pub fn get(&self, index: &Variable) -> SimplifiedVariable {
		self.map.get(index).copied().unwrap_or_else(|| match index {
			Variable::Bool(x) => {
				SimplifiedVariable::Bool(SimplifiedBool::Lit(BoolView(x.0.into())))
			}
			Variable::Int(_) => unreachable!(),
		})
	}

	pub fn insert(&mut self, index: Variable, elem: SimplifiedVariable) {
		self.map.insert(index, elem);
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimplifiedVariable {
	Bool(SimplifiedBool),
	Int(SimplifiedInt),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimplifiedBool {
	Lit(BoolView),
	Val(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimplifiedInt {
	Var(IntView),
	Val(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReifContext {
	Pos,
	#[allow(dead_code)]
	Neg,
	#[allow(dead_code)]
	Mixed,
}
