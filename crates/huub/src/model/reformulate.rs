use std::collections::BTreeMap;

use crate::{Literal, Variable};

/// A reformulation mapping helper that automatically maps variables to
/// themselves unless otherwise specified
#[derive(Default, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableMap {
	// Note the "to" of the mapping will likely need to be appended
	map: BTreeMap<Variable, Variable>,
}

impl VariableMap {
	pub fn get(&self, index: &Variable) -> SimplifiedVariable {
		self.map
			.get(index)
			.map(|v| match v {
				Variable::Bool(x) => SimplifiedVariable::Bool(SimplifiedBool::Lit((*x).into())),
			})
			.unwrap_or_else(|| match index {
				Variable::Bool(x) => SimplifiedVariable::Bool(SimplifiedBool::Lit((*x).into())),
			})
	}
}

pub enum SimplifiedBool {
	Lit(Literal),
	Val(bool),
}

pub enum SimplifiedVariable {
	Bool(SimplifiedBool),
}

pub enum ReifContext {
	Pos,
	#[allow(dead_code)]
	Neg,
	#[allow(dead_code)]
	Mixed,
}
