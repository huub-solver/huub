use pindakaas::{solver::VarRange, Var as RawVar};

use super::int_var::IntVarRef;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct BoolToIntMap {
	storage: Vec<(VarRange, IntVarRef)>,
}

impl BoolToIntMap {
	pub fn insert(&mut self, range: VarRange, var: IntVarRef) {
		if range.is_empty() {
			return;
		}
		if self.storage.is_empty() || self.storage.last().unwrap().0.end() < range.start() {
			self.storage.push((range, var));
			return;
		}
		panic!("Literal Mapping not added in the correct order")
	}

	pub fn get(&self, var: RawVar) -> Option<IntVarRef> {
		self.storage
			.binary_search_by(|(range, _)| {
				if range.start() > var {
					std::cmp::Ordering::Greater
				} else if range.end() < var {
					std::cmp::Ordering::Less
				} else {
					std::cmp::Ordering::Equal
				}
			})
			.ok()
			.map(|i| self.storage[i].1)
	}
}
