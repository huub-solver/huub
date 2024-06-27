use std::collections::HashMap;

use pindakaas::{solver::VarRange, Var as RawVar};

use crate::{solver::engine::int_var::IntVarRef, LitMeaning};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub(crate) struct BoolToIntMap {
	eager: Vec<(VarRange, IntVarRef)>,
	lazy: HashMap<RawVar, (IntVarRef, LitMeaning)>,
}

impl BoolToIntMap {
	pub(crate) fn insert_eager(&mut self, range: VarRange, var: IntVarRef) {
		if range.is_empty() {
			return;
		}
		if self.eager.is_empty() || self.eager.last().unwrap().0.end() < range.start() {
			self.eager.push((range, var));
			return;
		}
		panic!("Literal Mapping not added in the correct order")
	}

	pub(crate) fn insert_lazy(&mut self, var: RawVar, iv: IntVarRef, lit: LitMeaning) {
		let x = self.lazy.insert(var, (iv, lit));
		debug_assert_eq!(x, None, "lazy literal already exists")
	}

	pub(crate) fn get(&self, var: RawVar) -> Option<(IntVarRef, Option<LitMeaning>)> {
		let is_eager = self
			.eager
			.last()
			.map(|(last, _)| var <= last.end())
			.unwrap_or(false);
		if is_eager {
			self.eager
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
				.map(|i| (self.eager[i].1, None))
		} else {
			self.lazy
				.get(&var)
				.map(|(int_var, meaning)| (*int_var, Some(meaning.clone())))
		}
	}
}
