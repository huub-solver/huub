//! Module containing structures for tracking the relationships between Boolean
//! variables and integer variables.

use std::collections::HashMap;

use pindakaas::{Var as RawVar, VarRange};

use crate::{solver::int_var::IntVarRef, IntLitMeaning};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
/// A mapping of Boolean variables to integer variables of which they represent
/// conditions.
pub(crate) struct BoolToIntMap {
	/// The mapping of eagerly created Boolean variables to the integer variables.
	eager: Vec<(VarRange, IntVarRef)>,
	/// The mapping of lazily created Boolean variables to the integer variables
	/// and their meanings.
	lazy: HashMap<RawVar, (IntVarRef, IntLitMeaning)>,
}

impl BoolToIntMap {
	/// Return the integer variable the given Boolean variable represents a
	/// condition for, if any. If the Boolean variable was lazily created, then
	/// also return the [`LitMeaning`] of the literal.
	pub(crate) fn get(&self, var: RawVar) -> Option<(IntVarRef, Option<IntLitMeaning>)> {
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
	/// Insert a range of Boolean variables to map them to the integer variable
	/// for which they are eagerly created to represent conditions for.
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

	/// Insert a mapping of a lazily created Boolean variable to the integer
	/// variable and the meaning of the literal on the integer variable.
	pub(crate) fn insert_lazy(&mut self, var: RawVar, iv: IntVarRef, lit: IntLitMeaning) {
		let x = self.lazy.insert(var, (iv, lit));
		debug_assert_eq!(x, None, "lazy literal already exists");
	}
}
