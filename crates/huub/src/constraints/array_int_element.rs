//! Structures and algorithms for the `array_int_element` constraint, which
//! enforces that a resulting variable equals an element of an array of integer
//! values, chosen by an index variable.

use std::iter::once;

use itertools::Itertools;
use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{ReformulationActions, SimplificationActions},
	constraints::Constraint,
	reformulate::ReformulationError,
	solver::IntLitMeaning,
	IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_int_element` constraint within a model.
///
/// This constraint enforces that a result integer decision variable takes the
/// value equal the element of the given array of integer values at the given
/// index decision variable.
pub struct ArrayIntElement {
	/// The array of integer values
	pub(crate) array: Vec<IntVal>,
	/// The index variable
	pub(crate) index: IntDecision,
	/// The resulting variable
	pub(crate) result: IntDecision,
}

impl<S: SimplificationActions> Constraint<S> for ArrayIntElement {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let index = slv.get_solver_int(self.index);
		let result = slv.get_solver_int(self.result);

		let idx_map = self
			.array
			.iter()
			.enumerate()
			.map(|(i, v)| (*v, i as IntVal))
			.into_group_map();

		for (val, idxs) in idx_map {
			let val_eq = slv.get_int_lit(result, IntLitMeaning::Eq(val));
			let idxs: Vec<_> = idxs
				.into_iter()
				.map(|i| slv.get_int_lit(index, IntLitMeaning::Eq(i)))
				.collect();

			for &i in idxs.iter() {
				// (idx = i) -> (val = arr[i])
				slv.add_clause([!i, val_eq])?;
			}
			// (idx not in idxs) -> (val != arr[i])
			slv.add_clause(idxs.into_iter().chain(once(!val_eq)))?;
		}
		Ok(())
	}
}
