//! Structures and algorithms for the Boolean array element constraint, which
//! enforces that a resulting variable equals an element of an array of Boolean
//! decision variables, chosen by an index variable.

use std::iter::once;

use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	reformulate::ReformulationError,
	solver::IntLitMeaning,
	BoolDecision, IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_element` constraint with an array of Boolean
/// decision variables within a model.
///
/// This constraint enforces that a result Boolean decision variable takes the
/// value equal the element of the given array of Boolean decision varaibles at
/// the index given by the index integer decision variable.
pub struct BoolDecisionArrayElement {
	/// The array of Boolean decision variables
	pub(crate) array: Vec<BoolDecision>,
	/// The index variable
	pub(crate) index: IntDecision,
	/// The resulting variable
	pub(crate) result: BoolDecision,
}

impl<S: SimplificationActions> Constraint<S> for BoolDecisionArrayElement {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// Fix the bounds of the index is to the length of the array
		actions.set_int_lower_bound(self.index, 0)?;
		actions.set_int_upper_bound(self.index, self.array.len() as IntVal - 1)?;
		// Unify if the index is already fixed
		if let Some(i) = actions.get_int_val(self.index) {
			actions.unify_bool(self.array[i as usize], self.result)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let result = slv.get_solver_bool(self.result);
		let index = slv.get_solver_int(self.index);

		// Evaluate result literal
		let arr: Vec<_> = self.array.iter().map(|&v| slv.get_solver_bool(v)).collect();

		for (i, &l) in arr.iter().enumerate() {
			// Evaluate array literal
			let idx_eq = slv.get_int_lit(index, IntLitMeaning::Eq(i as IntVal));
			// add clause (idx = i + 1 /\ arr[i]) => val
			slv.add_clause([!idx_eq, !l, result])?;
			// add clause (idx = i + 1 /\ !arr[i]) => !val
			slv.add_clause([!idx_eq, l, !result])?;
		}

		// add clause (arr[1] /\ arr[2] /\ ... /\ arr[n]) => val
		slv.add_clause(arr.iter().map(|&l| !l).chain(once(result)))?;
		// add clause (!arr[1] /\ !arr[2] /\ ... /\ !arr[n]) => !val
		slv.add_clause(arr.into_iter().chain(once(!result)))?;
		Ok(())
	}
}
