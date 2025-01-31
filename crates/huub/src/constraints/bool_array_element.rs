//! Structures and algorithms for the Boolean array element constraint, which
//! enforces that a resulting variable equals an element of an array of Boolean
//! decision variables, chosen by an index variable.

use std::iter::once;

use pindakaas::{propositional_logic::Formula, ClauseDatabaseTools};

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
		if let Some(i) = actions.get_int_val(self.index) {
			actions.add_constraint(Formula::Equiv(vec![
				self.array[i as usize].into(),
				self.result.into(),
			]));
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
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
