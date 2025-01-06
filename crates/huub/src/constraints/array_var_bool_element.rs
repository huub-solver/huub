//! Structures and algorithms for the `array_var_bool_element` constraint, which
//! enforces that a resulting variable equals an element of an array of Boolean
//! decision variables, chosen by an index variable.

use std::iter::once;

use pindakaas::{propositional_logic::Formula, ClauseDatabaseTools};

use crate::{
	actions::{ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	model::{bool::BoolView, int::IntExpr},
	IntVal, LitMeaning, ReformulationError,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_var_bool_element` constraint within a model.
///
/// This constraint enforces that a result Boolean decision variable takes the
/// value equal the element of the given array of Boolean decision varaibles at
/// the index given by the index integer decision variable.
pub struct ArrayVarBoolElement {
	/// The array of Boolean decision expressions
	pub(crate) array: Vec<BoolView>,
	/// The index variable
	pub(crate) index: IntExpr,
	/// The resulting variable
	pub(crate) result: BoolView,
}

impl<S: SimplificationActions> Constraint<S> for ArrayVarBoolElement {
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

		for (i, l) in arr.iter().enumerate() {
			// Evaluate array literal
			let idx_eq = slv.get_int_lit(index, LitMeaning::Eq(i as IntVal));
			// add clause (idx = i + 1 /\ arr[i]) => val
			slv.add_clause([!idx_eq, !l, result])?;
			// add clause (idx = i + 1 /\ !arr[i]) => !val
			slv.add_clause([!idx_eq, *l, !result])?;
		}

		// add clause (arr[1] /\ arr[2] /\ ... /\ arr[n]) => val
		slv.add_clause(arr.iter().map(|l| !l).chain(once(result)))?;
		// add clause (!arr[1] /\ !arr[2] /\ ... /\ !arr[n]) => !val
		slv.add_clause(arr.into_iter().chain(once(!result)))?;
		Ok(())
	}
}
