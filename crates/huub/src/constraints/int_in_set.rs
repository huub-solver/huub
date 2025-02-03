//! Structures and algorithms for the integer in set constraint, which
//! constraints that an integer decision variable is assigned to a member of a
//! given set if-and-only-if a given Boolean decision variable is assigned to
//! `true`.

use pindakaas::propositional_logic::Formula;

use crate::{
	actions::{ConstraintInitActions, ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	reformulate::ReformulationError,
	BoolDecision, IntDecision, IntSetVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `int_in_set_reif` constraint within a model.
///
/// This constraint enforces that the given Boolean variable takes the value
/// `true` if-and-only-if an integer variable is in a given set.
pub struct IntInSetReif {
	/// The integer decision variable monitored.
	pub(crate) var: IntDecision,
	/// The set of considered values for the integer decision variable.
	pub(crate) set: IntSetVal,
	/// The Boolean variable that indicates if the integer decision variable is in
	/// the set.
	pub(crate) reif: BoolDecision,
}

impl<S: SimplificationActions> Constraint<S> for IntInSetReif {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		actions.simplify_on_change_bool(self.reif);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		match actions.get_bool_val(self.reif) {
			Some(true) => {
				actions.set_int_in_set(self.var, &self.set)?;
				Ok(SimplificationStatus::Subsumed)
			}
			Some(false) => {
				actions.set_int_not_in_set(self.var, &self.set)?;
				Ok(SimplificationStatus::Subsumed)
			}
			None => Ok(SimplificationStatus::Fixpoint),
		}
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		if self.set.iter().len() == 1 {
			let lb = *self.set.lower_bound().unwrap();
			let ub = *self.set.upper_bound().unwrap();
			<Formula<BoolDecision> as Constraint<S>>::to_solver(
				&Formula::Equiv(vec![
					Formula::And(vec![self.var.geq(lb).into(), self.var.leq(ub).into()]),
					self.reif.into(),
				]),
				slv,
			)
		} else {
			let eq_lits = self
				.set
				.iter()
				.flatten()
				.map(|v| self.var.eq(v).into())
				.collect();
			<Formula<BoolDecision> as Constraint<S>>::to_solver(
				&Formula::Equiv(vec![self.reif.into(), Formula::Or(eq_lits)]),
				slv,
			)
		}
	}
}
