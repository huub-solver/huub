//! Structures and algorithms for the integer in set constraint, which
//! constraints that an integer decision variable is assigned to a member of a
//! given set if-and-only-if a given Boolean decision variable is assigned to
//! `true`.

use pindakaas::propositional_logic::Formula;
use rangelist::IntervalIterator;

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
	/// The Boolean variable that indicates if the integer decision variable is
	/// in the set.
	pub(crate) reif: BoolDecision,
}

impl<S: SimplificationActions> Constraint<S> for IntInSetReif {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		actions.simplify_on_change_int(self.var);
		actions.simplify_on_change_bool(self.reif);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// Check whether `reif` is set, then just enforce the domain.
		match actions.get_bool_val(self.reif) {
			Some(true) => {
				actions.set_int_in_set(self.var, &self.set)?;
				return Ok(SimplificationStatus::Subsumed);
			}
			Some(false) => {
				actions.set_int_not_in_set(self.var, &self.set)?;
				return Ok(SimplificationStatus::Subsumed);
			}
			None => {}
		}
		// Compute the overlap between the set and the domain of `var`.
		let domain = actions.get_int_domain(self.var);
		self.set = self.set.intersect(&domain);
		// If the intersection is empty, then `reif` must be false.
		if self.set.is_empty() {
			actions.set_bool(!self.reif)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		// If `set` is a superset of domain, then it is known that `reif` is true.
		// (After intersection, we can just check equality)
		if domain == self.set {
			actions.set_bool(self.reif)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		// Otherwise, we check whether we can rewrite the constraint into a simpler
		// form.
		if self.set.intervals().len() == 1 {
			let lb = self.set.lower_bound().unwrap();
			let ub = self.set.upper_bound().unwrap();
			if lb == ub {
				actions.unify_bool(self.reif, self.var.eq(*lb))?;
				return Ok(SimplificationStatus::Subsumed);
			}
			if lb == domain.lower_bound().unwrap() {
				actions.unify_bool(self.reif, self.var.leq(*ub))?;
				return Ok(SimplificationStatus::Subsumed);
			}
			if ub == domain.upper_bound().unwrap() {
				actions.unify_bool(self.reif, self.var.geq(*lb))?;
				return Ok(SimplificationStatus::Subsumed);
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&mut self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		if self.set.iter().len() == 1 {
			let lb = *self.set.lower_bound().unwrap();
			let ub = *self.set.upper_bound().unwrap();
			<Formula<BoolDecision> as Constraint<S>>::to_solver(
				&mut Formula::Equiv(vec![
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
				&mut Formula::Equiv(vec![self.reif.into(), Formula::Or(eq_lits)]),
				slv,
			)
		}
	}
}
