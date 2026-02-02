//! Boolean decision variable definitions for the model layer.

use std::ops::Not;

use pindakaas::Lit as RawLit;

use crate::{
	actions::BoolInspectionActions,
	model::{
		Model,
		decision::{Decision, DecisionReference, private},
		view::View,
	},
	solver::activation_list::ActivationActionS,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Definition of an Boolean decision variable in a [`Model`].
pub(crate) struct BoolDecision {
	/// Whether the Boolean variable has already been assigned a value, or has
	/// been aliased to another variable.
	pub(crate) alias: Option<View<bool>>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<ActivationActionS>,
}

impl Decision<bool> {
	/// Return the index used to access this decision in model storage.
	pub(crate) fn idx(&self) -> usize {
		(i32::from(self.0.var()) - 1) as usize
	}

	/// Return whether this decision represents a negated literal.
	pub(crate) fn is_negated(&self) -> bool {
		self.0.is_negated()
	}

	/// Return the non-negated decision variable for this literal.
	pub(crate) fn var(&self) -> Self {
		Decision(self.0.var().into())
	}
}

impl BoolInspectionActions<Model> for Decision<bool> {
	fn val(&self, ctx: &Model) -> Option<bool> {
		let view: View<bool> = (*self).into();
		view.val(ctx)
	}
}

impl Not for Decision<bool> {
	type Output = Self;

	fn not(self) -> Self::Output {
		Decision(!self.0)
	}
}

impl DecisionReference for bool {
	type Ref = RawLit;
}
impl private::Sealed for bool {}
