//! Boolean decision variable definitions for the model layer.

use std::ops::Not;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions},
	constraints::{Conflict, Nogood},
	model::{
		Model, SimplificationContext, SimplificationReasonSink,
		decision::{Decision, DecisionReference, PolarityScore, private},
		view::View,
	},
	solver::activation_list::ActivationActionS,
};

/// Definition of an Boolean decision variable in a [`Model`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct BoolDecision {
	/// Whether the Boolean variable has already been assigned a value, or has
	/// been aliased to another variable.
	pub(crate) alias: Option<View<bool>>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<ActivationActionS>,
	/// Accumulated polarity evidence collected during the analyze stage.
	pub(crate) polarity: PolarityScore,
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
		self.resolve_alias(ctx).val(ctx)
	}
}

impl BoolInspectionActions<SimplificationContext<'_>> for Decision<bool> {
	fn val(&self, ctx: &SimplificationContext<'_>) -> Option<bool> {
		self.val(&*ctx.0)
	}
}

impl BoolPropagationActions<Model> for Decision<bool> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: bool,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.fix(
			&mut SimplificationContext(ctx),
			val,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}
}

impl<'a> BoolPropagationActions<SimplificationContext<'a>> for Decision<bool> {
	fn fix(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: bool,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).fix(ctx, val, reason)
	}
}

impl BoolSimplificationActions<Model> for Decision<bool> {
	fn unify(
		&self,
		ctx: &mut Model,
		other: impl Into<View<bool>>,
	) -> Result<(), Nogood<View<bool>>> {
		self.unify(&mut SimplificationContext(ctx), other)
			.map_err(Conflict::into_model_nogood)
	}
}

impl BoolSimplificationActions<SimplificationContext<'_>> for Decision<bool> {
	fn unify(
		&self,
		ctx: &mut SimplificationContext<'_>,
		other: impl Into<View<bool>>,
	) -> Result<(), Conflict<View<bool>>> {
		let other = other.into().resolve_alias(&*ctx.0);
		self.resolve_alias(&*ctx.0).unify(ctx, other)
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
