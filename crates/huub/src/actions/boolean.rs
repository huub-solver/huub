//! Traits for performing actions on Boolean decision variables.

use std::{fmt::Debug, hash::Hash, ops::Not};

use crate::{
	actions::{PropagationActions, ReasoningContext},
	constraints::ReasonBuilder,
	model::view::View,
};

/// Actions available to [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// all contexts for Boolean decision variables.
pub trait BoolInspectionActions<Context: ?Sized>: BoolOperations {
	/// Get the current value of a Boolean decision variable, if it has been
	/// assigned.
	fn val(&self, ctx: &Context) -> Option<bool>;
}

/// Operations that are required to be possible to perform on types acting as
/// boolean decision variables.
pub trait BoolOperations: Clone + Debug + Eq + Hash + Not + 'static {}

/// Actions available to [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// [`ReasoningEngine::PropagationCtx`](crate::actions::ReasoningEngine::PropagationCtx)
/// for Boolean decision variables.
pub trait BoolPropagationActions<Context>: BoolInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that the value of a Boolean decision variable is to be `val`,
	/// because of the given reason.
	fn fix(
		&self,
		ctx: &mut Context,
		val: bool,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that the value of a Boolean decision variable is to be `true`,
	/// because of the given reason.
	fn require(
		&self,
		ctx: &mut Context,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict> {
		self.fix(ctx, true, reason)
	}
}

/// Actions available to [`Constraint`](crate::constraints::Constraint)
/// implementations in
/// [`ReasoningEngine::PropagationCtx`](crate::actions::ReasoningEngine::PropagationCtx)
/// for Boolean decision variables.
///
/// Generally these actions are used in
/// [`Constraint::simplify`](crate::constraints::Constraint::simplify).
pub trait BoolSimplificationActions<Context>:
	BoolPropagationActions<Context> + Into<View<bool>>
where
	Context: ReasoningContext + ?Sized,
{
	/// Mark `self` as being equivalent to `other`, instructing the reasoning
	/// engine to use the same representation.
	fn unify(
		&self,
		ctx: &mut Context,
		other: impl Into<View<bool>>,
	) -> Result<(), Context::Conflict>;
}

impl<T> BoolOperations for T where T: Clone + Debug + Eq + Hash + Not + 'static {}

impl<Ctx> BoolInspectionActions<Ctx> for bool {
	fn val(&self, _: &Ctx) -> Option<bool> {
		Some(*self)
	}
}

impl<Ctx> BoolPropagationActions<Ctx> for bool
where
	Ctx: ReasoningContext + PropagationActions,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: bool,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), <Ctx as ReasoningContext>::Conflict> {
		if *self != val {
			return Err(ctx.declare_conflict(reason));
		}
		Ok(())
	}
}
