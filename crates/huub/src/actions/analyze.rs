//! Actions available to [`Constraint`](crate::constraints::Constraint)
//! implementations during the
//! [`analyze`](crate::constraints::Constraint::analyze) stage.

use crate::{IntVal, actions::ReasoningContext, solver::Polarity};

/// Actions available to [`Constraint`](crate::constraints::Constraint)
/// implementations in the
/// [`analyze`](crate::constraints::Constraint::analyze) stage for Boolean
/// decision variables.
pub trait BoolAnalyzeActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Record a unit of constraint-level polarity evidence stating that this
	/// Boolean view should be pushed in direction `polarity` (where
	/// [`Positive`](Polarity::Positive) means "prefer true") to make the
	/// constraint easier to satisfy.
	fn polarity(&self, ctx: &mut Context, polarity: Polarity);
}

/// Actions available to [`Constraint`](crate::constraints::Constraint)
/// implementations in the
/// [`analyze`](crate::constraints::Constraint::analyze) stage for integer
/// decision variables.
pub trait IntAnalyzeActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Record a unit of constraint-level polarity evidence stating that this
	/// integer view should be pushed in direction `polarity` to make the
	/// constraint easier to satisfy.
	fn polarity(&self, ctx: &mut Context, polarity: Polarity);

	/// Request that the direct encoding (the literals for the equality
	/// conditions `x = i`) of this integer view be created eagerly.
	fn request_direct_eager(&self, ctx: &mut Context);

	/// Request that the order encoding (the literals for the inequality
	/// conditions `x < i`) of this integer view be created eagerly.
	fn request_order_eager(&self, ctx: &mut Context);
}

impl<Context> IntAnalyzeActions<Context> for IntVal
where
	Context: ReasoningContext + ?Sized,
{
	fn polarity(&self, _: &mut Context, _: Polarity) {
		// A constant has no decision to record evidence on.
	}

	fn request_direct_eager(&self, _: &mut Context) {
		// A constant has no literals to create.
	}

	fn request_order_eager(&self, _: &mut Context) {
		// A constant has no literals to create.
	}
}

impl<Context> BoolAnalyzeActions<Context> for bool
where
	Context: ReasoningContext + ?Sized,
{
	fn polarity(&self, _: &mut Context, _: Polarity) {
		// A constant has no decision to record evidence on.
	}
}
