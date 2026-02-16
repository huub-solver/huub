//! Traits for performing actions on integer decision variables.

use std::{fmt::Debug, hash::Hash};

use rangelist::IntervalIterator;

use crate::{
	IntSet, IntVal,
	actions::{PropagationActions, ReasoningContext},
	constraints::ReasonBuilder,
	solver::IntLitMeaning,
};

/// Actions available to [`Brancher`](crate::solver::branchers::Brancher)
/// implementations for integer decision variables.
///
/// These actions are also available to
/// [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// [`ReasoningEngine::PropagationCtx`](crate::actions::ReasoningEngine::PropagationCtx).
pub trait IntDecisionActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Get (or create) a literal for the given referenced integer variable with
	/// the given meaning.
	fn lit(&self, ctx: &mut Context, meaning: IntLitMeaning) -> Context::Atom;

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned.
	fn val_lit(&self, ctx: &mut Context) -> Option<Context::Atom> {
		let val = self.val(ctx)?;
		Some(self.lit(ctx, IntLitMeaning::Eq(val)))
	}
}

/// Actions available to [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// [`ReasoningEngine::ExplanationCtx`](crate::actions::ReasoningEngine::ExplanationCtx) for
/// integer decision variables.
pub trait IntExplanationActions<Context>: IntInspectionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, or a relaxation if the literal does not yet
	/// exist.
	fn lit_relaxed(&self, ctx: &Context, meaning: IntLitMeaning) -> (Context::Atom, IntLitMeaning);

	/// Get the Boolean view that represents the current assignment of the
	/// integer view, or `None` if the integer view is not assigned or if the
	/// equality literal does not exist.
	fn try_val_lit(&self, ctx: &Context) -> Option<Context::Atom> {
		let val = self.val(ctx)?;
		self.try_lit(ctx, IntLitMeaning::Eq(val))
	}
}

/// Actions available to [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// all contexts for integer decision variables.
pub trait IntInspectionActions<Context>: IntOperations
where
	Context: ReasoningContext + ?Sized,
{
	/// Convenience method to get both the [`Self::min`] and [`Self::max`] of an
	/// integer view.
	fn bounds(&self, ctx: &Context) -> (IntVal, IntVal);
	/// Get the set of values from which the integer view is guaranteed to take
	/// a value (given the current search decisions).
	fn domain(&self, ctx: &Context) -> IntSet;

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn in_domain(&self, ctx: &Context, val: IntVal) -> bool;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn lit_meaning(&self, ctx: &Context, lit: Context::Atom) -> Option<IntLitMeaning>;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn max(&self, ctx: &Context) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn max_lit(&self, ctx: &Context) -> Context::Atom;

	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn min(&self, ctx: &Context) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn min_lit(&self, ctx: &Context) -> Context::Atom;

	/// Get a Boolean view that represents the given meaning on the integer
	/// view, if it already exists.
	fn try_lit(&self, ctx: &Context, meaning: IntLitMeaning) -> Option<Context::Atom>;

	/// Get the current value of an integer view, if it has been assigned (given
	/// the current search decisions).
	fn val(&self, ctx: &Context) -> Option<IntVal>;
}

/// Operations that are required to be possible to perform on types acting as
/// integer decision variables.
pub trait IntOperations: Clone + Debug + Eq + Hash + 'static {}

/// Actions available to [`Propagator`](crate::constraints::Propagator) and
/// [`Constraint`](crate::constraints::Constraint) implementations in
/// [`ReasoningEngine::PropagationCtx`](crate::actions::ReasoningEngine::PropagationCtx) for integer decision variables.
pub trait IntPropagationActions<Context>: IntDecisionActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that a an integer view takes a value `val` because of the given
	/// `reason`.
	fn fix(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view cannot take a value `val` because of the
	/// given `reason`.
	fn remove_val(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val` because of the given `reason`.
	fn tighten_max(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val` because of the given `reason`.
	fn tighten_min(
		&self,
		ctx: &mut Context,
		val: IntVal,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;
}

/// Actions available to [`Constraint`](crate::constraints::Constraint)
/// implementations in
/// [`ReasoningEngine::PropagationCtx`](crate::actions::ReasoningEngine::PropagationCtx)
/// for integer decision variables.
///
/// Generally these actions are used in
/// [`Constraint::simplify`](crate::constraints::Constraint::simplify).
pub trait IntSimplificationActions<Context>: IntPropagationActions<Context>
where
	Context: ReasoningContext + ?Sized,
{
	/// Enforce that a given integer expression cannot take any of the values in
	/// the given set.
	fn exclude(
		&self,
		ctx: &mut Context,
		values: &IntSet,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Enforce that the given integer expression takes a value in in the given
	/// set.
	fn restrict_domain(
		&self,
		ctx: &mut Context,
		domain: &IntSet,
		reason: impl ReasonBuilder<Context>,
	) -> Result<(), Context::Conflict>;

	/// Mark two integer decisions as being equivalent, ensuring the two use the
	/// same internal representation.
	fn unify(&self, ctx: &mut Context, other: impl Into<Self>) -> Result<(), Context::Conflict>;
}

impl<Ctx> IntDecisionActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		self.try_lit(ctx, meaning).unwrap()
	}
}

impl<Ctx> IntExplanationActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		(self.try_lit(ctx, meaning).unwrap(), meaning)
	}
}

impl<Ctx> IntInspectionActions<Ctx> for IntVal
where
	Ctx: ReasoningContext + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn bounds(&self, _: &Ctx) -> (IntVal, IntVal) {
		(*self, *self)
	}

	fn domain(&self, _: &Ctx) -> IntSet {
		(*self..=*self).into()
	}

	fn in_domain(&self, _: &Ctx, val: IntVal) -> bool {
		*self == val
	}

	fn lit_meaning(&self, _: &Ctx, _: Ctx::Atom) -> Option<IntLitMeaning> {
		None
	}

	fn max(&self, _: &Ctx) -> IntVal {
		*self
	}

	fn max_lit(&self, _: &Ctx) -> Ctx::Atom {
		true.into()
	}

	fn min(&self, _: &Ctx) -> IntVal {
		*self
	}

	fn min_lit(&self, _: &Ctx) -> Ctx::Atom {
		true.into()
	}

	fn try_lit(&self, _: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		Some(
			match meaning {
				IntLitMeaning::Eq(v) => *self == v,
				IntLitMeaning::NotEq(v) => *self != v,
				IntLitMeaning::GreaterEq(v) => *self >= v,
				IntLitMeaning::Less(v) => *self < v,
			}
			.into(),
		)
	}

	fn val(&self, _: &Ctx) -> Option<IntVal> {
		Some(*self)
	}
}

impl<Ctx> IntPropagationActions<Ctx> for IntVal
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val != *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn remove_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val == *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val < *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if val > *self {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}
}

impl<Ctx> IntSimplificationActions<Ctx> for IntVal
where
	Ctx: PropagationActions + ?Sized,
	Ctx::Atom: From<bool>,
{
	fn exclude(
		&self,
		ctx: &mut Ctx,
		values: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if values.contains(self) {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn restrict_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		if !domain.contains(self) {
			Err(ctx.declare_conflict(reason))
		} else {
			Ok(())
		}
	}

	fn unify(&self, ctx: &mut Ctx, other: impl Into<Self>) -> Result<(), Ctx::Conflict> {
		if self == &other.into() {
			Ok(())
		} else {
			Err(ctx.declare_conflict([]))
		}
	}
}

impl<T> IntOperations for T where T: Clone + Debug + Eq + Hash + 'static {}
