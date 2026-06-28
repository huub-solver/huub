//! Definitions for the default Boolean decision variable view employed in
//! [`Model`].

use std::{
	mem,
	num::NonZero,
	ops::{Add, Mul, Not, Sub},
};

use crate::{
	IntVal,
	actions::{
		BoolAnalyzeActions, BoolInspectionActions, BoolPropagationActions,
		BoolSimplificationActions, IntInspectionActions, IntPropCond, PropagationActions,
		ReasoningContext,
	},
	constraints::{Conflict, NO_REASON, Nogood},
	model::{
		AdvRef, Advisor, ConRef, Model, SimplificationContext, SimplificationReasonSink,
		decision::Decision,
		expressions::BoolFormula,
		resolved::Resolved,
		view::{DefaultView, View, private},
	},
	solver::{IntLitMeaning, Polarity, activation_list::ActivationAction},
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Inner storage for [`BoolDecision`], kept private to prevent access from
/// users.
#[non_exhaustive]
pub enum BoolView {
	/// A Boolean decision variable or its negation.
	Decision(Decision<bool>),
	/// A constant Boolean value.
	Const(bool),
	/// Whether an integer is equal to a constant.
	IntEq(Decision<IntVal>, IntVal),
	/// Whether an integer is greater than or equal to a constant.
	IntGreaterEq(Decision<IntVal>, IntVal),
	/// Whether an integer is less than a constant.
	IntLess(Decision<IntVal>, IntVal),
	/// Whether an integer is not equal to a constant.
	IntNotEq(Decision<IntVal>, IntVal),
}

impl Resolved<View<bool>> {
	/// Consuming variant of [`BoolPropagationActions::fix`].
	pub(crate) fn fix<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		val: bool,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		let lit = if val { self.0 } else { !self.0 };
		Resolved(lit).require(ctx, reason)
	}

	/// Consuming variant of [`BoolPropagationActions::require`].
	pub(crate) fn require<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		match self.0.0 {
			Decision(l) => {
				let model = &mut *ctx.0;
				let def = &mut model.bool_vars[l.idx()];
				debug_assert!(def.alias.is_none());
				def.alias = Some(View(Const(!l.is_negated())));
				model.bool_events.push(l.var());
			}
			Const(c) => c.require(ctx, reason)?,
			IntEq(iv, val) => iv.resolve_alias(&*ctx.0).fix(ctx, val, reason)?,
			IntGreaterEq(iv, val) => {
				iv.resolve_alias(&*ctx.0).tighten_min(ctx, val, reason)?;
			}
			IntLess(iv, val) => {
				iv.resolve_alias(&*ctx.0)
					.tighten_max(ctx, val - 1, reason)?;
			}
			IntNotEq(iv, val) => iv.resolve_alias(&*ctx.0).remove_val(ctx, val, reason)?,
		};
		Ok(())
	}

	/// Consuming variant of [`BoolSimplificationActions::unify`].
	pub(crate) fn unify(
		self,
		ctx: &mut SimplificationContext<'_>,
		other: Resolved<View<bool>>,
	) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		let x = self.0;
		let y = other.0;

		match (x.0, y.0) {
			(x, y) if x == y => Ok(()),
			(Decision(xl), Decision(yl)) if xl.var() == yl.var() => {
				Err(ctx.declare_conflict(|_, reason| {
					reason.extend([x, y]);
				}))
			}
			(Const(x), Const(y)) if x != y => Err(ctx.declare_conflict(NO_REASON)),
			(x, Const(b)) | (Const(b), x) => Resolved(View::<bool>(x)).fix(ctx, b, NO_REASON),
			(Decision(x), y) | (y, Decision(x)) => {
				let (x, y) = if let Decision(y) = y {
					if x.0.var() > y.0.var() {
						(x, View(Decision(y)))
					} else {
						(y, View(Decision(x)))
					}
				} else {
					(x, View(y))
				};
				let model = &mut *ctx.0;
				let store = &mut model.bool_vars[x.idx()];
				debug_assert_eq!(store.alias, None);
				store.alias = Some(if x.is_negated() { !y } else { y });

				// Move subscriptions from aliased variable to the new primary variable
				let constraints = mem::take(&mut store.constraints);
				match y.0 {
					// Move subscriptions to another Boolean decision
					Decision(lit) => model.bool_vars[lit.idx()].constraints.extend(constraints),
					// Move subscriptions to an integer decision
					IntEq(j, _) | IntGreaterEq(j, _) | IntLess(j, _) | IntNotEq(j, _) => {
						for act in constraints {
							let event = if matches!(y.0, IntEq(_, _) | IntNotEq(_, _)) {
								IntPropCond::Domain
							} else {
								IntPropCond::Bounds
							};
							match ActivationAction::<AdvRef, ConRef>::from(act) {
								ActivationAction::Advise(adv) => {
									let def: &mut Advisor = &mut model.advisors[adv.index()];
									def.condition = Some(match y.0 {
										IntEq(_, v) => IntLitMeaning::Eq(v),
										IntGreaterEq(_, v) => IntLitMeaning::GreaterEq(v),
										IntLess(_, v) => IntLitMeaning::Less(v),
										IntNotEq(_, v) => IntLitMeaning::NotEq(v),
										_ => unreachable!(),
									});
									model.int_vars[j.idx()]
										.constraints
										.add(ActivationAction::Advise(adv), event);
								}
								me @ ActivationAction::Enqueue(_) => {
									// TODO: This triggers even when the Boolean Condition does not
									// change value
									model.int_vars[j.idx()].constraints.add(me, event);
								}
							}
						}
					}
					Const(_) => unreachable!(),
				};
				Ok(())
			}
			(x, y) => {
				let x = BoolFormula::Atom(View(x));
				let y = BoolFormula::Atom(View(y));

				ctx.0
					.post_constraint_internal(BoolFormula::Equiv(vec![x, y]));
				Ok(())
			}
		}
	}
}

impl BoolInspectionActions<Model> for Resolved<View<bool>> {
	fn val(&self, ctx: &Model) -> Option<bool> {
		use BoolView::*;

		match self.0.0 {
			// View on a constant, or a Boolean decision that was fixed by
			// propagation (and therefore aliased to a `Const`).
			Const(b) => Some(b),
			// Integer comparison views must look at the underlying integer domain to determine
			// whether a value has been assigned to the Boolean decision.
			IntEq(iv, val) | IntNotEq(iv, val) if iv.val(ctx) == Some(val) => {
				Some(matches!(self.0.0, IntEq(_, _)))
			}
			IntEq(iv, val) | IntNotEq(iv, val) if !iv.in_domain(ctx, val) => {
				Some(matches!(self.0.0, IntNotEq(_, _)))
			}
			IntGreaterEq(iv, val) | IntLess(iv, val) if iv.min(ctx) >= val => {
				Some(matches!(self.0.0, IntGreaterEq(_, _)))
			}
			IntGreaterEq(iv, val) | IntLess(iv, val) if iv.max(ctx) < val => {
				Some(matches!(self.0.0, IntLess(_, _)))
			}
			_ => None,
		}
	}
}

impl BoolInspectionActions<SimplificationContext<'_>> for Resolved<View<bool>> {
	fn val(&self, ctx: &SimplificationContext<'_>) -> Option<bool> {
		self.val(&*ctx.0)
	}
}

impl Add<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn add(self, rhs: IntVal) -> Self::Output {
		let me: View<IntVal> = self.into();
		me + rhs
	}
}

impl<Ctx> BoolAnalyzeActions<Ctx> for View<bool>
where
	Ctx: ReasoningContext + ?Sized,
	Decision<bool>: BoolAnalyzeActions<Ctx>,
{
	fn polarity(&self, ctx: &mut Ctx, polarity: Polarity) {
		// Only views backed by a pure Boolean decision carry recordable
		// evidence; the decision resolves any alias and folds its negation.
		if let BoolView::Decision(l) = self.0 {
			l.polarity(ctx, polarity);
		}
	}
}

impl BoolInspectionActions<Model> for View<bool> {
	fn val(&self, ctx: &Model) -> Option<bool> {
		self.resolve_alias(ctx).val(ctx)
	}
}

impl BoolInspectionActions<SimplificationContext<'_>> for View<bool> {
	fn val(&self, ctx: &SimplificationContext<'_>) -> Option<bool> {
		self.val(&*ctx.0)
	}
}

impl BoolPropagationActions<Model> for View<bool> {
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
		.map_err(Conflict::into_nogood)
	}

	fn require(
		&self,
		ctx: &mut Model,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.require(&mut SimplificationContext(ctx), Model::adapt_reason(reason))
			.map_err(Conflict::into_nogood)
	}
}

impl<'a> BoolPropagationActions<SimplificationContext<'a>> for View<bool> {
	fn fix(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: bool,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).fix(ctx, val, reason)
	}

	fn require(
		&self,
		ctx: &mut SimplificationContext<'a>,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).require(ctx, reason)
	}
}

impl BoolSimplificationActions<Model> for View<bool> {
	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Nogood<View<bool>>> {
		self.unify(&mut SimplificationContext(ctx), other)
			.map_err(Conflict::into_nogood)
	}
}

impl BoolSimplificationActions<SimplificationContext<'_>> for View<bool> {
	fn unify(
		&self,
		ctx: &mut SimplificationContext<'_>,
		other: impl Into<Self>,
	) -> Result<(), Conflict<View<bool>>> {
		let other = other.into().resolve_alias(&*ctx.0);
		self.resolve_alias(&*ctx.0).unify(ctx, other)
	}
}

impl From<Decision<bool>> for View<bool> {
	fn from(decision: Decision<bool>) -> Self {
		View(BoolView::Decision(decision))
	}
}

impl From<Resolved<View<bool>>> for View<bool> {
	fn from(value: Resolved<View<bool>>) -> Self {
		value.into_inner()
	}
}

impl From<bool> for View<bool> {
	fn from(v: bool) -> Self {
		View(BoolView::Const(v))
	}
}

impl Mul<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn mul(self, rhs: IntVal) -> Self::Output {
		let me: View<IntVal> = self.into();
		me * rhs
	}
}

impl Mul<NonZero<IntVal>> for View<bool> {
	type Output = View<IntVal>;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		let me: View<IntVal> = self.into();
		me * rhs
	}
}

impl Not for View<bool> {
	type Output = Self;

	fn not(self) -> Self::Output {
		use BoolView::*;

		View(match self.0 {
			Decision(l) => Decision(!l),
			Const(b) => Const(!b),
			IntEq(v, i) => IntNotEq(v, i),
			IntGreaterEq(v, i) => IntLess(v, i),
			IntLess(v, i) => IntGreaterEq(v, i),
			IntNotEq(v, i) => IntEq(v, i),
		})
	}
}

impl Sub<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}

impl DefaultView for bool {
	type View = BoolView;
}
impl private::Sealed for bool {}

#[cfg(test)]
mod tests {
	use crate::{
		actions::{BoolInspectionActions, IntInspectionActions, IntPropagationActions},
		constraints::NO_REASON,
		model::Model,
	};

	/// A Boolean view over an integer decision comparison must report its value
	/// as soon as its domain allows us to determine it.
	#[test]
	fn int_cmp_view_val() {
		let mut prb = Model::default();
		let x = prb.new_int_decision(1..=5);

		// Nothing is entailed for an untouched domain.
		assert_eq!(x.eq(4).val(&prb), None);
		assert_eq!(x.ne(4).val(&prb), None);
		assert_eq!(x.geq(3).val(&prb), None);
		assert_eq!(x.lt(3).val(&prb), None);

		// Removing the single value `4` allows us to determine the value of the
		// (in)equality.
		x.remove_val(&mut prb, 4, NO_REASON).unwrap();
		assert_eq!(x.val(&prb), None);
		assert_eq!(x.eq(4).val(&prb), Some(false));
		assert_eq!(x.ne(4).val(&prb), Some(true));

		// Tightening the lower bound entails the threshold comparisons while `x`
		// (now in 3, 5) stays unfixed.
		x.tighten_min(&mut prb, 3, NO_REASON).unwrap();
		assert_eq!(x.val(&prb), None);
		assert_eq!(x.geq(3).val(&prb), Some(true));
		assert_eq!(x.lt(3).val(&prb), Some(false));
		assert_eq!(x.geq(6).val(&prb), Some(false));
	}
}
