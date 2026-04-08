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
		BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions,
		PropagationActions,
	},
	constraints::{Conflict, ReasonBuilder},
	model::{
		AdvRef, Advisor, ConRef, Model,
		decision::Decision,
		expressions::BoolFormula,
		resolved::Resolved,
		view::{DefaultView, View, private},
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, IntPropCond},
	},
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
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
	/// Whether an integer is greater or equal to a constant.
	IntGreaterEq(Decision<IntVal>, IntVal),
	/// Whether an integer is less than a constant.
	IntLess(Decision<IntVal>, IntVal),
	/// Whether an integer is not equal to a constant.
	IntNotEq(Decision<IntVal>, IntVal),
}

impl Resolved<View<bool>> {
	/// Consuming variant of [`BoolPropagationActions::fix`].
	pub(crate) fn fix(
		self,
		ctx: &mut Model,
		val: bool,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		let lit = if val { self.0 } else { !self.0 };
		Resolved(lit).require(ctx, reason)
	}

	/// Consuming variant of [`BoolPropagationActions::require`].
	pub(crate) fn require(
		self,
		ctx: &mut Model,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		match self.0.0 {
			Decision(l) => {
				let def = &mut ctx.bool_vars[l.idx()];
				debug_assert!(def.alias.is_none());
				def.alias = Some(View(Const(!l.is_negated())));
				ctx.bool_events.push(l.var());
			}
			Const(c) => c.require(ctx, reason)?,
			IntEq(iv, val) => iv.resolve_alias(ctx).fix(ctx, val, reason)?,
			IntGreaterEq(iv, val) => iv.resolve_alias(ctx).tighten_min(ctx, val, reason)?,
			IntLess(iv, val) => iv.resolve_alias(ctx).tighten_max(ctx, val - 1, reason)?,
			IntNotEq(iv, val) => iv.resolve_alias(ctx).remove_val(ctx, val, reason)?,
		};
		Ok(())
	}

	/// Consuming variant of [`BoolSimplificationActions::unify`].
	pub(crate) fn unify(
		self,
		ctx: &mut Model,
		other: Resolved<View<bool>>,
	) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		let x = self.0;
		let y = other.0;

		match (x.0, y.0) {
			(x, y) if x == y => Ok(()),
			(Decision(xl), Decision(yl)) if xl.var() == yl.var() => {
				Err(ctx.declare_conflict([x, y]))
			}
			(Const(x), Const(y)) if x != y => Err(ctx.declare_conflict([])),
			(x, Const(b)) | (Const(b), x) => Resolved(View::<bool>(x)).fix(ctx, b, []),
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
				let store = &mut ctx.bool_vars[x.idx()];
				debug_assert_eq!(store.alias, None);
				store.alias = Some(if x.is_negated() { !y } else { y });

				// Move subscriptions from aliased variable to the new primary variable
				let constraints = mem::take(&mut store.constraints);
				match y.0 {
					// Move subscriptions to another Boolean decision
					Decision(lit) => {
						ctx.bool_vars[lit.idx()].constraints.extend(constraints);
					}
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
									let def: &mut Advisor = &mut ctx.advisors[adv.index()];
									def.condition = Some(match y.0 {
										IntEq(_, v) => IntLitMeaning::Eq(v),
										IntGreaterEq(_, v) => IntLitMeaning::GreaterEq(v),
										IntLess(_, v) => IntLitMeaning::Less(v),
										IntNotEq(_, v) => IntLitMeaning::NotEq(v),
										_ => unreachable!(),
									});
									ctx.int_vars[j.idx()]
										.constraints
										.add(ActivationAction::Advise(adv), event);
								}
								me @ ActivationAction::Enqueue(_) => {
									// TODO: This triggers even when the Boolean Condition does not
									// change value
									ctx.int_vars[j.idx()].constraints.add(me, event);
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

				ctx.post_constraint(BoolFormula::Equiv(vec![x, y]));
				Ok(())
			}
		}
	}
}

impl BoolInspectionActions<Model> for Resolved<View<bool>> {
	fn val(&self, _ctx: &Model) -> Option<bool> {
		use BoolView::*;

		match self.0.0 {
			Const(b) => Some(b),
			_ => None,
		}
	}
}

impl Add<IntVal> for View<bool> {
	type Output = View<IntVal>;

	fn add(self, rhs: IntVal) -> Self::Output {
		let me: View<IntVal> = self.into();
		me + rhs
	}
}

impl BoolInspectionActions<Model> for View<bool> {
	fn val(&self, ctx: &Model) -> Option<bool> {
		self.resolve_alias(ctx).val(ctx)
	}
}

impl BoolPropagationActions<Model> for View<bool> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: bool,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(ctx).fix(ctx, val, reason)
	}

	fn require(
		&self,
		ctx: &mut Model,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(ctx).require(ctx, reason)
	}
}

impl BoolSimplificationActions<Model> for View<bool> {
	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Conflict<View<bool>>> {
		let other = other.into().resolve_alias(ctx);
		self.resolve_alias(ctx).unify(ctx, other)
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
