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
		IntInspectionActions, IntPropagationActions, PropagationActions,
	},
	constraints::{Conflict, ReasonBuilder},
	model::{
		AdvRef, Advisor, ConRef, Model,
		decision::Decision,
		expressions::BoolFormula,
		view::{DefaultView, View, private},
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, IntPropCond},
	},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
#[non_exhaustive]
/// Inner storage for [`BoolDecision`], kept private to prevent access from
/// users.
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

impl View<bool> {
	/// Resolve any aliasing in the BoolDecision, ensuring the result is a
	/// BoolDecision that if it is a `Lit`, then it is not an alias.
	pub(crate) fn resolve_alias(self, model: &Model) -> Self {
		use BoolView::*;

		let mut result = self;
		// If the current Lit is an alias, then resolve it.
		while let Decision(lit) = result.0 {
			if let Some(alias) = model.bool_vars[lit.idx()].alias {
				debug_assert_ne!(alias, result);
				debug_assert_ne!(alias, !result);
				result = if lit.is_negated() { !alias } else { alias };
			} else {
				break;
			}
		}
		// If the current Lit is a integer view, check whether it is already fixed.
		match result.0 {
			IntEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return false.into();
				} else if val == lb && val == ub {
					return true.into();
				}
			}
			IntGreaterEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if lb >= val {
					return true.into();
				} else if ub < val {
					return false.into();
				}
			}
			IntLess(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if ub < val {
					return true.into();
				} else if lb >= val {
					return false.into();
				}
			}
			IntNotEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return true.into();
				} else if val == lb && val == ub {
					return false.into();
				}
			}
			_ => {}
		}
		result
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
		use BoolView::*;

		let b = self.resolve_alias(ctx);
		match b.0 {
			Const(b) => Some(b),
			_ => None,
		}
	}
}

impl BoolPropagationActions<Model> for View<bool> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: bool,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		let lit = if val { *self } else { !*self };
		lit.require(ctx, reason)
	}

	fn require(
		&self,
		ctx: &mut Model,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		let var = self.resolve_alias(ctx);
		match var.0 {
			Decision(l) => {
				let def = &mut ctx.bool_vars[l.idx()];
				debug_assert!(def.alias.is_none());
				def.alias = Some(View(Const(!l.is_negated())));
				ctx.bool_events.push(l.var());
				Ok(())
			}
			Const(c) => c.require(ctx, reason),
			IntEq(iv, val) => iv.fix(ctx, val, reason),
			IntGreaterEq(iv, val) => iv.tighten_min(ctx, val, reason),
			IntLess(iv, val) => iv.tighten_max(ctx, val - 1, reason),
			IntNotEq(iv, val) => iv.remove_val(ctx, val, reason),
		}
	}
}

impl BoolSimplificationActions<Model> for View<bool> {
	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Conflict<View<bool>>> {
		use BoolView::*;

		let x = self.resolve_alias(ctx);
		let y = other.into().resolve_alias(ctx);

		match (x.0, y.0) {
			(x, y) if x == y => Ok(()),
			(Decision(xl), Decision(yl)) if xl.var() == yl.var() => {
				Err(ctx.declare_conflict([x, y]))
			}
			(Const(x), Const(y)) if x != y => Err(ctx.declare_conflict([])),
			(x, Const(b)) | (Const(b), x) => View::<bool>(x).fix(ctx, b, []),
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

impl From<Decision<bool>> for View<bool> {
	fn from(decision: Decision<bool>) -> Self {
		View(BoolView::Decision(decision))
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
