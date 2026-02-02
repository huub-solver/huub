//! Definitions for the default integer decision variable view employed in
//! [`Model`].

use std::{
	num::NonZero,
	ops::{Add, Mul, Neg},
};

use pindakaas::solver::Assumptions;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, BoolPropagationActions, IntDecisionActions, IntExplanationActions,
		IntInspectionActions, IntPropagationActions, PropagationActions, ReasoningContext,
	},
	constraints::ReasonBuilder,
	solver::{
		Decision, IntLitMeaning, Solver, View,
		decision::integer::{DirectStorage, OrderStorage},
		view::{DefaultView, boolean::BoolView, private},
	},
	views::{LinearBoolView, LinearView},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
/// The internal representation of [`IntView`].
///
/// Note that this representation is not meant to be exposed to the user.
pub enum IntView {
	/// Constant Integer Value
	Const(IntVal),
	/// Linear View of an Integer Variable
	Linear(LinearView<NonZero<IntVal>, IntVal, Decision<IntVal>>),
	/// Linear View of an Boolean Literal.
	Bool(LinearBoolView<NonZero<IntVal>, IntVal, Decision<bool>>),
}

impl DefaultView for IntVal {
	type View = IntView;
}
impl private::Sealed for IntVal {}

impl View<IntVal> {
	#[doc(hidden)]
	/// Returns an integer that can be used to identify the associated integer
	/// decision variable and whether the int view is a view on another decision
	/// variable.
	pub fn int_reverse_map_info(&self) -> (Option<u32>, bool) {
		match self.0 {
			IntView::Bool { .. } => (None, true),
			IntView::Linear(lin) => (
				Some(lin.var.ident()),
				lin.offset == 0 && lin.scale == NonZero::new(1).unwrap(),
			),
			_ => (None, true),
		}
	}

	#[doc(hidden)]
	/// Return a list of integers that can used to identify the literals that
	/// are associated to an integer view, and the meaning of those literals.
	pub fn lit_reverse_map_info<Sat: Assumptions>(
		&self,
		slv: &Solver<Sat>,
	) -> Vec<(NonZero<i32>, IntLitMeaning)> {
		match self.0 {
			IntView::Linear(lin) => {
				let var = &slv.engine.borrow().state.int_vars[lin.var.idx()];
				let mut lits = Vec::new();

				if let OrderStorage::Eager { storage, .. } = &var.order_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					val_iter.next();
					for (lit, val) in (*storage).zip(val_iter) {
						let i: NonZero<i32> = lit.into();
						let orig = IntLitMeaning::Less(val);
						let lt = lin.transform_meaning(orig);
						let geq = !lt;
						lits.extend([(i, lt), (-i, geq)]);
					}
				}

				if let DirectStorage::Eager(vars) = &var.direct_encoding {
					let mut val_iter = var.domain.clone().into_iter().flatten();
					val_iter.next();
					val_iter.next_back();
					for (lit, val) in (*vars).zip(val_iter) {
						let i: NonZero<i32> = lit.into();
						let orig = IntLitMeaning::Eq(val);
						let eq = lin.transform_meaning(orig);
						let ne = !eq;
						lits.extend([(i, eq), (-i, ne)]);
					}
				}
				lits
			}
			IntView::Bool(lin) => {
				let i: NonZero<i32> = lin.var.0.into();
				let lb = lin.transform_meaning(IntLitMeaning::Eq(0));
				let ub = lin.transform_meaning(IntLitMeaning::Eq(1));
				vec![(i, ub), (-i, lb)]
			}
			_ => Vec::new(),
		}
	}
}

impl Add<IntVal> for View<IntVal> {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		Self(match self.0 {
			IntView::Const(i) => IntView::Const(i + rhs),
			IntView::Linear(lin) => IntView::Linear(lin + rhs),
			IntView::Bool(lin) => IntView::Bool(lin + rhs),
		})
	}
}

impl From<Decision<IntVal>> for View<IntVal> {
	fn from(value: Decision<IntVal>) -> Self {
		Self(IntView::Linear(value.into()))
	}
}

impl From<Decision<bool>> for View<IntVal> {
	fn from(value: Decision<bool>) -> Self {
		Self(IntView::Bool(value.into()))
	}
}

impl From<IntVal> for View<IntVal> {
	fn from(value: IntVal) -> Self {
		Self(IntView::Const(value))
	}
}

impl From<LinearBoolView<NonZero<IntVal>, IntVal, Decision<bool>>> for View<IntVal> {
	fn from(value: LinearBoolView<NonZero<IntVal>, IntVal, Decision<bool>>) -> Self {
		Self(IntView::Bool(value))
	}
}

impl From<LinearView<NonZero<IntVal>, IntVal, Decision<IntVal>>> for View<IntVal> {
	fn from(value: LinearView<NonZero<IntVal>, IntVal, Decision<IntVal>>) -> Self {
		Self(IntView::Linear(value))
	}
}

impl From<View<bool>> for View<IntVal> {
	fn from(value: View<bool>) -> Self {
		Self(match value.0 {
			BoolView::Lit(l) => IntView::Bool(l.into()),
			BoolView::Const(c) => IntView::Const(c as IntVal),
		})
	}
}

impl<Ctx> IntDecisionActions<Ctx> for View<IntVal>
where
	Ctx: ReasoningContext<Atom = View<bool>> + ?Sized,
	Decision<IntVal>: IntDecisionActions<Ctx>,
	Decision<bool>: BoolInspectionActions<Ctx>,
	View<bool>: BoolInspectionActions<Ctx>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		match self.0 {
			IntView::Linear(lin) => lin.lit(ctx, meaning),
			IntView::Const(c) => c.lit(ctx, meaning),
			IntView::Bool(lin) => lin.lit(ctx, meaning),
		}
	}
}

impl<Ctx> IntExplanationActions<Ctx> for View<IntVal>
where
	Ctx: ReasoningContext<Atom = View<bool>> + ?Sized,
	Decision<IntVal>: IntExplanationActions<Ctx>,
	Decision<bool>: BoolInspectionActions<Ctx>,
	View<bool>: BoolInspectionActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (View<bool>, IntLitMeaning) {
		match self.0 {
			IntView::Linear(lin) => lin.lit_relaxed(ctx, meaning),
			IntView::Const(c) => c.lit_relaxed(ctx, meaning),
			IntView::Bool(lin) => lin.lit_relaxed(ctx, meaning),
		}
	}
}

impl<Ctx> IntInspectionActions<Ctx> for View<IntVal>
where
	Ctx: ReasoningContext<Atom = View<bool>> + ?Sized,
	Decision<IntVal>: IntInspectionActions<Ctx>,
	Decision<bool>: BoolInspectionActions<Ctx>,
	View<bool>: BoolInspectionActions<Ctx>,
{
	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		match self.0 {
			IntView::Const(c) => c.bounds(ctx),
			IntView::Linear(lin) => lin.bounds(ctx),
			IntView::Bool(lin) => lin.bounds(ctx),
		}
	}

	fn domain(&self, ctx: &Ctx) -> IntSet {
		match self.0 {
			IntView::Const(c) => c.domain(ctx),
			IntView::Linear(lin) => lin.domain(ctx),
			IntView::Bool(lin) => lin.domain(ctx),
		}
	}

	fn in_domain(&self, ctx: &Ctx, val: IntVal) -> bool {
		match self.0 {
			IntView::Const(c) => c.in_domain(ctx, val),
			IntView::Linear(lin) => lin.in_domain(ctx, val),
			IntView::Bool(lin) => lin.in_domain(ctx, val),
		}
	}

	fn lit_meaning(&self, ctx: &Ctx, lit: View<bool>) -> Option<IntLitMeaning> {
		match self.0 {
			IntView::Linear(lin) => lin.lit_meaning(ctx, lit),
			IntView::Const(c) => c.lit_meaning(ctx, lit),
			IntView::Bool(lin) => lin.lit_meaning(ctx, lit),
		}
	}

	fn max(&self, ctx: &Ctx) -> IntVal {
		match self.0 {
			IntView::Const(c) => c,
			IntView::Linear(lin) => lin.max(ctx),
			IntView::Bool(lin) => lin.max(ctx),
		}
	}

	fn max_lit(&self, ctx: &Ctx) -> View<bool> {
		match self.0 {
			IntView::Linear(lin) => lin.max_lit(ctx),
			IntView::Const(c) => c.max_lit(ctx),
			IntView::Bool(lin) => lin.max_lit(ctx),
		}
	}

	fn min(&self, ctx: &Ctx) -> IntVal {
		match self.0 {
			IntView::Const(c) => c,
			IntView::Linear(lin) => lin.min(ctx),
			IntView::Bool(lin) => lin.min(ctx),
		}
	}

	fn min_lit(&self, ctx: &Ctx) -> View<bool> {
		match self.0 {
			IntView::Linear(lin) => lin.min_lit(ctx),
			IntView::Const(c) => c.min_lit(ctx),
			IntView::Bool(lin) => lin.min_lit(ctx),
		}
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<View<bool>> {
		match self.0 {
			IntView::Linear(lin) => lin.try_lit(ctx, meaning),
			IntView::Const(c) => c.try_lit(ctx, meaning),
			IntView::Bool(lin) => lin.try_lit(ctx, meaning),
		}
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		match self.0 {
			IntView::Const(c) => c.val(ctx),
			IntView::Linear(lin) => lin.val(ctx),
			IntView::Bool(lin) => lin.val(ctx),
		}
	}
}

impl<Ctx> IntPropagationActions<Ctx> for View<IntVal>
where
	Ctx: PropagationActions<Atom = View<bool>> + ?Sized,
	Decision<IntVal>: IntPropagationActions<Ctx>,
	Decision<bool>: BoolPropagationActions<Ctx>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		match self.0 {
			IntView::Linear(lin) => lin.fix(ctx, val, reason),
			IntView::Bool(lin) => lin.fix(ctx, val, reason),
			IntView::Const(c) => c.fix(ctx, val, reason),
		}
	}

	fn remove_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		match self.0 {
			IntView::Linear(lin) => lin.remove_val(ctx, val, reason),
			IntView::Bool(lin) => lin.remove_val(ctx, val, reason),
			IntView::Const(c) => c.remove_val(ctx, val, reason),
		}
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		match self.0 {
			IntView::Linear(lin) => lin.tighten_max(ctx, val, reason),
			IntView::Bool(lin) => lin.tighten_max(ctx, val, reason),
			IntView::Const(c) => c.tighten_max(ctx, val, reason),
		}
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		match self.0 {
			IntView::Linear(lin) => lin.tighten_min(ctx, val, reason),
			IntView::Bool(lin) => lin.tighten_min(ctx, val, reason),
			IntView::Const(c) => c.tighten_min(ctx, val, reason),
		}
	}
}

impl Mul<NonZero<IntVal>> for View<IntVal> {
	type Output = Self;

	fn mul(self, rhs: NonZero<IntVal>) -> Self::Output {
		Self(match self.0 {
			IntView::Const(c) => IntView::Const(c * rhs.get()),
			IntView::Linear(lin) => IntView::Linear(lin * rhs),
			IntView::Bool(lin) => IntView::Bool(lin * rhs),
		})
	}
}

impl Neg for View<IntVal> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		Self(match self.0 {
			IntView::Const(i) => IntView::Const(-i),
			IntView::Linear(lin) => IntView::Linear(-lin),
			IntView::Bool(lin) => IntView::Bool(-lin),
		})
	}
}
