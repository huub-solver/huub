use crate::{
	actions::inspection::InspectionActions,
	solver::{
		engine::int_var::IntVarRef,
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, IntView, LitMeaning,
};

pub(crate) trait ExplanationActions: InspectionActions {
	fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
	fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;
	fn get_int_lit(&mut self, var: IntView, mut meaning: LitMeaning) -> BoolView {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			if let Some(m) = transformer.rev_transform_lit(meaning) {
				meaning = m;
			} else {
				return BoolView(BoolViewInner::Const(false));
			}
		}

		match var.0 {
			IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
				self.get_intref_lit(var, meaning)
			}
			IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match meaning {
				LitMeaning::Eq(i) => c == i,
				LitMeaning::NotEq(i) => c != i,
				LitMeaning::GreaterEq(i) => c >= i,
				LitMeaning::Less(i) => c < i,
			})),
			IntViewInner::Bool { lit, .. } => {
				let (meaning, negated) =
					if matches!(meaning, LitMeaning::NotEq(_) | LitMeaning::Less(_)) {
						(!meaning, true)
					} else {
						(meaning, false)
					};
				let bv = BoolView(match meaning {
					LitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
					LitMeaning::Eq(1) => BoolViewInner::Lit(lit),
					LitMeaning::Eq(_) => BoolViewInner::Const(false),
					LitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					LitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					LitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					_ => unreachable!(),
				});
				if negated {
					!bv
				} else {
					bv
				}
			}
		}
	}
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		self.get_int_val(var)
			.map(|v| self.get_int_lit(var, LitMeaning::Eq(v)))
	}
	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
}
