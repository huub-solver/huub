use crate::{
	actions::inspection::InspectionActions,
	solver::{
		engine::int_var::IntVarRef,
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, IntView, LitMeaning,
};

pub(crate) trait DecisionActions: InspectionActions {
	fn get_int_lit(&mut self, var: IntView, mut meaning: LitMeaning) -> BoolView {
		{
			if let IntViewInner::Linear { transformer, .. }
			| IntViewInner::Bool { transformer, .. } = var.0
			{
				match transformer.rev_transform_lit(meaning) {
					Ok(m) => meaning = m,
					Err(v) => return BoolView(BoolViewInner::Const(v)),
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
	}

	fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;
}
