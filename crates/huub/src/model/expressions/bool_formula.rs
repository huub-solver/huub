//! Definitions for Propositional Logic expressions and constraints that can be
//! used in [`Model`].

use pindakaas::{
	Lit as RawLit,
	propositional_logic::{Formula, TseitinEncoder},
};

use crate::{
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, InitActions,
		PropagationActions, ReasoningEngine, SimplificationActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::view::View,
	solver::view::boolean::BoolView,
};

/// Type alias for the type used to represent propositional logic formulas that
/// can be used in [`Model`](crate::model::Model).
pub type BoolFormula = Formula<View<bool>>;

impl<E> Constraint<E> for BoolFormula
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		let mut resolver = |bv: View<bool>| {
			if let Some(b) = bv.val(ctx) {
				return Err(b);
			};
			Ok(bv)
		};
		let result = self.clone().simplify_with(&mut resolver);
		let mut f = match result {
			Ok(f) => f,
			Err(true) => return Ok(SimplificationStatus::Subsumed),
			Err(false) => return Err(ctx.declare_conflict([])),
		};

		let negate = |f: BoolFormula| match f {
			Formula::Atom(x) => Formula::Atom(!x),
			Formula::Not(x) if matches!(*x, Formula::Atom(_)) => {
				let Formula::Atom(x) = *x else { unreachable!() };
				Formula::Atom(x)
			}
			f => Formula::Not(Box::new(f)),
		};

		while let Formula::Not(neg_f) = f {
			f = match *neg_f {
				// Demorgan's Law transformation
				Formula::And(v) => Formula::Or(v.into_iter().map(negate).collect()),
				Formula::Atom(x) => Formula::Atom(!x),
				Formula::IfThenElse { cond, then, els } => Formula::IfThenElse {
					cond,
					then: Box::new(!*then),
					els: Box::new(!*els),
				},
				Formula::Implies(x, y) => {
					// Demorgan's Law transformation
					// ¬(x → y) ≡ ¬(¬x v y) ≡ x ∧ ¬y
					Formula::And(vec![*x, !*y])
				}
				// Double not elimination
				Formula::Not(f) => *f,
				// Demorgan's Law transformation
				Formula::Or(v) => Formula::And(v.into_iter().map(negate).collect()),
				Formula::Equiv(f) => Formula::And(vec![
					Formula::Or(f.iter().map(|f| !(f.clone())).collect()),
					Formula::Or(f),
				]),
				Formula::Xor(f) if f.len() < 2 => unreachable!(),
				Formula::Xor(f) if f.len() == 2 => Formula::Equiv(f),
				Formula::Xor(mut f) => {
					f[0] = negate(f[0].clone());
					Formula::Xor(f)
				}
			};
		}

		*self = match f {
			Formula::And(v) => {
				for f in v {
					match f {
						Formula::Atom(x) => {
							x.require(ctx, [])?;
						}
						Formula::Not(x) if matches!(*x, Formula::Atom(_)) => {
							let Formula::Atom(x) = *x else { unreachable!() };
							x.fix(ctx, false, [])?;
						}
						f => {
							ctx.post_constraint(f);
						}
					}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			Formula::Atom(b) => {
				b.require(ctx, [])?;
				return Ok(SimplificationStatus::Subsumed);
			}
			Formula::Not(_) => unreachable!(),
			f => f,
		};
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let mut resolver = |bv: View<bool>| {
			let inner = slv.solver_view(bv);
			match inner.0 {
				BoolView::Const(b) => Err(b),
				BoolView::Lit(l) => Ok(l.0),
			}
		};
		let result: Result<Formula<RawLit>, _> = self.clone().simplify_with(&mut resolver);
		match result {
			Err(false) => Err(slv.declare_conflict([]).into()),
			Err(true) => Ok(()),
			Ok(f) => slv.cnf_encode(&f, &TseitinEncoder),
		}
	}
}

impl From<View<bool>> for BoolFormula {
	fn from(v: View<bool>) -> Self {
		Self::Atom(v)
	}
}

impl<E> Propagator<E> for BoolFormula
where
	E: ReasoningEngine,
	View<bool>: BoolSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.enqueue_now(true);
		match self {
			Formula::And(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::Atom(a) => a.enqueue_when_fixed(ctx),
			Formula::Equiv(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::IfThenElse { cond, then, els } => {
				cond.initialize(ctx);
				then.initialize(ctx);
				els.initialize(ctx);
			}
			Formula::Implies(f1, f2) => {
				f1.initialize(ctx);
				f2.initialize(ctx);
			}
			Formula::Not(f) => f.initialize(ctx),
			Formula::Or(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
			Formula::Xor(v) => v.iter_mut().for_each(|f| f.initialize(ctx)),
		}
	}

	fn propagate(
		&mut self,
		_: &mut <E as ReasoningEngine>::PropagationCtx<'_>,
	) -> Result<(), <E as ReasoningEngine>::Conflict> {
		unreachable!()
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::propositional_logic::Formula;

	use crate::{
		Model,
		actions::BoolInspectionActions,
		constraints::{Constraint, SimplificationStatus},
		model::expressions::bool_formula::BoolFormula,
	};

	#[test]
	fn simplify_and_formula() {
		use Formula::*;

		// Test case for And with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = And(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for And with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = And(vec![Atom(x), Atom(false.into())]);
		assert!(<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb).is_err());
	}

	#[test]
	fn simplify_equiv_formula() {
		use Formula::*;

		// Test case for Equiv(x, true) -> x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Equiv(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Equiv(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Equiv(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}

	#[test]
	fn simplify_ifthenelse_formula() {
		use Formula::*;

		// Test case for IfThenElse(true, t, e) -> t
		let mut prb = Model::default();
		let t = prb.new_bool_decision();
		let e = prb.new_bool_decision();
		let mut f: BoolFormula = IfThenElse {
			cond: Box::new(Atom(true.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		};
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(t.val(&prb), Some(true));
		assert_eq!(e.val(&prb), None);

		// Test case for IfThenElse(false, t, e) -> e
		let mut prb = Model::default();
		let t = prb.new_bool_decision();
		let e = prb.new_bool_decision();
		let mut f: BoolFormula = IfThenElse {
			cond: Box::new(Atom(false.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		};
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(t.val(&prb), None);
		assert_eq!(e.val(&prb), Some(true));
	}

	#[test]
	fn simplify_implies_formula() {
		use Formula::*;

		// Test case for Implies(true, y) -> y
		let mut prb = Model::default();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Implies(Box::new(Atom(true.into())), Box::new(Atom(y)));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(y.val(&prb), Some(true));

		// Test case for Implies(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Implies(Box::new(Atom(x)), Box::new(Atom(false.into())));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}

	#[test]
	fn simplify_not_formula() {
		use Formula::*;

		// Test case for Not(Not(x))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Not(Box::new(Atom(x)))));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for De Morgan's law with And
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(And(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Or(vec![Atom(!x), Atom(!y)]));

		// Test case for De Morgan's law with Or
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Or(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(Implies)
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Implies(Box::new(Atom(x)), Box::new(Atom(y)))));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(IfThenElse)
		let mut prb = Model::default();
		let c = prb.new_bool_decision();
		let t = prb.new_bool_decision();
		let e = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(IfThenElse {
			cond: Box::new(Atom(c)),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		}));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(
			f,
			IfThenElse {
				cond: Box::new(Atom(c)),
				then: Box::new(Not(Box::new(Atom(t)))),
				els: Box::new(Not(Box::new(Atom(e)))),
			}
		);

		// Test case for Not(Equiv(x,y))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Equiv(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed) // rewritten to two clauses
		);
		assert_eq!(x.val(&prb), None);
		assert_eq!(y.val(&prb), None);

		// Test case for Not(Xor(x, y))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Xor(vec![Atom(x), Atom(y)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Equiv(vec![Atom(x), Atom(y)]));

		// Test case for Not(Xor(x, y, z))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let z = prb.new_bool_decision();
		let mut f: BoolFormula = Not(Box::new(Xor(vec![Atom(x), Atom(y), Atom(z)])));
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f, Xor(vec![Atom(!x), Atom(y), Atom(z)]));
	}

	#[test]
	fn simplify_or_formula() {
		use Formula::*;

		// Test case for Or with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Or(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), None);

		// Test case for Or with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Or(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));
	}

	#[test]
	fn simplify_xor_formula() {
		use Formula::*;

		// Test case for Xor(x, false) -> x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Xor(vec![Atom(x), Atom(false.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Xor(x, true) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f: BoolFormula = Xor(vec![Atom(x), Atom(true.into())]);
		assert_eq!(
			<BoolFormula as Constraint<Model>>::simplify(&mut f, &mut prb),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}
}
