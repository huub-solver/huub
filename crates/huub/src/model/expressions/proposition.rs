//! Definitions for Propositional Logic expressions and constraints that can be
//! used in [`Model`].

use pindakaas::{
	Lit as RawLit,
	propositional_logic::{Formula, TseitinEncoder},
};

use crate::{
	DeepClone,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, InitActions,
		PropagationActions, ReasoningEngine, SimplificationActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, NO_REASON, Propagator,
		SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::view::View,
	solver::view::boolean::BoolView,
};

/// A [`Proposition`](crate::model::expressions::Proposition) wrapped so that it
/// can be posted as a constraint.
#[derive(Clone, Debug, DeepClone)]
pub struct PropositionConstraint(#[deepclone(clone)] pub(crate) Formula<View<bool>>);

/// Subscribe every atom in `formula` to be notified when it is fixed.
fn subscribe_atoms<E>(formula: &mut Formula<View<bool>>, ctx: &mut E::InitializationContext<'_>)
where
	E: ReasoningEngine,
	View<bool>: BoolSolverActions<E>,
{
	match formula {
		Formula::And(v) => v.iter_mut().for_each(|f| subscribe_atoms::<E>(f, ctx)),
		Formula::Atom(a) => a.enqueue_when_fixed(ctx),
		Formula::Equiv(v) => v.iter_mut().for_each(|f| subscribe_atoms::<E>(f, ctx)),
		Formula::IfThenElse { cond, then, els } => {
			subscribe_atoms::<E>(cond, ctx);
			subscribe_atoms::<E>(then, ctx);
			subscribe_atoms::<E>(els, ctx);
		}
		Formula::Implies(f1, f2) => {
			subscribe_atoms::<E>(f1, ctx);
			subscribe_atoms::<E>(f2, ctx);
		}
		Formula::Not(f) => subscribe_atoms::<E>(f, ctx),
		Formula::Or(v) => v.iter_mut().for_each(|f| subscribe_atoms::<E>(f, ctx)),
		Formula::Xor(v) => v.iter_mut().for_each(|f| subscribe_atoms::<E>(f, ctx)),
	}
}

impl From<View<bool>> for Formula<View<bool>> {
	fn from(v: View<bool>) -> Self {
		Formula::Atom(v)
	}
}

impl<E> Constraint<E> for PropositionConstraint
where
	E: ReasoningEngine,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		let mut resolver = |bv: View<bool>| {
			if let Some(b) = bv.val(ctx) {
				return Err(b);
			};
			Ok(bv)
		};
		let result = self.0.clone().simplify_with(&mut resolver);
		let mut f = match result {
			Ok(f) => f,
			Err(true) => return Ok(SimplificationStatus::Subsumed),
			Err(false) => return Err(ctx.declare_conflict(NO_REASON)),
		};

		let negate = |f: Formula<View<bool>>| match f {
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

		self.0 = match f {
			Formula::And(v) => {
				for f in v {
					match f {
						Formula::Atom(x) => {
							x.require(ctx, NO_REASON)?;
						}
						Formula::Not(x) if matches!(*x, Formula::Atom(_)) => {
							let Formula::Atom(x) = *x else { unreachable!() };
							x.fix(ctx, false, NO_REASON)?;
						}
						f => {
							ctx.post_constraint(PropositionConstraint(f));
						}
					}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			Formula::Atom(b) => {
				b.require(ctx, NO_REASON)?;
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
		let result: Result<Formula<RawLit>, _> = self.0.clone().simplify_with(&mut resolver);
		match result {
			Err(false) => Err(slv.declare_conflict(NO_REASON).into()),
			Err(true) => Ok(()),
			Ok(f) => slv.cnf_encode(&f, &TseitinEncoder),
		}
	}
}

impl From<Formula<View<bool>>> for PropositionConstraint {
	fn from(f: Formula<View<bool>>) -> Self {
		PropositionConstraint(f)
	}
}

impl From<View<bool>> for PropositionConstraint {
	fn from(v: View<bool>) -> Self {
		PropositionConstraint(Formula::Atom(v))
	}
}

impl<E> Propagator<E> for PropositionConstraint
where
	E: ReasoningEngine,
	View<bool>: BoolSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.enqueue_now(true);
		subscribe_atoms::<E>(&mut self.0, ctx);
	}

	fn propagate(
		&mut self,
		_: &mut <E as ReasoningEngine>::PropagationContext<'_>,
	) -> Result<(), <E as ReasoningEngine>::Conflict> {
		unreachable!()
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::propositional_logic::Formula;

	use crate::{
		actions::BoolInspectionActions,
		constraints::{Constraint, SimplificationStatus},
		model::{Model, SimplificationContext, expressions::proposition::PropositionConstraint},
	};

	#[test]
	fn simplify_and_formula() {
		use Formula::*;

		// Test case for And with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(And(vec![Atom(x), Atom(true.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for And with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(And(vec![Atom(x), Atom(false.into())]));
		assert!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			)
			.is_err()
		);
	}

	#[test]
	fn simplify_equiv_formula() {
		use Formula::*;

		// Test case for Equiv(x, true) -> x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Equiv(vec![Atom(x), Atom(true.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Equiv(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Equiv(vec![Atom(x), Atom(false.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
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
		let mut f = PropositionConstraint(IfThenElse {
			cond: Box::new(Atom(true.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		});
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(t.val(&prb), Some(true));
		assert_eq!(e.val(&prb), None);

		// Test case for IfThenElse(false, t, e) -> e
		let mut prb = Model::default();
		let t = prb.new_bool_decision();
		let e = prb.new_bool_decision();
		let mut f = PropositionConstraint(IfThenElse {
			cond: Box::new(Atom(false.into())),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		});
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
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
		let mut f = PropositionConstraint(Implies(Box::new(Atom(true.into())), Box::new(Atom(y))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(y.val(&prb), Some(true));

		// Test case for Implies(x, false) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Implies(Box::new(Atom(x)), Box::new(Atom(false.into()))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
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
		let mut f = PropositionConstraint(Not(Box::new(Not(Box::new(Atom(x))))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for De Morgan's law with And
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f = PropositionConstraint(Not(Box::new(And(vec![Atom(x), Atom(y)]))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f.0, Or(vec![Atom(!x), Atom(!y)]));

		// Test case for De Morgan's law with Or
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f = PropositionConstraint(Not(Box::new(Or(vec![Atom(x), Atom(y)]))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(Implies)
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f =
			PropositionConstraint(Not(Box::new(Implies(Box::new(Atom(x)), Box::new(Atom(y))))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));
		assert_eq!(y.val(&prb), Some(false));

		// Test case for Not(IfThenElse)
		let mut prb = Model::default();
		let c = prb.new_bool_decision();
		let t = prb.new_bool_decision();
		let e = prb.new_bool_decision();
		let mut f = PropositionConstraint(Not(Box::new(IfThenElse {
			cond: Box::new(Atom(c)),
			then: Box::new(Atom(t)),
			els: Box::new(Atom(e)),
		})));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(
			f.0,
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
		let mut f = PropositionConstraint(Not(Box::new(Equiv(vec![Atom(x), Atom(y)]))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed) // rewritten to two clauses
		);
		assert_eq!(x.val(&prb), None);
		assert_eq!(y.val(&prb), None);

		// Test case for Not(Xor(x, y))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let mut f = PropositionConstraint(Not(Box::new(Xor(vec![Atom(x), Atom(y)]))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f.0, Equiv(vec![Atom(x), Atom(y)]));

		// Test case for Not(Xor(x, y, z))
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let y = prb.new_bool_decision();
		let z = prb.new_bool_decision();
		let mut f = PropositionConstraint(Not(Box::new(Xor(vec![Atom(x), Atom(y), Atom(z)]))));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::NoFixpoint)
		);
		assert_eq!(f.0, Xor(vec![Atom(!x), Atom(y), Atom(z)]));
	}

	#[test]
	fn simplify_or_formula() {
		use Formula::*;

		// Test case for Or with a true literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Or(vec![Atom(x), Atom(true.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), None);

		// Test case for Or with a false literal
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Or(vec![Atom(x), Atom(false.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
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
		let mut f = PropositionConstraint(Xor(vec![Atom(x), Atom(false.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(true));

		// Test case for Xor(x, true) -> !x
		let mut prb = Model::default();
		let x = prb.new_bool_decision();
		let mut f = PropositionConstraint(Xor(vec![Atom(x), Atom(true.into())]));
		assert_eq!(
			<PropositionConstraint as Constraint<Model>>::simplify(
				&mut f,
				&mut SimplificationContext(&mut prb)
			),
			Ok(SimplificationStatus::Subsumed)
		);
		assert_eq!(x.val(&prb), Some(false));
	}
}
