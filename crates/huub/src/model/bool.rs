//! Representation and manipulation of Boolean decision variable and expressions
//! in [`Model`].

use std::ops::Not;

use pindakaas::{
	propositional_logic::{Formula, TseitinEncoder},
	ClauseDatabaseTools, Encoder, Lit as RawLit,
};

use crate::{
	actions::{ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	model::{int::IntVar, reformulate::ReformulationError},
	solver::view::BoolViewInner,
	IntVal,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
/// A Boolean expression that is represented using a literal or a constaint in
/// the oracle SAT solver.
pub enum BoolView {
	/// A Boolean decision variable or its negation.
	Lit(RawLit),
	/// A constant Boolean value.
	Const(bool),
	/// Wether an integer is equal to a constant.
	IntEq(IntVar, IntVal),
	/// Wether an integer is greater or equal to a constant.
	IntGreaterEq(IntVar, IntVal),
	/// Wether an integer is less than a constant.
	IntLess(IntVar, IntVal),
	/// Wether an integer is not equal to a constant.
	IntNotEq(IntVar, IntVal),
}

impl<S: SimplificationActions> Constraint<S> for Formula<BoolView> {
	fn simplify(&mut self, _: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let mut resolver = |bv: BoolView| {
			let inner = slv.get_solver_bool(bv);
			match inner.0 {
				BoolViewInner::Const(b) => Err(b),
				BoolViewInner::Lit(l) => Ok(l),
			}
		};
		let result: Result<Formula<RawLit>, _> = self.clone().simplify_with(&mut resolver);
		match result {
			Err(false) => Err(ReformulationError::TrivialUnsatisfiable),
			Err(true) => Ok(()),
			Ok(f) => {
				let mut wrapper = slv.with_conditions(vec![]);
				Ok(TseitinEncoder.encode(&mut wrapper, &f)?)
			}
		}
	}
}

impl From<BoolView> for Formula<BoolView> {
	fn from(v: BoolView) -> Self {
		Self::Atom(v)
	}
}

impl From<bool> for BoolView {
	fn from(v: bool) -> Self {
		BoolView::Const(v)
	}
}

impl Not for BoolView {
	type Output = BoolView;

	fn not(self) -> Self::Output {
		match self {
			BoolView::Lit(l) => BoolView::Lit(!l),
			BoolView::Const(b) => BoolView::Const(!b),
			BoolView::IntEq(v, i) => BoolView::IntNotEq(v, i),
			BoolView::IntGreaterEq(v, i) => BoolView::IntLess(v, i),
			BoolView::IntLess(v, i) => BoolView::IntGreaterEq(v, i),
			BoolView::IntNotEq(v, i) => BoolView::IntEq(v, i),
		}
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;

	use crate::{InitConfig, Model, Solver};
	use pindakaas::propositional_logic::Formula;

	#[test]
	fn test_bool_and() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::And(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(&vars, expect!["true, true, true"]);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::And(b.iter().cloned().map_into().collect());
		m += Formula::from(!b[0]);
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();

		// Regression test case: empty and
		let mut m = Model::default();
		let b = m.new_bool_var();

		m += Formula::Equiv(vec![
			b.into(),
			Formula::And(vec![
				Formula::Atom(true.into()),
				Formula::Atom(true.into()),
				Formula::Atom(true.into()),
			]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![map.get(&mut slv, &b.into())];
		slv.expect_solutions(&vars, expect!["true"]);
	}

	#[test]
	fn test_bool_and_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Equiv(vec![
			b[0].into(),
			Formula::And(vec![b[1].into(), b[2].into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, false
		false, false, true
		false, true, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_clause_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Equiv(vec![
			b[0].into(),
			Formula::Or(vec![b[1].into(), b[2].into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, false
		true, false, true
		true, true, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_eq_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Equiv(vec![
			b[0].into(),
			Formula::Equiv(vec![b[1].into(), b[2].into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, true
		false, true, false
		true, false, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_not() {
		// Satisfiable test case that rewrites the expression
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += Formula::Not(Box::new(Formula::Xor(
			b.iter().copied().map_into().collect(),
		)));
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    false, false
    true, true"#]],
		);

		// Simple Satisfiable test case that reifies the test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Not(Box::new(Formula::Equiv(
			b.iter().copied().map_into().collect(),
		)));
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    false, false, true
    false, true, false
    false, true, true
    true, false, false
    true, false, true
    true, true, false"#]],
		);
	}

	#[test]
	fn test_bool_or() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Or(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, true
		false, true, false
		false, true, true
		true, false, false
		true, false, true
		true, true, false
		true, true, true"#]],
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Or(b.iter().cloned().map_into().collect());
		m += Formula::And(b.iter().cloned().map(|l| (!l).into()).collect());
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();

		// Regression test case: empty or
		let mut m = Model::default();
		let b = m.new_bool_var();

		m += Formula::Equiv(vec![
			b.into(),
			Formula::Or(vec![
				Formula::Atom(false.into()),
				Formula::Atom(false.into()),
				Formula::Atom(false.into()),
			]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![map.get(&mut slv, &b.into())];
		slv.expect_solutions(&vars, expect!["false"]);
	}

	#[test]
	fn test_bool_xor() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += Formula::Xor(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
				false, false, true
				false, true, false
				true, false, false
				true, true, true"#]],
		);

		// Regression test case
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += Formula::Equiv(vec![
			b[1].into(),
			Formula::Xor(vec![Formula::Atom(true.into()), b[0].into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
				false, true
				true, false"#]],
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += Formula::Xor(b.iter().cloned().map_into().collect());
		m += Formula::from(!b[0]);
		m += Formula::from(!b[1]);
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();
	}
}
