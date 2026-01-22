use std::num::NonZero;

use expect_test::{Expect, expect};
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::RangeList;
use tracing_test::traced_test;

use crate::{
	Decision, InitConfig, IntVal, Model, ReformulationError, Solver, ValueSelection,
	VariableSelection,
	actions::{IntInspectionActions, IntSimplificationActions},
	branchers::IntBrancher,
	constraints::int_linear::{IntLinearLessEqBounds, IntLinearNotEqValue},
	solver::{
		SolveResult, Value, View,
		int_var::{EncodingType, IntVar},
	},
};

#[test]
fn it_works() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	prb.add_constraint(Formula::Or(vec![(!a).into(), (!b).into()]));
	prb.add_constraint(Formula::Or(vec![a.into(), b.into()]));

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get_bool(&mut slv, a);
	let b = map.get_bool(&mut slv, b);

	assert_eq!(
		slv.solve(|value| {
			assert_ne!(value(a.into()), value(b.into()));
		}),
		SolveResult::Satisfied
	);
}

#[test]
/// Test case to check if resolving a multi-step linear alias works properly.
fn lin_multi_alias() {
	let mut prb = Model::default();
	let x = prb.new_int_var(RangeList::from_iter([1..=10]));
	let y = prb.new_int_var(RangeList::from_iter([1..=10]));
	let z = prb.new_int_var(RangeList::from_iter([1..=10]));
	let x_trans = x * -1 - 1;
	let y_trans = y + 1;
	let z_trans = z + 1;
	assert!(x.unify(&mut prb, y_trans).is_ok());
	assert!(y.unify(&mut prb, z_trans).is_ok());
	assert_eq!(x_trans.lower_bound(&prb), -11);
	assert_eq!(x_trans.upper_bound(&prb), -4);
}

#[test]
fn test_bounding_add() {
	let mut prb = Model::default();
	let x = prb.new_int_var(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_add(&mut prb, 100).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN, IntVal::MAX - 100));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN + 100, IntVal::MAX));
}

#[test]
fn test_bounding_mul() {
	let mut prb = Model::default();
	let x = prb.new_int_var(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_mul(&mut prb, 2).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN / 2, IntVal::MAX / 2));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN, IntVal::MAX - 1));
}

#[test]
fn test_bounding_neg() {
	let mut prb = Model::default();
	let x = prb.new_int_var(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_neg(&mut prb).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN + 1, IntVal::MAX));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN + 1, IntVal::MAX));
}

#[test]
fn test_bounding_sub() {
	let mut prb = Model::default();
	let x = prb.new_int_var(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_sub(&mut prb, 255).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN + 255, IntVal::MAX));

	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN, IntVal::MAX - 255));
}

#[test]
/// Tests for when a propagator propagates the same literal twice within the
/// same call.
fn test_duplicate_propagation() {
	let mut slv = Solver::default();
	let a = IntVar::new_in(
		&mut slv,
		RangeList::from(0..=1),
		EncodingType::Eager,
		EncodingType::Lazy,
	);
	let b = IntVar::new_in(
		&mut slv,
		RangeList::from(0..=1),
		EncodingType::Eager,
		EncodingType::Lazy,
	);
	IntLinearLessEqBounds::post(
		&mut slv,
		[
			a * NonZero::new(3).unwrap(),
			b,
			b * NonZero::new(2).unwrap(),
		],
		3,
	);
	IntLinearNotEqValue::post(&mut slv, [a * NonZero::new(3).unwrap(), b], 3);
	IntBrancher::new_in(
		&mut slv,
		vec![a, b],
		VariableSelection::InputOrder,
		ValueSelection::IndomainMax,
	);
	slv.expect_solutions(
		&[a, b],
		expect![[r#"
    0, 0
    0, 1"#]],
	);
}

#[traced_test]
#[test]
fn test_unify_int_impossible() {
	let mut prb = Model::default();
	let a = prb.new_int_var(1..=5);
	let b = prb.new_int_var(1..=2);

	rel!(&mut prb, 0 == a * 2 - b * 5);

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get_int(&mut slv, a);
	let b = map.get_int(&mut slv, b);

	assert_eq!(
		slv.solve(|value| {
			assert_eq!(value(a.into()), Value::Int(5));
			assert_eq!(value(b.into()), Value::Int(2));
		}),
		SolveResult::Satisfied
	);
}

#[test]
fn test_unify_int_lin_view_domains() {
	let mut prb = Model::default();
	let a = prb.new_int_var(RangeList::from_iter([1..=1, 3..=3, 5..=5]));
	let b = prb.new_int_var(RangeList::from_iter([1..=3]));

	rel!(&mut prb, 0 == a * 6 - b * 2);

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get_int(&mut slv, a);
	let b = map.get_int(&mut slv, b);

	let (res, _, solns) = slv.collect_all_solutions(&[a.into(), b.into()]);
	assert_eq!(res, SolveResult::Complete);
	assert_eq!(solns, vec![vec![Value::Int(1), Value::Int(3)]]);
}

#[test]
fn test_unify_int_view_for_bool_1() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == a * 2 + b * -2);

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false
		true, true"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_2() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == a * -2 + b * 3);

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_3() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == a * -2 + b * -3);

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_4() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == a * 2 + b * 3);

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_5() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == a * 2 + b * -3);

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_6() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	rel!(&mut prb, 0 == ((a * 2) + 2) + b * -3);

	prb.assert_unsatisfiable();
}

impl Model {
	pub(crate) fn assert_unsatisfiable(&mut self) {
		let err: Result<(Solver, _), _> = self.to_solver(&InitConfig::default());
		assert!(
			matches!(err, Err(ReformulationError::SimplificationConflict(_))),
			"expected unsatisfiable"
		);
	}

	pub(crate) fn expect_solutions<V: Into<Decision> + Clone>(
		mut self,
		vars: &[V],
		expected: Expect,
	) {
		let (mut slv, map) = self.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.iter()
			.map(|v| map.get(&mut slv, &v.clone().into()))
			.collect_vec();
		slv.expect_solutions(&vars, expected);
	}
}

impl Solver {
	pub(crate) fn assert_all_solutions<V: Into<View> + Clone>(
		self,
		vars: &[V],
		pred: impl Fn(&[Value]) -> bool,
	) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let (status, _) = self.all_solutions(&vars, |value| {
			let mut soln = Vec::with_capacity(vars.len());
			for var in &vars {
				soln.push(value(*var));
			}
			assert!(pred(&soln));
		});
		assert_eq!(status, SolveResult::Complete);
	}

	pub(crate) fn assert_unsatisfiable(&mut self) {
		assert_eq!(self.solve(|_| unreachable!()), SolveResult::Unsatisfiable);
	}

	pub(crate) fn expect_solutions<V: Into<View> + Clone>(self, vars: &[V], expected: Expect) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let (status, _, mut solns) = self.collect_all_solutions(&vars);
		assert_eq!(status, SolveResult::Complete);
		solns.sort();
		let solns = format!(
			"{}",
			solns.iter().format_with("\n", |sol, f| {
				f(&format_args!(
					"{}",
					sol.iter().format_with(", ", |elt, g| match elt {
						Value::Bool(b) => g(&format_args!("{b}")),
						Value::Int(i) => g(&format_args!("{i}")),
					})
				))
			})
		);
		expected.assert_eq(&solns);
	}
}
