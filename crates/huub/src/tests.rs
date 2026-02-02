use std::num::NonZero;

use expect_test::{Expect, expect};
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::RangeList;
use tracing_test::traced_test;

use crate::{
	IntVal, Model,
	constraints::int_linear::{IntLinearLessEqBounds, IntLinearNotEqValue},
	lower::{InitConfig, LoweringError},
	model::deserialize::AnyView as ModelView,
	solver::{
		AnyView as SolverView, BoolValuation, IntValuation, Solver, Status, Value,
		branchers::{IntBrancher, ValueSelection, VariableSelection},
		decision::integer::{EncodingType, IntDecision},
	},
};

#[test]
fn it_works() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.proposition(Formula::Or(vec![(!a).into(), (!b).into()]))
		.post();
	prb.proposition(Formula::Or(vec![a.into(), b.into()]))
		.post();

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get(&mut slv, a);
	let b = map.get(&mut slv, b);

	assert_eq!(
		slv.solve(|sol| {
			assert_ne!(a.val(sol), b.val(sol));
		}),
		Status::Satisfied
	);
}

#[test]
/// Test case to check if resolving a multi-step linear alias works properly.
fn lin_multi_alias() {
	use crate::actions::{IntInspectionActions, IntSimplificationActions};

	let mut prb = Model::default();
	let x = prb.new_int_decision(RangeList::from_iter([1..=10]));
	let y = prb.new_int_decision(RangeList::from_iter([1..=10]));
	let z = prb.new_int_decision(RangeList::from_iter([1..=10]));
	let x_trans = x * -1 - 1;
	let y_trans = y + 1;
	let z_trans = z + 1;
	assert!(x.unify(&mut prb, y_trans).is_ok());
	assert!(y.unify(&mut prb, z_trans).is_ok());
	assert_eq!(x_trans.min(&prb), -11);
	assert_eq!(x_trans.max(&prb), -4);
}

#[test]
fn test_bounding_add() {
	use crate::actions::IntInspectionActions;

	let mut prb = Model::default();
	let x = prb.new_int_decision(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_add(&mut prb, 100).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN, IntVal::MAX - 100));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN + 100, IntVal::MAX));
}

#[test]
fn test_bounding_mul() {
	use crate::actions::IntInspectionActions;

	let mut prb = Model::default();
	let x = prb.new_int_decision(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_mul(&mut prb, 2).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN / 2, IntVal::MAX / 2));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN, IntVal::MAX - 1));
}

#[test]
fn test_bounding_neg() {
	use crate::actions::IntInspectionActions;

	let mut prb = Model::default();
	let x = prb.new_int_decision(IntVal::MIN..=IntVal::MAX);

	let y = x.bounding_neg(&mut prb).unwrap();

	// Check underlying domain
	assert_eq!(x.bounds(&prb), (IntVal::MIN + 1, IntVal::MAX));
	// Check view domain
	assert_eq!(y.bounds(&prb), (IntVal::MIN + 1, IntVal::MAX));
}

#[test]
fn test_bounding_sub() {
	use crate::actions::IntInspectionActions;

	let mut prb = Model::default();
	let x = prb.new_int_decision(IntVal::MIN..=IntVal::MAX);

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
	let a = IntDecision::new_in(
		&mut slv,
		RangeList::from(0..=1),
		EncodingType::Eager,
		EncodingType::Lazy,
	);
	let b = IntDecision::new_in(
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
	let a = prb.new_int_decision(1..=5);
	let b = prb.new_int_decision(1..=2);

	prb.linear(a * 2 - b * 5).eq(0).post();

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get(&mut slv, a);
	let b = map.get(&mut slv, b);

	assert_eq!(
		slv.solve(|sol| {
			assert_eq!(a.val(sol), 5);
			assert_eq!(b.val(sol), 2);
		}),
		Status::Satisfied
	);
}

#[test]
fn test_unify_int_lin_view_domains() {
	let mut prb = Model::default();
	let a = prb.new_int_decision(RangeList::from_iter([1..=1, 3..=3, 5..=5]));
	let b = prb.new_int_decision(RangeList::from_iter([1..=3]));

	prb.linear(a * 6 - b * 2).eq(0).post();

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get(&mut slv, a);
	let b = map.get(&mut slv, b);

	let (res, _, solns) = slv.collect_all_solutions(&[a.into(), b.into()]);
	assert_eq!(res, Status::Complete);
	assert_eq!(solns, vec![vec![Value::Int(1), Value::Int(3)]]);
}

#[test]
fn test_unify_int_view_for_bool_1() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(a * 2 + b * -2).eq(0).post();

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
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(a * -2 + b * 3).eq(0).post();

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_3() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(a * -2 + b * -3).eq(0).post();

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_4() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(a * 2 + b * 3).eq(0).post();

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_5() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(a * 2 + b * -3).eq(0).post();

	prb.expect_solutions(
		&[a, b],
		expect![[r#"
		false, false"#]],
	);
}

#[test]
fn test_unify_int_view_for_bool_6() {
	let mut prb = Model::default();
	let a = prb.new_bool_decision();
	let b = prb.new_bool_decision();

	prb.linear(((a * 2) + 2) + b * -3).eq(0).post();

	prb.assert_unsatisfiable();
}

impl Model {
	pub(crate) fn assert_unsatisfiable(&mut self) {
		let err: Result<(Solver, _), _> = self.to_solver(&InitConfig::default());
		assert!(
			matches!(err, Err(LoweringError::Simplification(_))),
			"expected unsatisfiable"
		);
	}

	pub(crate) fn expect_solutions<V: Into<ModelView> + Clone>(
		mut self,
		vars: &[V],
		expected: Expect,
	) {
		let (mut slv, map) = self.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.iter()
			.map(|v| map.get_any(&mut slv, v.clone().into()))
			.collect_vec();
		slv.expect_solutions(&vars, expected);
	}
}

impl Solver {
	pub(crate) fn assert_all_solutions<V: Into<SolverView> + Clone>(
		self,
		vars: &[V],
		pred: impl Fn(&[Value]) -> bool,
	) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let (status, _) = self.all_solutions(&vars, |sol| {
			let mut soln = Vec::with_capacity(vars.len());
			for var in &vars {
				soln.push(var.val(sol));
			}
			assert!(pred(&soln));
		});
		assert_eq!(status, Status::Complete);
	}

	pub(crate) fn assert_unsatisfiable(&mut self) {
		assert_eq!(self.solve(|_| unreachable!()), Status::Unsatisfiable);
	}

	pub(crate) fn expect_solutions<V: Into<SolverView> + Clone>(
		self,
		vars: &[V],
		expected: Expect,
	) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let (status, _, mut solns) = self.collect_all_solutions(&vars);
		assert_eq!(status, Status::Complete);
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
