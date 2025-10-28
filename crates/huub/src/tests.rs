use expect_test::{expect, Expect};
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::RangeList;
use tracing_test::traced_test;

use crate::{
	actions::{IntInspectionActions, IntSimplificationActions, SimplificationActions},
	branchers::IntBrancher,
	// constraints::int_linear::{IntLinearLessEqBounds, IntLinearNotEqValue},
	solver::{
		int_var::{EncodingType, IntVar},
		SolveResult, Value, View,
	},
	Decision,
	InitConfig,
	Model,
	NonZeroIntVal,
	ReformulationError,
	Solver,
	ValueSelection,
	VariableSelection,
};

#[test]
fn it_works() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	prb += Formula::Or(vec![(!a).into(), (!b).into()]);
	prb += Formula::Or(vec![a.into(), b.into()]);

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
	assert_eq!(x_trans.get_lower_bound(&prb), -11);
	assert_eq!(x_trans.get_upper_bound(&prb), -4);
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
	todo!();
	// IntLinearLessEqBounds::new_in(
	// 	&mut slv,
	// 	[
	// 		a * NonZeroIntVal::new(3).unwrap(),
	// 		b,
	// 		b * NonZeroIntVal::new(2).unwrap(),
	// 	],
	// 	3,
	// );
	// IntLinearNotEqValue::new_in(&mut slv, [a * NonZeroIntVal::new(3).unwrap(),
	// b], 3);
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

	todo!();
	// let lin = (a * 2 - b * 5).eq(0);
	// prb += lin;

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

	todo!();

	// let lin = (a * 6 - b * 2).eq(0);
	// prb += lin;

	let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
	let a = map.get_int(&mut slv, a);
	let b = map.get_int(&mut slv, b);

	let (res, _, solns) = slv.get_all_solutions(&[a.into(), b.into()]);
	assert_eq!(res, SolveResult::Complete);
	assert_eq!(solns, vec![vec![Value::Int(1), Value::Int(3)]]);
}

#[test]
fn test_unify_int_view_for_bool_1() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();
	todo!();
	// prb += (a * 2 + b * -2).eq(0);
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
	todo!();
	// prb += (a * -2 + b * 3).eq(0);
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
	todo!();
	// prb += (a * -2 + b * -3).eq(0);
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
	todo!();
	// prb += (a * 2 + b * 3).eq(0);
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
	todo!();
	// prb += (a * 2 + b * -3).eq(0);
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
	todo!();
	// prb += (((a * 2) + 2) + b * -3).eq(0);
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
		let (status, _, mut solns) = self.get_all_solutions(&vars);
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
