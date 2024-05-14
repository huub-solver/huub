use expect_test::Expect;
use itertools::Itertools;

use crate::{BoolExpr, Model, ReformulationError, SolveResult, Solver, SolverView, Value};

#[test]
fn it_works() {
	let mut prb = Model::default();
	let a = prb.new_bool_var();
	let b = prb.new_bool_var();

	prb += BoolExpr::Or(vec![(!a).into(), (!b).into()]);
	prb += BoolExpr::Or(vec![a.into(), b.into()]);

	let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
	let a = map.get_bool(a);
	let b = map.get_bool(b);

	assert_eq!(
		slv.solve(|value| {
			assert_ne!(value(a.into()), value(b.into()));
		}),
		SolveResult::Satisfied
	);
}

impl Model {
	pub(crate) fn assert_unsatisfiable(&mut self) {
		let err: Result<(Solver, _), _> = self.to_solver();
		assert!(
			matches!(err, Err(ReformulationError::TrivialUnsatisfiable)),
			"expected unsatisfiable"
		);
	}
}

impl Solver {
	pub(crate) fn assert_all_solutions<V: Into<SolverView> + Clone>(
		&mut self,
		vars: &[V],
		pred: impl Fn(&[Value]) -> bool,
	) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let status = self.all_solutions(&vars, |value| {
			let mut soln = Vec::with_capacity(vars.len());
			for var in &vars {
				soln.push(value(*var).unwrap());
			}
			assert!(pred(&soln));
		});
		assert_eq!(status, SolveResult::Complete);
	}

	pub(crate) fn expect_solutions<V: Into<SolverView> + Clone>(
		&mut self,
		vars: &[V],
		expected: Expect,
	) {
		let vars: Vec<_> = vars.iter().map(|v| v.clone().into()).collect();
		let (status, mut solns) = self.get_all_solutions(&vars);
		assert_eq!(status, SolveResult::Complete);
		solns.sort();
		let solns = format!(
			"{}",
			solns.iter().format_with("\n", |sol, f| {
				f(&format_args!(
					"{}",
					sol.iter().format_with(", ", |elt, g| match elt {
						Value::Bool(b) => g(&format_args!("{}", b)),
						Value::Int(i) => g(&format_args!("{}", i)),
					})
				))
			})
		);
		expected.assert_eq(&solns);
	}

	pub(crate) fn assert_unsatisfiable(&mut self) {
		assert_eq!(self.solve(|_| unreachable!()), SolveResult::Unsatisfiable);
	}
}
