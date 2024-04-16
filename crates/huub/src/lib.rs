pub(crate) mod model;
pub(crate) mod propagator;
pub(crate) mod solver;

pub use model::{
	BoolExpr, BoolVar, Constraint, Literal, Model, SimplifiedBool, SimplifiedInt,
	SimplifiedVariable, Variable, VariableMap,
};
pub use pindakaas::solver::SolveResult;
pub use solver::{BoolView, IntView, LitMeaning, Solver, Valuation, Value};

#[cfg(test)]
mod tests {

	use super::*;

	#[test]
	fn it_works() {
		let mut prb = Model::default();
		let a = prb.new_bool_var();
		let b = prb.new_bool_var();

		prb += Constraint::Clause(vec![(!a).into(), (!b).into()]);
		prb += Constraint::Clause(vec![a.into(), b.into()]);

		let (mut slv, map): (Solver, _) = prb.to_solver();
		let SimplifiedVariable::Bool(SimplifiedBool::Lit(a)) = map.get(&Variable::Bool(a)) else {
			unreachable!()
		};
		let SimplifiedVariable::Bool(SimplifiedBool::Lit(b)) = map.get(&Variable::Bool(b)) else {
			unreachable!()
		};

		assert_eq!(
			slv.solve(|value| {
				assert_ne!(value(a.into()), value(b.into()));
			}),
			SolveResult::Sat
		);
	}
}
