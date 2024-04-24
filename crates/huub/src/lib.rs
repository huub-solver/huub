pub(crate) mod model;
pub(crate) mod propagator;
pub(crate) mod solver;

pub use model::{Constraint, Model, Variable};
pub use pindakaas::solver::SolveResult;
pub use solver::{BoolView, IntVal, IntView, LitMeaning, Solver, SolverView, Valuation, Value};

#[cfg(test)]
mod tests {
	use crate::{
		Constraint, Model, SimplifiedBool, SimplifiedVariable, SolveResult, Solver, Variable,
	};

	#[test]
	fn it_works() {
		let mut prb = Model::default();
		let a = prb.new_bool_var();
		let b = prb.new_bool_var();

		prb += Constraint::Clause(vec![(!a).into(), (!b).into()]);
		prb += Constraint::Clause(vec![a.into(), b.into()]);

		let (mut slv, map): (Solver, _) = prb.to_solver();
		let a = map.get(&Variable::Bool(a));
		let b = map.get(&Variable::Bool(b));

		assert_eq!(
			slv.solve(|value| {
				assert_ne!(value(a), value(b));
			}),
			SolveResult::Sat
		);
	}
}
