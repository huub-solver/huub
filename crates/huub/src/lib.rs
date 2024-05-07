pub(crate) mod model;
pub(crate) mod propagator;
pub(crate) mod solver;

pub use model::{
	bool::BoolExpr, flatzinc::FlatZincError, int::IntExpr, reformulate::ReformulationError,
	Constraint, Model, Variable,
};
pub use pindakaas::solver::SlvTermSignal;
use pindakaas::Lit as RawLit;
pub use solver::{
	engine::int_var::LitMeaning,
	value::{IntVal, NonZeroIntVal, Valuation, Value},
	view::{BoolView, IntView, SolverView},
	Goal, SolveResult, Solver,
};

/// Type alias for a disjunction of literals (clause), used for internal type documentation.
type Clause<L = RawLit> = Vec<L>;
/// Type alias for a conjunction of literals (clause), used for internal type documentation.
type Conjunction<L = RawLit> = Vec<L>;

#[cfg(test)]
mod tests {
	use crate::{BoolExpr, Model, SolveResult, Solver, Variable};

	#[test]
	fn it_works() {
		let mut prb = Model::default();
		let a = prb.new_bool_var();
		let b = prb.new_bool_var();

		prb += BoolExpr::Or(vec![(!a).into(), (!b).into()]);
		prb += BoolExpr::Or(vec![a.into(), b.into()]);

		let (mut slv, map): (Solver, _) = prb.to_solver().unwrap();
		let a = map.get(&Variable::Bool(a));
		let b = map.get(&Variable::Bool(b));

		assert_eq!(
			slv.solve(|value| {
				assert_ne!(value(a), value(b));
			}),
			SolveResult::Satisfied
		);
	}
}
