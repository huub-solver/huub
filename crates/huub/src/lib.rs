pub(crate) mod actions;
pub(crate) mod helpers;
pub(crate) mod model;
pub(crate) mod propagator;
pub(crate) mod solver;
#[cfg(test)]
pub(crate) mod tests;

pub use helpers::linear_transform::LinearTransform;
pub use model::{
	bool::BoolExpr, constraint::Constraint, flatzinc::FlatZincError,
	reformulate::ReformulationError, Model,
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
