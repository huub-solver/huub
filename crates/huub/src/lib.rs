//! # Huub - A Modular and Maintainable Lazy Clause Generation Solver
//! Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and
//! maintainability in addition to speed. LCG solvers are a class of solvers
//! that can be used to solve decision and optimization problems. They are
//! characterized by their ability to dynamically add new Boolean variables and
//! clauses to a Boolean Satisfiability (SAT) solver during the search process.
//! This allows the solver exploit SAT solver's ability to learn from failures
//! during the search process, without having to encode the full problem into
//! Boolean variables and clauses.

pub mod actions;
pub mod constraints;
pub mod helpers;
pub mod lower;
pub mod model;
pub mod solver;
#[cfg(test)]
pub(crate) mod tests;
pub mod views;

use pindakaas::solver::TermSignal;
use rangelist::RangeList;

use crate::model::Model;

/// Type alias for a disjunction of literals (clause), used for internal type
/// documentation.
type Clause<L> = Vec<L>;

/// Type alias for a conjunction of literals (clause), used for internal type
/// documentation.
type Conjunction<L> = Vec<L>;

/// Type of the optimization objective
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Goal<V> {
	/// Search for a solution that minimizes the given objective.
	Minimize(V),
	/// Search for a solution that maximizes the given objective.
	Maximize(V),
}

/// Type alias for a set of integers parameter value.
type IntSet = Set<IntVal>;

/// Type alias for an parameter integer value.
type IntVal = i64;

/// Type alias for an efficient set of values, that is suitable to track
/// decision variable domains.
///
/// This uses [`rangelist::RangeList`] to represent a set of values efficiently,
/// without storing each value individually.
pub type Set<T> = RangeList<T>;

/// Type alias for a signal given by callbacks to the [`Solver`](solver::Solver)
/// to indicate whether it should terminate.
pub type TerminationSignal = TermSignal;
