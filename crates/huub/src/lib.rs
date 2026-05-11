//! # Huub - a CP+SAT solver library for better decisions.
//!
//! Huub is an efficient Rust library for developing constraint-based decision
//! and optimization systems with learning capabilities. It combines the
//! modelling strengths of constraint programming (CP) with the learning,
//! conflict analysis, and proof machinery of Boolean satisfiability (SAT)
//! solving.
//!
//! Huub is built for combinatorial problems such as scheduling, rostering,
//! packing, planning, configuration, and MiniZinc workflows. It lets models use
//! high-level decision variables and constraints while still allowing the SAT
//! engine to learn from deductions and failures during search.
//!
//! The solver is designed to be reliable, performant, and extensible. It is
//! well-tested, performs state-of-the-art preprocessing before search begins,
//! combines strong propagation with modern SAT solving techniques, and exposes
//! extension points for custom propagators, branchers, decision variable views,
//! and SAT backends.
//!
//! # Quick start
//!
//! A typical Huub workflow starts by building a [`model::Model`], converting it
//! to a [`solver::Solver`], and querying solution values through the lowered
//! solver views.
//!
//! ```
//! # use huub::{
//! # 	lower::InitConfig,
//! # 	model::Model,
//! # 	solver::{Solver, Status, Valuation},
//! # };
//! let mut model = Model::default();
//! let x = model.new_int_decision(0..=5);
//! let y = model.new_int_decision(0..=5);
//!
//! model.linear(x + y).eq(5).post();
//! model.unique(vec![x, y]).post();
//!
//! let (mut solver, map): (Solver, _) = model.to_solver(&InitConfig::default())?;
//! let x = map.get(&mut solver, x);
//! let y = map.get(&mut solver, y);
//!
//! let mut solution = None;
//! let status = solver
//! 	.solve()
//! 	.on_solution(|sol| {
//! 		solution = Some((x.val(sol), y.val(sol)));
//! 	})
//! 	.satisfy();
//!
//! assert_eq!(status, Status::Satisfied);
//! let (x, y) = solution.unwrap();
//! assert_eq!(x + y, 5);
//! assert_ne!(x, y);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

#![expect(
	clippy::tabs_in_doc_comments,
	reason = "doctest examples use tab-indented code to match rustfmt output",
	// Tracking Issue: https://github.com/rust-lang/rust-clippy/issues/12425
)]

pub mod actions;
pub mod constraints;
pub mod helpers;
pub mod lower;
pub mod model;
pub mod solver;
#[cfg(test)]
pub(crate) mod tests;
pub mod views;

use rangelist::RangeList;

/// Type alias for a disjunction of literals, used for internal type
/// documentation.
type Clause<L> = Vec<L>;

/// Type alias for a conjunction of literals, used for internal type
/// documentation.
type Conjunction<L> = Vec<L>;

/// Type alias for an integer set parameter value.
type IntSet = Set<IntVal>;

/// Type alias for an integer parameter value.
type IntVal = i64;

/// Type alias for an efficient set of values, that is suitable to track
/// decision variable domains.
///
/// This uses [`rangelist::RangeList`] to represent a set of values efficiently,
/// without storing each value individually.
pub type Set<T> = RangeList<T>;
