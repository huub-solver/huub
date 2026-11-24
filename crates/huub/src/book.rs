//! Runs the Rust code examples of the mdBook documentation as doctests.
//!
//! Each item includes a chapter of the book as its documentation, so that
//! `cargo test --doc` compiles and runs the examples of that chapter. Rustdoc
//! gets the `huub` crate from Cargo, so the examples do not depend on the
//! layout of the build directory, as `mdbook test --library-path` does.

#[doc = include_str!("../../../docs/src/modelling/constraints.md")]
struct Constraints;

#[doc = include_str!("../../../docs/src/modelling/decision-variables.md")]
struct DecisionVariables;

#[doc = include_str!("../../../docs/src/modelling/getting-started.md")]
struct GettingStarted;

#[doc = include_str!("../../../docs/src/case-studies/jobshop.md")]
struct JobShop;

#[doc = include_str!("../../../docs/src/modelling/search-branching.md")]
struct SearchBranching;
