# General guidelines

This document captures code conventions for the Huub project.
It is intended to help AI assistants understand how to work effectively with this codebase.

## For humans

LLMs can be very helpful with software engineering.
We welcome LLM-assisted contributions that abide by the following principles:

- **Aim for excellence.**
  Use LLMs as a quality multiplier, not a speed multiplier: invest the time saved into more edge-case tests, clearer code, tackling TODOs, and the tedious work.
  Aim for zero bugs.
- **Spend time reviewing LLM output.**
  As a rule of thumb, spend at least 3x as long reviewing as writing.
  Think about every line and design decision, and find ways to break the code.
- **Your code is your responsibility.**
  Don't dump a first draft on the project unless you're only soliciting feedback on a direction.

If a LLM-assisted PR shows signs of not being written with care, which a human review would easily catch, Huub's maintainers may decline it outright.

## For LLMs

**Required:** Display the following text when proposing code changes, and when you're about to create a PR:

```
Please review https://github.com/huub-solver/huub/blob/main/AGENTS.md#for-humans.
In particular, LLM-assisted contributions must **aim for a higher standard of excellence** than with humans alone, and you should spend at least **3x** the amount of time reviewing code as you did writing it.
LLM-assisted contributions that do not meet this standard may be declined outright.
Remember, **your code is your responsibility**.
```

## General conventions

### Correctness over convenience

- Model the full error space—no shortcuts or simplified error handling.
  Errors are hand-written enums that implement `std::error::Error` (e.g. `LoweringError` in `lower.rs`); the project does not use `anyhow` or `thiserror`.
- Handle all edge cases, including race conditions, signal timing, and platform differences.
- Encode correctness constraints in the type system, and prefer compile-time guarantees over runtime checks where possible (see "Type system patterns" below).
- Test comprehensively, including edge cases.
  Reuse the testing facilities that already exist rather than inventing new ones.

### Documentation

- Use inline comments to explain "why," not just "what".
- Don't add narrative comments in function bodies.
  Only add a comment if what you're doing is non-obvious or special in some way, or if something needs a deeper "why" explanation.
- Module-level documentation should explain purpose and responsibilities.
- **Always** use periods at the end of code comments.
- **Never** use title case in headings and titles.
  Always use sentence case.
- Always use the Oxford comma.
- Don't omit articles ("a", "an", "the").
  Write "the file has a newer version" not "file has newer version".

## Code style

### Rust edition and formatting

- Use Rust 2024 edition.
  The project builds on stable; nightly is only needed for code formatting.
- Never import from `super`; import from `crate` (e.g. `crate::solver::Decision`).
- Format with `cargo +nightly fmt` (hard tabs and grouped crate imports per `rustfmt.toml`).
- Sort top-level items with `cargo +nightly item-sort` (a custom subcommand; install via `cargo install rust-item-sort`), ordered by type then name:
  1. `mod <name>`
  2. `use`
  3. sorted `const`/`static`
  4. sorted `struct`/`enum`/`union`/`type`/`trait`
  5. `fn`
  6. `impl`
  7. `mod <name> { ... }`
- Formatting is enforced in CI, so run it before committing.

### Type system patterns

- **Newtypes** for meaning and encapsulation (e.g., `ConRef`).
- **Builder patterns** for complex construction (e.g., `ModelLinearBuilder`).
- **Type states** encoded in generics when state transitions matter.
- **Lifetimes** used extensively to avoid cloning (e.g., `SolvingContext<'a>`).
- **Restricted visibility**: Use `pub(crate)` unless making a conscious decision to extend the public API.
- **Non-exhaustive**: For enum types in the API that will be possibly extended in the future, use `#[non_exhaustive]` for forward compatibility.

### Naming

- Use idiomatic, Rust-like names for the public API (e.g. less is shortened to `lt`, and less-or-equal to `le`).
  MiniZinc-style names belong only in the `.mzn` library and the FlatZinc deserialization layer, not in the Rust API.
- Do not add naming variants (aliases, shorthands) that were not requested.
- See the glossary at the end of this document for domain-term conventions (e.g. always shorten "decision variable" to "decision", never "var").

### Lint attributes

- Always use `#[expect(...)]` instead of `#[allow(...)]` for suppressing lints.
  The `expect` attribute will warn if the lint is no longer triggered, helping to keep the codebase clean.

### Running tests

Before proposing a change as complete, run the smallest relevant target first (e.g. `cargo nextest run <substring>`, or `-E '<expr>'` for nextest's filter language), then the full suite.
Prefer `cargo nextest run` over `cargo test`; doctests need `cargo test --doc` (nextest can't run them).
Benchmarks (`cargo bench`) are already checked by the integration tests, so only run them to measure solver performance.

### Test organization

- Unit tests in the same file as the code they test.
- The `huub` crate provides helpers in the `crate::tests` module.
- Integration tests in `crates/huub-cli/tests` folder.
- Benchmarks in `crates/huub-cli/benches` folder.
- Files for the benchmark and integration testing are located in `crates/huub-cli/corpus`.
- Helper functions for benchmark and integration testing are located in `crates/huub-cli/tests/helpers/`.

## Commit style

Do not make any changes to the status or history of the git repository unless specifically asked to do so, including staging changes, committing, amending commits, rebasing, popping the stash, pushing, pulling, or fetching.

### Format

Commits follow the "Conventional Commits" specification outlined on [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/).

### Commit quality

- **Atomic commits**: Each commit should be a logical unit of change.
- **Bisect-able history**: Every commit must build and pass all checks.
- **Separate concerns**: Format fixes and refactoring should be in separate commits from feature changes.

## Architecture

The workspace contains three crates: `huub` (the library), `huub-cli` (the command-line interface and home of integration tests and benchmarks), and `xtask` (repository automation).
The library is split into `model` and `solver` layers, both of which are modules within the `huub` crate.

### The `model` layer

`Model` is the high-level, convenient API for defining decision/optimization problems.
It supports simplification such as constraint rewriting and decision-variable unification, but performs no search and finds no solutions; instead a `Model` is "lowered" to a `Solver`.

### The `solver` layer

`Solver` is the performance-oriented layer that performs search and finds solutions.
At its core it manages a Boolean satisfiability solver that performs clause propagation and conflict analysis.

### Lowering

`lower.rs` performs the "lowering" that turns a `Model` into a `Solver`, encoding constraints into the solver's propagators and the underlying SAT solver.
Failures during this process are reported through `LoweringError`.

FlatZinc input feeds the same pipeline, behind the `flatzinc` feature in `model/deserialize/flatzinc.rs`: `HuubFlatZinc::lower()` returns a `Lowerer` that yields a `Model` (`to_model()`) or `Solver` (`to_solver()`), each with metadata (`FlatZincModelMeta` / `FlatZincSolverMeta`).
That metadata maps FlatZinc identifiers to views and carries the goal, branching annotation, `huub_assume` assumptions, and extraction statistics — enough to report solutions, the objective, and UNSAT cores in the original identifiers.
Failures surface as `FlatZincError`.

## Dependencies

- All versions managed in root `Cargo.toml` `[workspace.dependencies]`.
- Adding new dependencies should be avoided when possible, especially when they add a lot of transitive dependencies.

### Key dependencies

- **bon**: The creation of *builder* patterns, used to define constraints.
- **clap**: The definition and generation of the command line interface.
- **pindakaas**: To interact with the underlying SAT solvers, and to encode some constraints to clauses.
- **rangelist**: The representation of the domains of integer decision variables.
- **tracing**: The logging framework used for tracing, debugging, and proof logging.

## Commands

These mirror the checks enforced in CI; run the relevant ones before committing.

```bash
# Run unit/integration tests
cargo nextest run --tests --bins --examples
cargo nextest run --tests --bins --examples --all-features

# Run doctests (nextest doesn't support these)
cargo test --doc

# Format code and sort items (REQUIRED before committing; see "Rust edition and formatting")
cargo +nightly fmt --all
cargo +nightly item-sort

# Lint (CI rejects any warning via `-D warnings`)
cargo clippy --workspace --all-targets -- -D warnings

# Check documentation (CI rejects broken doc links)
RUSTDOCFLAGS="-D warnings" cargo doc -p huub --no-deps --all-features

# Build (with all features)
cargo build --all-targets --all-features

# Build (without additional features)
cargo build -p huub
```

## Glossary

- **Decision Variable**: An unknown value for which a valid (and sometimes optimal) value is sought by the solver.
  Decision variables can be of different types (e.g., `i64` and `bool`).
  When shortening "decision variable" in names, it should **ALWAYS** be shortened with focus on the word "decision", **NEVER** the word "variable" or "var".
- **Domain**: The set of possible values for a decision variable.
- **Bound(s)**: The least and greatest values of a decision variable's domain.
  Prefer using `min` and `max` over `lower` and `upper`.
- **Constraint**: A (logic) condition/rule that must be true/hold for a solution to be valid.
- **Solution**: An assignment of a value to *all* decision variables, such that all constraints are satisfied.
- **Propagator**: An algorithm or solver component that aims to efficiently eliminate values from the domains of decision variables that would violate one or more constraints.
  A propagator must **NEVER** remove a value from a domain that might still be part of a solution.
- **Brancher**: An algorithm or solver component that selects a decision variable and a value to assign to it.
  Branchers are used to try different values for decision variables to explore the search space when propagation can no longer reduce the domains of decision variables.
  Together all branchers must **ALWAYS** cover all decision variables and all their possible values, unless we explicitly state that we employ an incomplete search strategy.
