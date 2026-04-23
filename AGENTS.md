# General guidelines

This document captures code conventions for the Huub project.
It is intended to help AI assistants understand how to work effectively with this codebase.

## For humans

LLMs can be very helpful with software engineering.
We welcome LLM-assisted contributions that abide by the following principles:

- **Aim for excellence.**
  For the Huub project, LLMs should be used not as a speed multiplier but a quality multiplier.
  Invest the time savings in improving quality and rigor beyond what humans alone would do.
  Write tests that cover more edge cases. Refactor code to make it easier to understand.
  Tackle the TODOs.
  Do all the tedious things.
  Aim for your code to have zero bugs.
- **Spend time reviewing LLM output.**
  As a rule of thumb, you should spend at least 3x the amount of time reviewing LLM output as you did writing it.
  Think about every line and every design decision.
  Find ways to break code.
- **Your code is your responsibility.**
  Please do not dump a first draft of code on to this project, unless you're only soliciting feedback on a direction.

If your LLM-assisted PR shows signs of not being written with thoughtfulness and care, such as missing cases that human review would have easily caught, Huub's maintainers may decline the PR outright.

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
- Handle all edge cases, including race conditions, signal timing, and platform differences.
- Use the type system to encode correctness constraints.
- Prefer compile-time guarantees over runtime checks where possible.

### Production-grade engineering

- Use type system extensively: newtypes, builder patterns, type states, lifetimes.
- Test comprehensively, including edge cases.
- Pay attention to what facilities already exist for testing, and aim to reuse them.
- Getting the details right is really important!

### Documentation

- Use inline comments to explain "why," not just "what".
- Don't add narrative comments in function bodies.
  Only add a comment if what you're doing is non-obvious or special in some way, or if something needs a deeper "why" explanation.
- Module-level documentation should explain purpose and responsibilities.
- **Always** use periods at the end of code comments.
- **Never** use title case in headings and titles. Always use sentence case.
- Always use the Oxford comma.
- Don't omit articles ("a", "an", "the"). Write "the file has a newer version" not "file has newer version".

## Code style

### Rust edition and formatting

- Use Rust 2024 edition.
- Never import from `super`, instead import from `crate` (e.g. `crate::solver::Decision`).
- Format with `cargo +nightly fmt` (using nightly formatting features).
- Formatting is enforced in CI—always run `cargo +nightly fmt` before committing.
- Formatting uses hard tabs and grouped crate imports as configured in `rustfmt.toml`.
- Items in rust file should be ordered first based on their type, then based on their name, using the following order.
  1. `mod <name>`
  2. `use`
  3. sorted `const`/`static`
  4. sorted `struct`/`enum`/`union`/`type`/`trait`
  5. `fn`
  6. `impl`
  7. `mod <name> { ... }`

### Type system patterns

- **Newtypes** for meaning and encapsulation (e.g., `ConRef`).
- **Builder patterns** for complex construction (e.g., `ModelLinearBuilder`).
- **Type states** encoded in generics when state transitions matter.
- **Lifetimes** used extensively to avoid cloning (e.g., `SolvingContext<'a>`).
- **Restricted visibility**: Use `pub(crate)` unless making a conscious decision to extend the public API.
- **Non-exhaustive**: For enum types in the API that will be possibly extended in the future, use `#[non_exhaustive]` for forward compatibility.

### Lint attributes

- Always use `#[expect(...)]` instead of `#[allow(...)]` for suppressing lints.
  The `expect` attribute will warn if the lint is no longer triggered, helping to keep the codebase clean.

### Running tests

Before proposing a change as complete, run the smallest relevant test target first, and then run the full test suite.
Prefer using `cargo nextest run` over `cargo test` to run unit and integration tests.
For doctests, use `cargo test --doc` (doctests are not supported by nextest).
For benchmarks, use `cargo bench`, but note that all checking of the benchmarks is automatically performed by the integration tests as well and only need to be run to test the performance of the solver.

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

#### The `model` crate/layer

- `Model` is the core data structure that represents the problem to be solved.
- The model layer allows additional simplification, including rewriting constraints and unification of decision variables.
- The model layer aims to be convenient for its users, providing a high-level API for defining decision/optimization problems.
- The model layer does not perform any search and does not find any solutions.
  Instead, a `Model` can be "lowered" to a `Solver`.

#### The `solver` crate/layer

- `Solver` is the core data structure that represents the solver.
- The solver is a performance-oriented layer that performs search and finds solutions.
- At its core, the solver layer manages a Boolean satisfiability solver that performs clause propagation and conflict analysis.

## Dependencies

- All versions managed in root `Cargo.toml` `[workspace.dependencies]`.
- Adding new dependencies should be avoided when possible, especially when they add a lot of transitive dependencies.

### Key dependencies

- **bon**: The creation of *builder* patterns, used to define constraints.
- **clap**: The definition and generation of the command line interface.
- **pindakaas**: To interact with the underlying SAT solvers, and to encode some constraints to clauses.
- **rangelist**: The representation of the domains of integer decision variables.
- **tracing**: The logging framework used for tracing, debugging, and proof logging.

### Commands

```bash
# Run unit/integration tests
cargo nextest run --tests --bins --examples
cargo nextest run --tests --bins --examples --all-features

# Run doctests (nextest doesn't support these)
cargo test --doc

# Format code (REQUIRED before committing)
cargo +nightly fmt --all

# Lint (no warnings are allowed)
cargo clippy --workspace --all-features --all-targets

# Build (with all features)
cargo build --all-targets --all-features

# Build (without additional features)
cargo build -p huub
```

### Terms

- **Decision Variable**: An unknown value for which a valid (and sometimes optimal) value is sought by the solver. Decision variables can be of different types (e.g., `i64` and `bool`). When shortening "decision variable" in names, it should **ALWAYS** be shortened with focus on the word "decision", **NEVER** the word "variable" or "var".
- **Domain**: The set of possible values for a decision variable.
- **Bound(s)**: The least and greatest values of a decision variable's domain. Prefer using `min` and `max` over `lower` and `upper`.
- **Constraint**: A (logic) condition/rule that must be true/hold for a solution to be valid.
- **Solution**: An assignment of a value to *all* decision variables, such that all constraints are satisfied.
- **Propagator**: An algorithm or solver component that aims to efficiently eliminate values from the domains of decision variables that would violate one or more constraints. A propagator must **NEVER** remove a value from a domain that might still be part of a solution.
- **Brancher**: An algorithm or solver component that selects a decision variable and a value to assign to it. Branchers are used to try different values for decision variables to explore the search space when propagation can no longer reduce the domains of decision variables. Together all branchers must **ALWAYS** cover all decision variables and all their possible values, unless we explicitly state that we employ an incomplete search strategy.
