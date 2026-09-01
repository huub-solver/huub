# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [101.0.0](https://github.com/huub-solver/huub/compare/huub-v100.1.0...huub-v101.0.0) - 2026-09-01

### Added

- [**breaking**] clone propagators through `deepclone` instead of `dyn-clone`
- [**breaking**] allow propagators to update their initialization after posting
- [**breaking**] add time-table-edge-finding to the cumulative propagator ([#374](https://github.com/huub-solver/huub/pull/374))
- circuit and subcircuit propagators ([#354](https://github.com/huub-solver/huub/pull/354))
- add size propagation to no_overlap propagator
- support additional decision and domain selection strategies
- bias search using decision variable polarity
- MiniZinc assumption interface for UNSAT core reporting
- update to CaDiCaL version 3.0.0

### Fixed

- consistency between `Nogood` and `Conflict`
- [**breaking**] build explanations in place to stop allocation churn
- repair stale matchings before Tarjan to avoid value-only SCCs
- invalid non-strict no_overlap propagation where size can be zero
- target and source optimization in no_overlap for non-fixed sizes
- evaluate model integer-comparison bool views against their domain
- emit Fixed event when bound tightening collapses a gapped domain
- resolve linear constraints with no terms at posting time
- sound Hall-set explanation for domain-consistent alldifferent ([#350](https://github.com/huub-solver/huub/pull/350))
- mark flatzinc identifier types as non_exhaustive
- avoid bound-notification assertion when fixing an integer variable
- *(flatzinc)* correct non-strict diffn_k constraint identifier name

### Other

- reformat comment with rust nightly
- resolve cargo clippy issues
- add link to the Huub Discord
- build the reverse map from trace messages
- [**breaking**] reason closures allocate directly on the reason trail
- store eager reasons in a backtrack-truncated trail arena
- bump bon from 3.9.1 to 3.9.3
- add a CLAUDE.md that imports AGENTS.md
- use `--cadical-` prefix for CaDiCaL specific options
- bump rangelist from 0.4.0 to 0.5.0

## [100.1.0](https://github.com/huub-solver/huub/compare/huub-v100.0.0...huub-v100.1.0) - 2026-06-01

### Added

- domain-consistent propagator for IntUnique ([#326](https://github.com/huub-solver/huub/pull/326))

### Fixed

- tighten variable domains when scaling views in `Model::linear`
- upper bound logic in `IntDecision::domain`
- avoid RefCell double-borrow in flatzinc decision unification

## [100.0.0](https://github.com/huub-solver/huub/releases/tag/huub-v100.0.0) - 2026-05-14

This is the first Huub release.
The version number 100 honors Hubertus Dekker, namesake of the solver framework, who would have turned 100 this year.
See [huub.solutions](https://huub.solutions) for documentation and more information.
