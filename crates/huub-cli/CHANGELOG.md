# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [101.0.0](https://github.com/huub-solver/huub/compare/huub-cli-v100.1.0...huub-cli-v101.0.0) - 2026-08-28

### Added

- [**breaking**] add time-table-edge-finding to the cumulative propagator ([#374](https://github.com/huub-solver/huub/pull/374))
- circuit and subcircuit propagators ([#354](https://github.com/huub-solver/huub/pull/354))
- support additional decision and domain selection strategies
- MiniZinc assumption interface for UNSAT core reporting

### Fixed

- [**breaking**] build explanations in place to stop allocation churn

### Other

- resolve cargo clippy issues
- build the reverse map from trace messages
- use `--cadical-` prefix for CaDiCaL specific options

## [100.1.0](https://github.com/huub-solver/huub/compare/huub-cli-v100.0.0...huub-cli-v100.1.0) - 2026-06-01


### Other

- update `huub` to version `100.1.0`
- exclude in-repo-only files from huub-cli package

## [100.0.0](https://github.com/huub-solver/huub/releases/tag/huub-cli-v100.0.0) - 2026-05-14

This is the first Huub release.
The version number 100 honors Hubertus Dekker, namesake of the solver framework, who would have turned 100 this year.
See [huub.solutions](https://huub.solutions) for documentation and more information.
