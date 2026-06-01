# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
