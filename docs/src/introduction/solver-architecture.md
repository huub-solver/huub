# Solver architecture

At a high level, Huub combines:

- modelling infrastructure
- propagation and explanation machinery
- branching and search control
- SAT integration for learning and conflict analysis

The system is organised to keep these responsibilities relatively modular.
