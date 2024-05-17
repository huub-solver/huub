<p align="center">
  <img
    src="https://lh3.googleusercontent.com/d/1AEg8GdoDUlZ5QZZXJkjqrp1BOKlG-312"
    alt="Huub logo"
    height="350px">
</p>

Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and maintainability in addition to speed.
LCG solvers are a class of solvers that can be used to solve decision and optimization problems.
They are characterized by their ability to dynamically add new Boolean variables and clauses to a Boolean Satisfiability (SAT) solver during the search process.
This allows the solver exploit SAT solver's ability to learn from failures during the search process, without having to encode the full problem into Boolean variables and clauses.

## Documentation

[Documentation](https://docs.rs/huub/latest/huub/)

## Installation

Huub can be used either as a [MiniZinc](https://www.minizinc.org/) solver or as a standalone Rust modelling and solving library for decision and optimization problems.

### Installing Huub as a MiniZinc solver

The following command can be used to install the Huub FlatZinc interface, which can be used as a MiniZinc solver.

```bash
cargo install fzn-huub
```

- [crates.io](https://crates.io/crates/fzn-huub)

After installation of the `fzn-huub` executable, a MiniZinc solver configuration file must be added to a directory on the [`MZN_SOLVER_PATH`](https://www.minizinc.org/doc-latest/en/fzn-spec.html#solver-configuration-files).
The following file can serve as a template for the solver configuration file for Huub.

```json
{
  "name": "Huub",
  "version": "0.1.0",
  "id": "one.dekker.huub",
  "inputType": "JSON",
  "executable": "PATH_TO_HUUB_EXECUTABLE",
  "mznlib": "PATH_TO_HUUB_MZNLIB",
  "stdFlags": ["-a", "-i", "-s", "-t", "-v"],
  "extraFlags": []
}
```

Note that `PATH_TO_HUUB_EXECUTABLE` should be replaced with the path to the `fzn-huub` executable and `PATH_TO_HUUB_MZNLIB` should be replaced with the path where the `share/minizinc/huub` folder from this repository is placed.

### Installing Huub as a Rust library

The following command can be used to add Huub as a dependency to your Rust project.

```bash
cargo add huub
```

- [crates.io](https://crates.io/crates/huub)

## Naming

Huub is named after Hubert Dekker, a passionate business administration and accounting teacher who spent his holidays creating the rosters for his school by hand, allowing students to pick any combination of possible subjects.
This solver is dedicated to him in the hope that it allows problems to be solved with the same flexibility and care that he put into his rosters.
The logo of the solver is based on an old caricature of him as a teacher, made to include his features at an older age.

## Authors

- [Jip J. Dekker](https://dekker.one/)
- [Alexey Ignatiev](https://alexeyignatiev.github.io/)
- [Peter J. Stuckey](https://research.monash.edu/en/persons/peter-stuckey)
- [Allen Zhong](https://research.monash.edu/en/persons/allen-zhong)

## Acknowledgements

This research was partially funded by the Australian Government through the Australian Research Council Industrial Transformation Training Centre in Optimization Technologies, Integrated Methodologies, and Applications ([OPTIMA](https://optima.org.au)), Project ID IC200100009.

## Related

Huub is built using the IPASIR-UP interface for SAT solvers, proposed by [Fazakas et al.](https://doi.org/10.4230/LIPIcs.SAT.2023.8).
Huub is tested with the following solvers that implement this interface.

- [CaDiCaL](https://github.com/arminbiere/cadical)

The connection to SAT solvers and encoding methods to SAT for Huub use Pindakaas, a Rust crate for SAT solving and encoding to SAT.

- [Pindakaas](https://github.com/pindakaashq/pindakaas)

Huub is inspired by the following LCG solvers, among others.

- [Chuffed](https://github.com/chuffed/chuffed)
- [OR-Tools](https://github.com/google/or-tools)
