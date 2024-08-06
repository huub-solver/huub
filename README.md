<p align="center">
  <img
    src="https://dekker.one/_next/static/media/huub.8da5f34e.svg"
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

1. Download the latest release of Huub from the [releases page](https://github.com/Dekker1/huub/releases) and download the `fzn-huub` archive that matches your system.
2. Extract (and install) the downloaded archive to a sensible location on your system.
3. Add the `share/solvers` directory from the extracted archive to the [`MZN_SOLVER_PATH`](https://docs.minizinc.dev/en/stable/fzn-spec.html#solver-configuration-files) environment variable.
4. `Huub` should now show up in the list of solvers when running `minizinc --solvers` and in the MiniZinc IDE.

### Installing Huub as a Rust library

The following command can be used to add Huub as a dependency to your Rust project.

```bash
cargo add huub
```

- [crates.io](https://crates.io/crates/huub)

## Naming

Huub is named after Hubertus Dekker, a passionate business administration and accounting teacher who spent his holidays creating the rosters for his school by hand, allowing students to pick any combination of possible subjects.
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

## Development

When working on the integration of Huub with MiniZinc, you would likely want to compile a MiniZinc instance and run it using a current build of `fzn-huub`.
This process can be split into two steps.
First, the required `.fzn.json` and `.ozn` files can be produced using the following command.

```sh
minizinc --solver share/minizinc/solvers/huub.msc --compile [OTHER FLAGS AND INSTANCE FILES]
```

Then, you can run the current version of `fzn-huub` using `cargo` and pipe the result back into MiniZinc to evaluate the output using the following command.

```sh
cargo run [BUILD FLAGS] -- [HUUB FLAGS AND FZNJSON FILE] | minizinc --ozn-file [OZN FILE]
```

Note that if you are intending to use a debugger on `fzn-huub`, then you would find the latest build in `./target/debug` or `./target/release-with-debug` (created using `cargo build` or `cargo build --profile release-with-debug`) to give to the debugger in combination with the `[HUUB FLAGS AND FZNJSON FILE]`.
For example, the following command can be used to run `fzn-huub` with the `lldb` debugger.

```sh
lldb -- ./target/debug/fzn-huub [HUUB FLAGS AND FZNJSON FILE]
```
