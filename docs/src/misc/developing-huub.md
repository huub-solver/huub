# Developing Huub

This page contains information for developers working on Huub itself, including building, testing, debugging the solver, and understanding its dependencies and inspirations.

## MiniZinc Integration

For local MiniZinc debugging, you can assemble a staging deployment tree under `target/staging` with the current debug and release binaries, the MiniZinc library, generated solver configurations (`huub.msc` and `huub-dev.msc`), and generated completions using the following commands:

```sh
cargo xtask stage
```

This creates symlinks `target/staging/bin/huub` and `target/staging/bin/huub-dev`, pointing at the current release and debug builds (don't forget to trigger `cargo build` or `cargo build --release` before running!), and the associated MiniZinc solver configurations in `huub.msc` and `huub-dev.msc` in `target/staging/share/minizinc/solvers`.

The `huub-dev.msc` solver entry uses the `Huub (dev)` name and the `solutions.huub-dev` identifier so it is easy to distinguish from a release build.

Adding `target/staging/share/minizinc/solvers` to the [`MZN_SOLVER_PATH`](https://docs.minizinc.dev/en/stable/fzn-spec.html#solver-configuration-files) environment variable will allow you to use the two solver configurations as follows:

```sh
minizinc --solver huub [ARGS...]
# or
minizinc --solver huub-dev [ARGS...]
```

### Compiling and Running MiniZinc Models

Alternatively, you can compile a MiniZinc instance and run it using a current build of Huub.

This process can be split into two steps. First, produce the required `.fzn.json` and `.ozn` files using the following command:

```sh
minizinc --solver huub --compile [OTHER FLAGS AND INSTANCE FILES]
```

Then, run the current version of Huub using `cargo` and pipe the result back into MiniZinc to evaluate the output:

```sh
cargo run [BUILD FLAGS] -- [HUUB FLAGS AND FZNJSON FILE] | minizinc --ozn-file [OZN FILE]
```

### Debugging with a Debugger

To attach a debugger directly, you can point it at the latest build in `./target/debug` or `./target/release-with-debug` (created using `cargo build` or `cargo build --profile release-with-debug`) in combination with the `[HUUB FLAGS AND FZNJSON FILE]`.

For example, the following command can be used to run Huub with the `lldb` debugger:

```sh
lldb -- ./target/debug/huub [HUUB FLAGS AND FZNJSON FILE]
```

## Related Projects and Dependencies

### SAT Solver Integration

Huub is built using the IPASIR-UP interface for SAT solvers, proposed by [Fazakas et al.](https://doi.org/10.4230/LIPIcs.SAT.2023.8). Huub is tested with the following solvers that implement this interface:

- [CaDiCaL](https://github.com/arminbiere/cadical)

### Encoding to SAT

The connection to SAT solvers and encoding methods to SAT for Huub use [Pindakaas](https://github.com/pindakaashq/pindakaas), a Rust crate for SAT solving and encoding to SAT.

### Related Solvers

If you're exploring CP+SAT approaches, you might also be interested in:

- [Chuffed](https://github.com/chuffed/chuffed) — A C++ CP+SAT solver with a focus on performance.
- [OR-Tools](https://github.com/google/or-tools) — Google's operations research library with multiple solving paradigms, based around CP+SAT.
- [Pumpkin](https://github.com/ConSol-Lab/Pumpkin/) — Another CP+SAT solver written in Rust.
