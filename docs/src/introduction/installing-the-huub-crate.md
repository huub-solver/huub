# Installing the Huub crate

Huub can be used directly from Rust by adding the `huub` crate to a Cargo project.
This is the recommended route when Huub needs to be integrated into a Rust application, when models are generated programmatically, or when solver components need to be extended.

This section assumes that Rust and Cargo are already installed.
If you are new to Rust projects, start with the official “[First Steps with Cargo](https://doc.rust-lang.org/cargo/getting-started/first-steps.html)” guide.
That guide introduces the `cargo new`, `cargo build`, and `cargo run` workflow used by most Rust projects.

## Adding Huub to a project

The easiest way to add Huub to an existing Cargo project is to use `cargo add`.

```bash
cargo add huub
```

This updates the project's `Cargo.toml` file and adds Huub as a dependency.
The same dependency can also be written manually in `Cargo.toml`.

```toml
[dependencies]
huub = "x.y.z"
```

Use `cargo add` when you want Cargo to choose the current published version for you.
Use the manual `Cargo.toml` form when you want to make the dependency declaration explicit in documentation, examples, or templates.
The version `x.y.z` is not a real version.
When writing the dependency manually, replace it with the current version of Huub from [crates.io](https://crates.io/crates/huub).

Cargo also accepts flags when adding dependencies.
The most important one for Huub is `--features`, which enables optional crate features.

```bash
cargo add --features feature-name huub
```

The equivalent `Cargo.toml` dependency is:

```toml
[dependencies]
huub = { version = "x.y.z", features = ["feature-name"] }
```

The feature name `feature-name` is a placeholder.
Replace it with the feature or features that are needed by your project.
The currently available feature is described below.
After adding the dependency, the project can be checked or built in the usual way.


## Available features

### `flatzinc`

The `flatzinc` feature enables support for constructing Huub objects from FlatZinc JSON produced by MiniZinc.
This is useful when a Rust application wants to reuse the MiniZinc front-end while still working with Huub's Rust API.
If a Rust program builds Huub models directly through the Rust API, the feature is not required.

With this feature enabled, Huub exposes the FlatZinc deserialization module at `huub::model::deserialize::flatzinc`.
That module provides the conversion path from a parsed FlatZinc instance into a `Model`, and from there into a `Solver`.

The two main entry points are:

- `Model::from_fzn`, which creates a `Model` and FlatZinc metadata from a parsed FlatZinc instance.
- `Solver::from_fzn`, which creates a `Solver` and FlatZinc metadata directly from a parsed FlatZinc instance.

The intended workflow is:

1. Write a MiniZinc model.
2. Compile the model using Huub as the MiniZinc solver, so that MiniZinc uses the Huub MiniZinc library.
3. Read the generated FlatZinc JSON in Rust.
4. Use the `flatzinc` feature to construct a Huub `Model` or `Solver`.

For example, the MiniZinc compilation step can be performed with:

```bash
minizinc --solver huub --compile model.mzn data.dzn
```

Huub's MiniZinc solver configuration uses JSON input, so the generated solver input is the format expected by the FlatZinc deserialization path.
Reading a FlatZinc JSON file directly in an application also requires code that parses the JSON into the FlatZinc data structure.
In practice, that usually means depending on `flatzinc-serde` and `serde_json` in the application as well as enabling Huub's `flatzinc` feature.
