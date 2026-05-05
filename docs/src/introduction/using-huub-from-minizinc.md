# Using Huub from MiniZinc

For many users, the easiest way to use Huub is through [MiniZinc](https://www.minizinc.org/).
In this workflow, MiniZinc is used as the modelling language and Huub is used as the backend solver.
You write a MiniZinc model, MiniZinc compiles it with given instance data, and MiniZinc instructs Huub to solve it.

This chapter has two purposes.
First, it explains how to install Huub as a MiniZinc solver.
Second, it introduces the Huub-specific functionality that is exposed through the MiniZinc library shipped with Huub.

## Installing Huub as a MiniZinc solver

Huub releases contain both the solver executable and the MiniZinc integration files needed to make Huub available to MiniZinc.
In particular, the release archive contains a MiniZinc solver configuration and the Huub MiniZinc library files.

To install Huub as a MiniZinc solver, perform the following steps.

1. Download a Huub release for your platform from the [GitHub releases page](https://github.com/huub-solver/huub/releases).
2. Extract the archive to a suitable location on your system.
  The structure of the archive follows the [conventional Unix directory layout](https://en.wikipedia.org/wiki/Unix_filesystem).
3. Ensure the `share/minizinc/solvers/` directory from the extracted archive is on the standard solver path or add it to the [`MZN_SOLVER_PATH`](https://docs.minizinc.dev/en/stable/fzn-spec.html#solver-configuration-files) environment variable.
4. Verify the installation by running `minizinc --solvers`.

If the installation was successful, `Huub` should appear in the list of available solvers.
It should then also be available from the MiniZinc IDE.

Once this is configured, Huub can be selected in the same way as any other MiniZinc solver.
For example, from the command line a model can be solved using the following command.

```sh
minizinc --solver huub model.mzn data.dzn
```

You can use the following command to inspect the available command line flag for Huub.

```sh
huub --help
```

Alternatively, you can inspect them through MiniZinc as follows.

```sh
minizinc --help huub
```

## Huub-specific MiniZinc functionality

In the Huub MiniZinc library, used to compile MiniZinc instances to Huub specific FlatZinc, we include an additional user-facing `huub.mzn` file.
This file contains the MiniZinc definitions to expose Huub-specific functionality in models.
When selecting the Huub solver and using the Huub solver configuration file, the `huub.mzn` library file can be included simply as follows.

```mzn
include "huub.mzn";

% [Huub-specific usage]
```

We will now outline the different exposed functionality.

### Disjunctive Propagation

The Huub MiniZinc library contains three annotations that let a model request particular propagation algorithms for the `disjunctive` constraint.
They allow the users to choose which propagation techniques should be enabled for that constraint.
The annotations are:
- `edge_finding` requests edge-finding propagation.
- `not_last` requests not-last propagation.
- `detectable_precedence` requests detectable-precedence propagation.
Whenever any of the annotations is present on the `disjunctive` constraint, it overrides the default enabled propagation methods, disabling any other propagation methods that would be enabled by default.
This is best thought of as tuning mechanisms rather than adding these annotations for each `disjunctive` constraint.
