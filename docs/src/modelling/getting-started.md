# Getting Started

This chapter introduces you to Huub by walking through a complete example: the classic “Send More Money” cryptarithmetic puzzle.
We'll learn how to model problems, post constraints, and solve them step-by-step.

In the “Send More Money” problem, each letter represents a different digit (0-9), and the following arithmetic relationship must hold.

```text
  SEND
+ MORE
------
 MONEY
```

We need to find an assignment of digits to letters such that the addition is correct.
Note that `S` and `M` are the first digits of the numbers, and thus cannot take the value zero.
This introductory example demonstrates the core concepts of constraint modelling: decision variables, constraints, and solving.

## Building the model

Let's build the model step by step.

### Creating decision variables

The first step is to create decision variables for each unknown digit.
In Huub, we do this using `model.new_int_decision()`.

```text
{{#include ../../../crates/huub/examples/send-more-money/main.rs:create_model}}
```

Each call to `new_int_decision()` creates a decision variable with the specified possible values, also called its domain.
Since we only need to determine the value for each repeated letter once, we only create a single decision variable for them.
By restricting S and M to `1..=9`, we also enforce that they cannot be zero without needing a separate constraint.

### Posting constraints

The next step is to post constraints that the solution must satisfy.
In this problem, we have to post two constraints.

**1. Unique constraint:** Each letter must be different digit.

```text
{{#include ../../../crates/huub/examples/send-more-money/main.rs:unique_constraint}}
```

The `unique()` constraint ensures that all decisions in the vector have different values.
It is important that each decision variable only appears once in the argument vector, since the `unique()` constraint enforces that *each position* in the vector takes a different value.
Constraint-builder methods, like `unique()` are finalized using the `.post()` method, which adds it to the model.

**2. Arithmetic constraint:** The addition `SEND+MORE=MONEY` must be correct.
The key insight here is to connect the individual digits into the larger numbers by multiplying them and adding them together.
We need:
- SEND = 1000×S + 100×E + 10×N + D
- MORE = 1000×M + 100×O + 10×R + E
- MONEY = 10000×M + 1000×O + 100×N + 10×E + Y
We can then constrain `SEND + MORE` to equal `MONEY`.

In Huub, we express this using linear expressions.
Similar to our strategy above we can first create expressions for `SEND`, `MORE`, and `MONEY`, and then we use a `linear()` constraint to constrain the equality.

```rust,ignore
{{#include ../../../crates/huub/examples/send-more-money/main.rs:arithmetic_constraint}}
```

The `linear()` method takes a linear expression and returns a builder.
We then call `.eq()` to specify that the expression should equal another expression, and again use `.post()` to add the constraint to the model.

## Solving the problem

Now that we have defined the model, we need to convert it to a solver and run the search to find a solution.

### Converting to a solver

The first step is to convert the model to a solver object that can search for solutions:

```rust,ignore
{{#include ../../../crates/huub/examples/send-more-money/main.rs:convert_to_solver}}
```

The `to_solver()` method returns a tuple:
- `solver`: The `Solver` object that will perform the search.
- `map`: A `LoweringMap` that maps from the `Model` decision variables to the `Solver` decision variables.

We need to query the map to get the decision variables that we can use in the solver.
This version of the decision variables will allow us to query the solution for their values later on.

```rust,ignore
{{#include ../../../crates/huub/examples/send-more-money/main.rs:map_variables}}
```

### Running the solver

Now we can search for solutions.
For a simple constraint satisfaction problem (finding one solution without optimization), we use the `solve()` method with a callback:

```rust,ignore
{{#include ../../../crates/huub/examples/send-more-money/main.rs:solve_and_print}}
```

The callback function is called if a solution is found.
Inside the callback, you can query decision variable values using the `val` method from the `IntValuation` trait.
If no solution is found (either because of a set search limit or because none exists), then the callback is never called.

## Understanding the solving process

When you run this model with Huub, the solver performs **depth-first search** with backjumping.
At each node in the search tree:

1. **Constraint propagation:** The solver propagates constraints to reduce the domains of decision variables.
   For example in our problem, if we determined that `S=9`, then propagation would infer that no other decision variables can take the value 9, removing it from their domain.
2. **Branching:** If domains cannot be reduced further, the solver picks an unassigned decision and tries assigning it a value from its domain.
3. **Backjumping on conflict:** If an inconsistency is detected, the solver backtracks (not necessarily to the previous decision, but often to the decision that caused the inconsistency).

The beauty of Huub's CP+SAT approach is that complex constraints like `unique()` are implemented as **propagators** that efficiently reduce domains, and when conflicts occur, the SAT solver learns **clauses** that prevent exploring the same inconsistent region again.

## Complete working example

The complete example is available as the `send-more-money` and can be run with:

```bash
cargo run --example send-more-money
```

Output:
```text
Solution found!

     S=9, E=5, N=6, D=7
 +   M=1, O=0, R=8, E=5
-----------------------
M=1, O=0, N=6, E=5, Y=2

9567 + 1085 = 10652
```
