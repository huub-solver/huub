# Decision Variables

Decision variables are the unknowns in a constraint program.
They represent the values we want to find solutions for.

## Boolean decision variables

At the core of all decision variables in Huub are Boolean decision variables.
They are unknowns that must take the value `true` or `false`.
You can create Boolean variables using `model.new_bool_decision()`:

```rust
let x = model.new_bool_decision();
let y = model.new_bool_decision();
```

For convenience, you can also create multiple Boolean decisions at once:

```rust
let vars = model.new_bool_decisions(10);
```

Boolean decision variables are used directly when modelling decisions that are inherently binary, such as:
- whether something is included or not,
- whether a constraint is active or not, or
- modeling the truth values of logical formulas.
Boolean decision variables in Huub generally function the same way as the Boolean decision variables in a SAT solver.
There they are use used as “literals” (allowing you to negate them), as part of “clauses” (i.e. disjunctions).
Importantly, in SAT the negation of the decision is inherent to the “clause”, avoiding a separate representation for the negated decision.
Later in this section we'll see that the same is true for Huub through the use of `View`s.
Different from SAT solvers, however, Boolean decision variables can be used in a much wider array of constraints, as shown in the next section.

## Integer decision variables

Integer decision variables represent decisions that can be represented by whole (integral) numbers.
Although we use integers to represent them, they are generally used to represent anything that must take a value from an enumerable set of values.
For each integer decision variables, we must specify its domain upon creation.
In Huub, the domain is given using a value that can be converted into a `RangeList<i64>`, such as a `RangeInclusive<i64>` or a `RangList<i64>` itself.
For example:

```rust
let x = model.new_int_decision(1..=9);      // values 1 to 9
let y = model.new_int_decision(0..=100);    // values 0 to 100
let z = model.new_int_decision(RangeList::from([1..=1, 3..=3, 5.=5, 7..=7]); // specific values
```

Again for convenience, when you need many decisions with the same domain, you can use the batch creation method.
The following fragment creates 20 integer decisions, each with the domain 0 to 9.

```rust
let vars = model.new_int_decisions(20, 0..=9);
```

### Choosing appropriate domains

When creating decision variables, it is important to specify a domain that is as tight as possible.
Small domains are essential for constraint propagation efficiency.
For example, when posting constraints involving arithmetic, decisions with excessively large domains might cause (potential) numerical overflow during propagation.
Moreover, some constraint propagators depend critically on the size of a domain, meaning that larger domains require more work during propagation.

As a best practice, think carefully about what values each decision can actually take in your problem, rather than just using the largest possible range.
The effort spent on specifying good domains upfront pays dividends in solver performance.

**Important:** If the domain has only one value, Huub automatically converts it to a constant.
Similarly, if the domain only has two values, then Huub will use a single Boolean decision to represent it.
This is an automatic optimization, there's no need to over-optimize the code that creates your decision variables.

### Empty domains

In Huub, there is a fundamental invariant: **decision variable domains are never empty**.
When creating a new decision, you must ensure the domain is not empty.
For example, attempting to create a decision with an invalid range:

```rust
// This would panic
let invalid = model.new_int_decision(5..=2);  // min > max
```

After creation, the solver enforces this invariant.
It is important for correctness: it guarantees that at any point in the search, either a variable still has possible values, or the search has failed and will backtrack.
In practice, this means you don't need to worry about empty domains after the decision variables have been created.

### Understanding domains in constraint programming

The **domain** of a decision is the set of possible values it can take.
Constraint propagation works by progressively reducing domains.
For example, if you constrain two decisions to be different using `unique()`, the solver eliminates values from their domains that would violate this constraint.

The key insight in constraint programming is that the solver explores the search space by:

1. **Constraint propagation:** Eliminating values from domains based on constraints.
2. **Branching:** When propagation can't eliminate more values, picking a decisions and trying different values for it.

By representing domains explicitly, Huub can reason about what values are still possible for each decisions, which makes the search more efficient.

## Decision views and aliases

When you create a decision variable, Huub returns a **View** of that decision.
A view is a reference that you can use within the model layer (for posting constraints) and later within the solver layer (for querying solution values).

The reason for this two-level design (Decision in the Model, View in the Solver) is that Huub may transform decisions during lowering—for example, replacing a decision with a linear expression or combining multiple decisions.
Views ensure you always query the correct transformed decisions, even if the underlying representation changes.

This abstraction is particularly important when constraints transform or combine decisions, which we'll see in later chapters on constraints and expressions.

### Decision references and cloning

When you copy a view, you don't create a new decision—you create another reference to the same decision implementation.
For example:

```rust
let x = model.new_int_decision(1..=10);
let x_alias = x;  // x_alias refers to the same decision as x
```

Both `x` and `x_alias` refer to the same underlying decision, not separate decisions.
This is useful when you want to use the same decision in multiple constraints.

## Efficient domain representation

Internally, integer decisions use **interval lists** to represent their domains.
This allows Huub to represent domains compactly even for large ranges of values.
For example, the domain `{0, 1, 2, 3, 10, 11, 12}` is represented as two intervals: `[0,3]` and `[10,12]`, which is much more memory-efficient than storing each value individually.

This representation is transparent to you as a modeler, but it means Huub can efficiently handle decisions with large domains without excessive memory overhead.
