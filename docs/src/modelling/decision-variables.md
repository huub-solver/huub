# Decision Variables

Decision variables are the unknowns in a constraint program.
They represent the values we want to find solutions for.

## Boolean decision variables

At the core of all decision variables in Huub are Boolean decision variables.
They are unknowns that must take the value `true` or `false`.
You can create Boolean decisions using `model.new_bool_decision()`:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_bool_decision();
let y = model.new_bool_decision();
```

For convenience, you can also create multiple Boolean decisions at once:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let vars = model.new_bool_decisions(10);
```

Boolean decision variables are used directly when modelling decisions that are inherently binary, such as:
- whether something is included or not,
- whether a constraint is active or not, or
- modeling the truth values of logical formulas.

Boolean decision variables in Huub generally function the same way as the Boolean decision variables in a SAT solver.
There they are used as "literals" (allowing you to negate them), as part of "clauses" (i.e. disjunctions).
Importantly, in SAT the negation of the decision is inherent to the "clause", avoiding a separate representation for the negated decision.
Later in this section we'll see that the same is true for Huub through the use of `View`s.
Different from SAT solvers, however, Boolean decision variables can be used in a much wider array of constraints, as shown in the next section.

## Integer decision variables and domains

Integer decision variables represent decisions that can be represented by whole (integral) numbers.
Although we use integers to represent them, they can be used to represent anything that must take a value from an enumerable set of values.

### What is a domain?

For each integer decision variable, we must specify its **domain** upon creation.
The domain is the set of possible values the decision can take.
Choosing a good domain means specifying realistic values based on your problem, which can be critical for solver efficiency.

In Huub, domains are represented as **interval lists**, using the `rangelist::RangeList` type.
This allows Huub to represent domains compactly even for large ranges of values.
For example, the domain `{0, 1, 2, 3, 10, 11, 12}` is represented as two intervals: `[0,3]` and `[10,12]`, which is much more memory-efficient than storing each value individually.
This representation is transparent to you as a modeler, but it enables Huub to efficiently handle decisions with large domains without excessive memory overhead.

You can create an integer decision using `model.new_int_decision(<domain>)`.
The `<domain>` argument can be any value that can be converted into a `Set<i64>`, such as a `RangeInclusive<i64>` or a `rangelist::RangeList<i64>` itself.
For example:

```rust
# extern crate huub;
# use huub::{model::Model, Set};
# let mut model = Model::default();
let x = model.new_int_decision(1..=9);      // values 1 to 9
let y = model.new_int_decision(0..=100);    // values 0 to 100
let z = model.new_int_decision(Set::from_iter([1..=1, 3..=3, 5..=5, 7..=7])); // specific values
```

For convenience, when you need many decisions with the same domain, you can use the batch creation method.
The following fragment creates 20 integer decisions, each with the domain 0 to 9:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let vars = model.new_int_decisions(20, 0..=9);
```

### Why domains matter

When specifying a domain, it is important to choose a domain that is as tight as possible.
Small domains are essential for constraint propagation efficiency.
There are several concrete reasons why this matters:

- **Numerical overflow**: When posting constraints involving arithmetic, decisions with excessively large domains might cause (potential) numerical overflow during propagation.
- **Search space**: A smaller domain directly reduces the search space the solver must explore.
- **Propagation speed**: Some constraint propagators have complexity that depends on domain size, so larger domains require significantly more work during propagation.

As a best practice, think carefully about what values each decision can actually take in your problem.
The effort spent on specifying good domains upfront pays dividends in solver performance.

### Domain invariants and special cases

**Empty domains are never allowed.** In Huub, there is a fundamental invariant: decision variable domains are never empty.
When creating a new decision, you must ensure the domain is not empty.
For example, attempting to create a decision with an invalid range will panic:

```rust,ignore
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let invalid = model.new_int_decision(5..=2);  // This panics: min > max
```

After creation, the solver enforces this invariant.
It is important for correctness: it guarantees that at any point in the search, either a decision still has possible values, or the search has failed and will backtrack.
In practice, this means you don't need to worry about empty domains after the decision variables have been created.

**Automatic optimizations.** Huub automatically optimizes certain special cases:

- If the domain has only one value, Huub automatically converts it to a constant (e.g., `5..=5` becomes the constant 5).
- If the domain only has two values, then Huub will use a single Boolean decision to represent it.

These are automatic optimizations; there's no need to manually optimize your code when creating decision variables.

## Decision variable `View`s

When you create a decision variable, Huub returns a `View` of that decision.
A View can represent three different things:

1. **A base decision variable** — When you specify a domain with multiple values, Huub creates an actual unknown decision and returns a View to it. This is what the solver works to assign.
2. **A functional view** — Later in the modeling layer, constraints and expressions can create derived Views that are functions of base decisions (like a linear transformation `2*x + 3`).
   These Views don't create separate base decisions to track.
3. **A constant value** — When you specify a domain with only one possible value (e.g., `5..=5`), Huub returns a View that is a constant.
   There's no unknown to solve for; the value is already determined.

This three-level design minimizes the number of base decisions the solver must manage, which keeps the underlying solver efficient.
When you copy (or clone) a `View`, you don't create a new decision, you just create a copy of the reference.
For example:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(1..=10);
let x_alias = x;  // x_alias refers to the same decision as x
```

Both `x` and `x_alias` refer to the same underlying decision, not separate decisions.
