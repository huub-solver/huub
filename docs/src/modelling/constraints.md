# Constraints

Constraints are the rules that a solution must satisfy.
They restrict the possible combinations of values that decision variables can take.
While decision variables represent the unknowns, constraints encode the problem logic.

## Understanding constraints and propagation

When you post constraints to Huub, they are stored in the model.
Once you convert the model to a solver (via `to_solver`), Huub's *constraint propagation* eliminates values from domains that would violate the constraints.
This reduction happens automatically, even before the solver begins searching for solutions.

For example, if you post the constraint that `x != y` (x and y are different), and x can be {1, 2, 3} while y is {3}, then:
1. The constraint discovers that y = 3
2. It eliminates 3 from x's domain, leaving {1, 2}
3. It repeats this process, propagating consequences, until no more values can be eliminated

This is why good constraint propagation is so important: more values can be eliminated before search even begins.

## The constraint posting interface

In Huub, constraints are posted using a builder pattern on the `Model`.
Constraints accept positional arguments in the initial call, named (and sometimes optional) arguments using calls on the builder object, before finalizing with `.post()`.
The pattern typically looks like:

```rust,ignore
model.constraint_name(pos1, pos2)
	.name1(val1)
	.name2(val2)
	.post();
```

For example:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
# let x = model.new_int_decision(0..=10);
# let y = model.new_int_decision(0..=10);
# let z = model.new_int_decision(0..=10);
# let array = vec![x, y, z];
# let idx = model.new_int_decision(0..=2);
# let res = model.new_int_decision(0..=10);
model.unique(vec![x, y, z]).post();
model.linear(x + y*2).eq(10).post();
model.element(array).index(idx).result(res).post();
```

## Constraints in Huub

### Uniqueness constraints

The `unique` constraint enforces that each position in a collection takes a different value (also known as “all different”).

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let digits = model.new_int_decisions(8, 0..=9);
model.unique(digits).post();
```

This forces each digit to take a different value from 0 to 9.

### Linear constraints

Linear constraints enforce arithmetic relationships between decisions.
They are expressed as linear equations or inequalities.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(0..=10);
let y = model.new_int_decision(0..=10);

model.linear(x + y).eq(15).post();   // x + y = 15
model.linear(x*2 + y).le(20).post(); // 2*x + y <= 20
model.linear(x).gt(y).post();        // x > y
```

You can also use arithmetic operators on decision variables:
- `+` (addition)
- `-` (subtraction)
- `*` (multiplication by constants; note: decision-by-decision multiplication requires the `mul` constraint)

Supported comparisons are:
- `.eq(rhs)` — equal to
- `.ne(rhs)` — not equal to
- `.le(rhs)` — less than or equal to
- `.lt(rhs)` — strictly less than
- `.ge(rhs)` — greater than or equal to
- `.gt(rhs)` — strictly greater than

### Element constraints

The element constraint relates a decision variable to an element of an array based on an index decision variable.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let index = model.new_int_decision(0..=4);
let array = model.new_int_decisions(5, 1..=10);
let result = model.new_int_decision(1..=10);

model.element(array).index(index).result(result).post();
// result = array[index]
```

### Minimum and maximum constraints

These constraints enforce that a decision variable is the minimum or maximum of a set of decision variables.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let vars = model.new_int_decisions(5, 1..=20);
let min_var = model.new_int_decision(1..=20);
let max_var = model.new_int_decision(1..=20);

model.minimum(vars.clone()).result(min_var).post();
model.maximum(vars).result(max_var).post();
```

### Multiplication constraints

The `mul` constraint enforces that one decision variable is the product of two others.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(0..=10);
let y = model.new_int_decision(0..=10);
let product = model.new_int_decision(0..=100);

model.mul(x, y).result(product).post();
// product = x * y
```

### Table constraints

Table constraints restrict decisions to take only combinations of values that appear in a given table (like a relation in a database).

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(1..=3);
let y = model.new_int_decision(1..=3);

let valid_combinations = vec![
	vec![1, 2],
	vec![1, 3],
	vec![2, 3],
];

model.table(vec![x, y]).values(valid_combinations).post();
// (x, y) must be one of the valid combinations
```

This is useful when you have discrete rules that cannot easily be expressed as mathematical constraints.

### Value precedence constraints

The value precedence constraint enforces an ordering on the first occurrences of values in a sequence.
By default, it enforces that value 1 precedes value 2, which precedes value 3, and so on.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let vars = model.new_int_decisions(5, 1..=3);

model.value_precede(vars).post();
// The first occurrence of 1 comes before the first occurrence of 2,
// which comes before the first occurrence of 3
```

You can also specify a custom list of values to order:

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let vars = model.new_int_decisions(5, 0..=10);

model.value_precede(vars).values(vec![10, 5, 2]).post();
// The first occurrence of 10 comes before 5, which comes before 2
```

This is useful for breaking symmetries in solutions.

### Power constraints

The power constraint enforces that one decision variable is the result of raising a base to an exponent.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let base = model.new_int_decision(0..=10);
let exponent = model.new_int_decision(0..=5);
let result = model.new_int_decision(0..=100000);

model.pow(base, exponent).result(result).post();
// result = base ^ exponent
```

### Division constraints

The division constraint enforces that one decision variable is the integer division of two others (using truncation towards zero).

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let numerator = model.new_int_decision(-100..=100);
let denominator = model.new_int_decision(-10..=10);
let result = model.new_int_decision(-100..=100);

model.div(numerator, denominator).result(result).post();
// result = numerator / denominator (integer division)
```

### Propositional logic constraints

Boolean formulas allow you to express complex logical conditions using conjunction (AND), disjunction (OR), negation (NOT), implication, and equivalence.

```rust
# extern crate huub;
# use huub::model::Model;
# use huub::model::expressions::BoolFormula;
# let mut model = Model::default();
let x = model.new_bool_decision();
let y = model.new_bool_decision();
let z = model.new_bool_decision();

// Create a formula: (x AND y) OR NOT z
let formula = BoolFormula::Or(vec![
	  BoolFormula::And(vec![
		    BoolFormula::Atom(x),
		    BoolFormula::Atom(y),
	  ]),
	  BoolFormula::Not(Box::new(
	    	BoolFormula::Atom(z),
	  )),
]);

model.proposition(formula).post();
```

## General posting options

Some constraints support additional options that control how they propagate and enable more expressive modeling patterns.

### Reification

A reified constraint is one that is controlled by a Boolean decision variable.
The Boolean decision variable is `true` if-and-only-if the constraint is satisfied.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(0..=10);
let y = model.new_int_decision(0..=10);
let active = model.new_bool_decision();

model.linear(x + y).eq(5).reified_by(active).post();
// The constraint x + y = 5 is active only when `active` is true
```

Many constraint builders also support half-reification with `implied_by`, which enforces a one-way implication: when the Boolean decision variable is `true`, the constraint must hold, but when it is `false`, then we do not care whether the constraint holds or not.
This is useful for modeling conditional logic and implications.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
# let x = model.new_int_decision(0..=10);
# let y = model.new_int_decision(0..=10);
# let active = model.new_bool_decision();
model.linear(x + y).eq(5).implied_by(active).post();
// If `active` is true, then x + y = 5 (but x + y can still equal 5 when `active` is false)
```

### Defining new decision from constraints

Constraints that compute a functional value, that have a `.result()` named argument, can instead use `.define()` to create and return a new decision variable representing that result.
This is a concise alternative to manually creating a resulting decision and posting the constraint.

```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
let x = model.new_int_decision(0..=10);
let y = model.new_int_decision(0..=10);

// Create a new decision variable equal to x + y
let sum = model.linear(x + y).define();

// Or in multiplication:
let product = model.mul(x, y).define();

// Or in absolute value:
let abs_value = model.abs(x).define();
```

Using `.define()` is equivalent to manually creating a resulting decision and posting a constraint.
For example, `model.maximum([x,y]).define()` is shorthand for:
```rust
# extern crate huub;
# use huub::model::Model;
# let mut model = Model::default();
# let x = model.new_int_decision(0..=10);
# let y = model.new_int_decision(0..=10);
let max = model.new_int_decision(0..=10);
model.maximum([x, y]).result(max).post();
```

The new decision variable is automatically added to the model with an appropriate domain inferred from the constraint.
Note, however, that Huub does not automatically detect multiple invocations of the same `.define()` operation, i.e. *common sub-expression elimination*.
As such, it is wise to ensure each functional definition is only created once to avoid duplicate decision variables and constraint propagation, slowing down the solving process.

## Choosing effective constraints

When modeling a problem, use specialized constraints whenever available rather than expressing the constraint as a series of simpler constraints.
Specialized constraints have optimized propagators that work more efficiently than generic alternatives.
For example, `unique` is more efficient than posting many individual `!=` constraints, and `minimum` is more efficient than a set of inequalities.
Similarly, use constraint types that directly express your problem's semantics (like `element` for array indexing) rather than encoding the same idea through multiple simpler constraints.
