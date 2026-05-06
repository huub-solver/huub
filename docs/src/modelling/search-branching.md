# Search and Branching

Once you have created a model with decision variables and constraints, Huub searches for a solution, trying different (potentially all) possible values for the decisions.
This chapter explains how the search process works, how to direct it, and how to find optimal solutions.

## How Huub Searches

Huub performs a depth-first search through the space of possible decisions.
The search tree is explored by making directives on decisions and propagating the consequences of those constraints.
When a conflict is detected—a state where a constraint cannot be satisfied—the solver analyzes the conflict using the underlying SAT solver's conflict-driven clause learning (CDCL) algorithm.
This creates a learned clause that records the reason for the conflict, allowing the solver to backjump directly to the point where the conflict originated, rather than linearly backtracking.

### The search process

At each node in the search tree, the solver must decide:

1. **Which decision to branch on?** Which unfixed decision should we try to limit next?
2. **How do we limit its domain?** Do we try to assign a value to this decision, split its domain, or remove a value, and using what value(s)?

Once the directive is put in place to limit the decision's domain, constraints can once again propagate and may reduce the domains of other decisions.
If this propagation leads to a conflict (an empty domain), the CDCL algorithm analyzes the conflict and the solver backtracks accordingly.
If propagation completes without conflict, the search continues deeper in the tree.

### User-directed vs. automatic search

Huub offers two search strategies for making these decisions, which you can switch between:

**User-directed search:** You provide `Brancher` implementations that explicitly direct which decision to branch on and in what order.
This gives you precise control over the search strategy.
The solver processes user-defined branchers first; when they are exhausted, it falls back to the SAT solver.
This allows you to guide the search for the most critical decisions while letting the SAT solver handle others.

**Automatic search:** The solver defers to the built-in SAT solver (e.g. CaDiCaL), which uses modern heuristics like VSIDS (Variable State Independent Decaying Sum) to make decisions.
This often works well without explicit configuration.

You can set which mode the solver uses via the `SearchStrategy` setting.
Huub provides four options:

- **`SearchStrategy::Branchers`** (default): Use user-defined branchers until they are all exhausted, then defer to the SAT solver.
  This allows domain-specific knowledge to guide critical decisions while leveraging SAT solver heuristics for remaining decisions.

- **`SearchStrategy::Sat`**: Always use the SAT solver's heuristics, ignoring any user-defined branchers.
  Use this if you find that the SAT solver's built-in heuristics work better for your problem.

- **`SearchStrategy::Transition(trigger)`**: Start with user-defined branchers, then switch permanently to the SAT solver when a trigger condition is met.
  The trigger can be based on the number of conflicts (`SwitchTrigger::Conflicts(n)`) or restarts (`SwitchTrigger::Restarts(n)`).
  This allows you to benefit from domain knowledge early in the search, then switch to pure SAT heuristics later.

- **`SearchStrategy::Interleaved(trigger)`**: Alternate between user-defined branchers and the SAT solver at regular intervals.
  Use this to continuously balance domain-specific guidance with SAT solver heuristics throughout the search.

## Directing Search with Branchers

A `Brancher` is an object that directs the search.
Huub provides two pre-built branchers for common use cases: `IntBrancher` for integer decisions and `BoolBrancher` for Boolean decisions.
You can also implement custom branchers for specialized problems.

### Decision and value selection strategies

The built-in branchers use two independent strategies to make decisions:

**Decision selection** — which unfixed decision to branch on:

- `FirstFail`: Choose the decision with the **smallest** remaining domain.
  This is often effective because early failure detection can prune large parts of the search tree.
- `AntiFirstFail`: Choose the decision with the **largest** remaining domain.
  This can be useful to diversify the search.
- `InputOrder`: Choose the first unfixed decision in the order they were added.
- `Smallest`: Choose the decision with the smallest lower bound.
  Useful when you want to explore small values first.
- `Largest`: Choose the decision with the largest upper bound. Useful when you want to explore large values first.

**Value selection** — how to limit the chosen decision:

- `IndomainMin`: Assign the decision to its **lower bound** (smallest possible value). This explores small values first.
- `IndomainMax`: Assign the decision to its **upper bound** (largest possible value). This explores large values first.
- `OutdomainMin`: **Remove** the lower bound and explore other values. This can help find infeasibility quickly.
- `OutdomainMax`: **Remove** the upper bound and explore other values.

### Using branchers in the solver

To use a brancher, create it with a list of decisions, a decision selection strategy, and a value selection strategy, then add it to the solver:

```rust
# extern crate huub;
# use huub::{
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{
# 		branchers::{IntBrancher, ValueSelection, VariableSelection},
# 		IntValuation, Solver,
# 	},
# };
# let mut model = Model::default();
# let x = model.new_int_decision(0..=100);
# let y = model.new_int_decision(0..=100);
# let (mut solver, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
# let x = map.get(&mut solver, x);
# let y = map.get(&mut solver, y);
// Use an IntBrancher to branch on decisions [x, y] using FirstFail and
// IndomainMin
IntBrancher::new_in(
	&mut solver,
	vec![x, y],
	VariableSelection::FirstFail,
	ValueSelection::IndomainMin,
);

solver.solve(|sol| {
	println!("Found solution: x={}, y={}", x.val(sol), y.val(sol));
});
```

**Note:** Once you have assigned all branchers to the solver, any remaining unfixed decisions will be handled by the SAT solver's automatic heuristics.

## Warm Starting the Search

When you have a known solution or a partial solution, you can use a `WarmStartBrancher` to guide the solver towards it.
This can significantly speed up the search by quickly finding a good starting point.

A warm-start brancher takes a list of Boolean conditions to enforce. The solver will try to satisfy these conditions, but if a conflict occurs, it will abandon the warm-start and proceed with regular search.
This makes warm-starting robust: if your partial solution turns out to be incompatible with the constraints, the solver will gracefully recover.

```rust
# extern crate huub;
# use huub::{
# 	actions::IntDecisionActions,
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{branchers::WarmStartBrancher, IntLitMeaning, Solver},
# };
# let mut model = Model::default();
# let b = model.new_bool_decision();
# let x = model.new_int_decision(1..=10);
# let (mut solver, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
# let b = map.get(&mut solver, b);
# let x = map.get(&mut solver, x);
// Warm start by suggesting certain boolean decisions should be true
let warm_start_decisions = vec![b, x.lit(&mut solver, IntLitMeaning::Eq(5))];

// Create and register the warm-start brancher
WarmStartBrancher::new_in(&mut solver, warm_start_decisions);

solver.solve(|solution| {
	println!("Found solution");
});
```

The warm-start brancher will try to enforce these decisions first, potentially finding a solution much faster than exploring from scratch.

## Finding Solutions

Once you have created a solver, you can search for solutions using the `solve()` method:

```rust
# extern crate huub;
# use huub::{
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{Solver, Status},
# };
# let mut model = Model::default();
# let x = model.new_int_decision(1..=9);
# let (mut solver, _): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
let status = solver.solve(|solution| {
	// This callback is invoked if a solution is found.
	println!("Found a solution!");
});

match status {
	Status::Satisfied => println!("Found a solution"),
	Status::Unsatisfiable => println!("No solution exists"),
	Status::Unknown => println!("Search was interrupted"),
	Status::Complete => unreachable!("no *further solutions possible* (not used with solve)"),
}
```

The `solve()` method returns immediately after finding the first solution.
For some applications, this is sufficient—you have a valid assignment to all decision variables.

## Setting Termination Limits

To prevent the solver from running indefinitely, you can set termination limits using a callback function.
This is useful for time-limited solving, controlling resource usage, or stopping the search after finding a good enough solution.

The `set_terminate_callback` method allows you to provide a closure that returns a termination signal:

```rust
# extern crate huub;
# use std::time::Instant;
#
# use huub::{
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{Solver, Status},
# 	TerminationSignal,
# };
# let mut model = Model::default();
# let (mut solver, _): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
let start_time = Instant::now();
let time_limit = std::time::Duration::from_secs(10);

solver.set_terminate_callback(Some(move || {
	if start_time.elapsed() > time_limit {
		TerminationSignal::Terminate
	} else {
		TerminationSignal::Continue
	}
}));

let status = solver.solve(|solution| {
	println!("Found solution");
});

match status {
	Status::Satisfied => println!("Found solution within time limit"),
	Status::Unknown => println!("Interrupted after time limit with no solution"),
	_ => {}
}
```

The callback is called periodically during the search, allowing you to check conditions like:

- **Time limits**: Stop after N seconds or milliseconds.
- **Solution limits**: Stop after finding N solutions.
- **Resource limits**: Stop when memory or CPU usage exceeds a threshold.
- **External signals**: Stop when receiving an interrupt signal (Ctrl+C).

When the callback returns `TerminationSignal::Terminate`, the solver will abandon the current search branch and return immediately with `Status::Unknown` if no solution has been found yet.


## Finding Optimal Solutions

To find the *best* solution (minimizing or maximizing an objective), Huub provides the `branch_and_bound()` method.
This performs an iterative search: after finding each solution, it adds a constraint that the next solution must be better, and continues searching.

```rust
# extern crate huub;
# use huub::{
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{IntValuation, Solver, Status},
# 	Goal,
# };
# let mut model = Model::default();
# let x = model.new_int_decision(0..=100);
# let y = model.new_int_decision(0..=100);
# let cost = model.linear(x + y).define();
# let (mut solver, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
# let cost = map.get(&mut solver, cost);
let (status, stats, optimal_cost) = solver.branch_and_bound(
	Goal::Minimize(cost),
	// This callback is invoked for each solution that is found.
	|sol| println!("Found (better) solution with cost {}", cost.val(sol)),
);

match status {
	Status::Complete => {
		println!("Optimal solution found with cost {:?}.", optimal_cost);
	}
	Status::Satisfied => {
		println!("Search was interrupted, after at least one solution was found.");
	}
	Status::Unsatisfiable => {
		println!("No feasible solution exists.");
	}
	Status::Unknown => {
		println!("Search was interrupted before any solution was found.");
	}
	_ => {}
}
```

The branch-and-bound loop continues until:

- **Complete**: A solution is found that cannot be improved further (proven optimal).
- **Unsatisfiable**: No feasible solutions exist.
- **Satisfied**: The search was interrupted by a termination signal, after at least one solution was found.
- **Unknown**: The search was interrupted by a termination signal, before any solution was found.

For a minimization goal, after each solution is found, Huub adds a constraint that the objective must be strictly less than the current best value.
For a maximization goal, it adds a constraint that the objective must be greater than or equal to the current best value plus one.


## Finding All Solutions

To find all possible solutions (not just the first one or the optimal one), use the `all_solutions()` method.
This is useful for exploring the solution space, enumerating all valid assignments, or finding Pareto-optimal solutions.

```rust
# extern crate huub;
# use huub::{
# 	lower::InitConfig,
# 	model::Model,
# 	solver::{IntValuation, Solver, Status},
# };
# let mut model = Model::default();
# let x = model.new_int_decision(1..=3);
# let y = model.new_int_decision(1..=3);
# model.linear(x).ne(y).post();
# let (mut solver, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
# let x = map.get(&mut solver, x);
# let y = map.get(&mut solver, y);
let mut num_sol = 0;
let (status, stats) = solver.all_solutions(&vec![x.into(), y.into()], |solution| {
	num_sol += 1;
	println!("Solution: x={}, y={}", x.val(solution), y.val(solution));
});

match status {
	Status::Complete => {
		println!("Found all {num_sol} solutions");
	}
	Status::Satisfied => {
		println!("Interrupted; found {num_sol} solutions");
	}
	Status::Unsatisfiable => {
		println!("No solutions exist");
	}
	_ => {}
}
```

The method works by iteratively finding solutions and then adding "no-good" constraints that exclude each found solution from future searches.
The solver continues until either:

- **Complete**: All solutions have been enumerated (trying to find another solution fails).
- **Satisfied**: The search was interrupted by a termination signal after finding at least one solution.
- **Unsatisfiable**: No solutions exist (if no solutions were found before interruption, returns `Unknown`).
- **Unknown**: The search was interrupted before any solution was found.

Note that you must specify the decision variables whose values you want to enumerate in the `vars` slice.
This allows the solver to know which combinations to treat as distinct solutions—other decisions in the model are not constrained by the no-good exclusion.

## Solver Statistics

You can retrieve statistics about the search process to understand solver behavior:

```rust
# extern crate huub;
# use huub::{lower::InitConfig, model::Model, solver::Solver};
# let mut model = Model::default();
# let (mut solver, _): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
# let _ = solver.solve(|_| {});
let stats = solver.solver_statistics();

println!("Conflicts: {}", stats.conflicts);
println!("User search directives: {}", stats.user_search_directives);
println!("SAT solver directives: {}", stats.sat_search_directives);
println!("Propagations: {}", stats.cp_propagator_calls);
println!("Restarts: {}", stats.restarts);
```

These statistics help you understand:

- `conflicts`: How many times the solver had to backtrack.
- `user_search_directives`: How many times your branchers directed the search.
- `sat_search_directives`: How many times the SAT solver directed the search.
- `cp_propagator_calls`: How many times constraints propagated values.
- `restarts`: How many times the solver restarted the search from the top.

## SAT Solver Control Options

Huub's underlying SAT solver includes various preprocessing and inprocessing techniques that can be tuned to control search behavior and performance.
These are configured when creating the solver through the `InitConfig`:

```rust
# extern crate huub;
# use huub::{lower::InitConfig, model::Model, solver::Solver};
# let mut model = Model::default();
# let x = model.new_int_decision(0..=10);
// Enable/disable various SAT preprocessing and inprocessing techniques
let mut config = InitConfig::default()
	.with_preprocessing(2)
	.with_inprocessing(true)
	.with_probing(true)
	.with_subsumption(true)
	.with_variable_elimination(true)
	.with_vivification(true)
	.with_conditioning(true)
	.with_reason_eager(true);

# let (_, _): (Solver, _) = model.to_solver(&config).unwrap();
```

**Key SAT solver options:**

- **Preprocessing** (`with_preprocessing(n)`): Run N rounds of SAT preprocessing before search begins.
  More rounds can reduce the problem size but take more time upfront.
  Default is typically 1.
- **Inprocessing** (`with_inprocessing(bool)`):
  Enable or disable SAT inprocessing during search.
  Inprocessing simplifies clauses and removes redundant variables as the solver learns more.
  Can improve search efficiency but adds overhead.
- **Probing** (`with_probing(bool)`): Enable or disable failed-literal probing, which tries to detect implications of setting variables to specific values.
  This helps find inconsistencies early, but it is computationally expensive.
- **Subsumption** (`with_subsumption(bool)`): Enable or disable forward subsumption, which removes clauses that are subsumed by learned clauses.
  This reduces clause database bloat, but requires expensive checking.
- **Variable Elimination** (`with_variable_elimination(bool)`): Enable or disable bounded variable elimination, which removes variables by adding resolvent clauses.
  It can reduce the problem size significantly, but it is expensive.
- **Vivification** (`with_vivification(bool)`): Enable or disable clause vivification, which strengthens clauses by removing literals that are implied. Helps derive stronger learned clauses.
- **Conditioning** (`with_conditioning(bool)`): Enable or disable blocked clause elimination (conditioning), which removes clauses that are logically redundant with respect to the learned clause set.
- **Reason Eager** (`with_reason_eager(bool)`): Eagerly compute explanation clauses for all literals propagated at the conflict level.
  This improves explanations but adds memory overhead.

These options trade off between problem size reduction (fewer variables/clauses means faster search) and preprocessing time.
For time-critical applications, you may want to disable expensive techniques or reduce preprocessing rounds.
