# Jobshop

Jobshop scheduling is a strong first case study because it connects modelling, propagation, and search behavior in a single example.


## Problem description

The Job Shop Scheduling Problem (JSSP) is a classic combinatorial optimization problem.
There are **N jobs** and **M machines**.
Each job consists of a fixed sequence of operations; each operation must be processed on a specific machine for a given duration.
The problem has the following constraints:

- **Precedence**: the operations of a job must be executed in order.
- **Disjunctive**: at most one operation may run on any machine at a time.

This example models both constraints and solves to optimality using Huub's Lazy Clause Generation engine, supporting two objective functions:

| Objective | Description |
|-----------|-------------|
| `makespan` *(default)* | Minimise the time at which the last operation completes. |
| `total-completion-time` | Minimise the sum of per-job completion times. |

## Implementation walkthrough

The implementation of the jobshop example is organized into three modules:

### Creating decision variables

Each operation requires a start time decision variable.
In the `JobShopModel::new()` method, we create a start time variable for each operation of each job:

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/model.rs:create_decision_variables}}
```

Each start time variable has a domain from 0 to the sum of all processing times in the instance (the latest time any operation can possibly start).

### Posting constraints

Two types of constraints model the jobshop problem:

**Precedence constraints**: Each job's operations must be executed in order.
For each job, we ensure that operation `i+1` cannot start before operation `i` finishes:

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/model.rs:precedence_constraints}}
```

**Disjunctive constraints**: No two operations can run on the same machine simultaneously.
For each machine, we post a disjunctive constraint that enforces non-overlapping execution:

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/model.rs:disjunctive_constraints}}
```

### Defining the objective

The example supports two objective functions.
For the makespan objective, we create a decision variable that must be greater than or equal to the completion time of every job.
For the total completion time objective, we use `.define()` to create a derived view that represents the sum of all job completion times:

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/model.rs:define_objective}}
```

### Search strategy and branching

This example demonstrates how to implement a custom brancher for domain-specific search strategies.
While Huub provides built-in branchers for common variable selection strategies, implementing a custom brancher allows you to leverage problem-specific knowledge.

In the jobshop problem, a key insight is that jobs with more work remaining are generally less constrained.
By prioritizing these jobs early, we can detect infeasibility faster and prune more of the search space.

To implement a custom brancher, you create a struct that implements the `Brancher` trait, which requires a `decide` method called at each search node to determine the next variable-value assignment to try.

#### Initialization

The brancher stores the operations and maintains trailed data to track:
- The scores for each job (how much work or how many operations remain)
- The index of the first unfixed variable

The trailed data is automatically restored on backtrack, allowing the brancher to maintain consistent state across the search tree.

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/brancher.rs:initialize_brancher}}
```

During initialization, we call `solver.ensure_decidable()` on each operation's start time variable to inform the solver that our brancher will make decisions about these variables.
We then register the brancher with the solver using `push_brancher()`.

#### The decide method

At each search node, the `decide` method implements the following logic:

1. **Check if done**: If we've assigned all operations, return `Directive::Exhausted` to signal the brancher has finished.

2. **Compute job scores**: Iterate through all unfixed operations. Track which job each unfixed operation belongs to. The score for each job is either the total remaining processing time or the number of remaining operations, depending on the chosen strategy.

3. **Select the best job**: Among jobs with unfixed operations, choose the one with the highest score (or lowest for "least work" strategies). This is the job we should branch on next.

4. **Branch on the selected job's first unfixed operation**: Return a branching directive indicating which operation to branch on and what value to try first.

5. **Update state**: Update trailed data so it's properly restored when the search backtracks.

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/brancher.rs:decide_method}}
```

### Solving and extracting solutions

The solver uses branch-and-bound search to find optimal solutions.
This algorithm maintains an upper bound on the objective (the best solution found so far) and uses this bound to prune branches that cannot lead to better solutions.

Each time a solution is found, it triggers a callback.
The callback is your opportunity to extract the solution, perform logging, or update the objective bound.
In the jobshop example, the callback displays the makespan or total completion time of each solution found, allowing you to track progress as the solver explores the search space:

```rust,ignore
{{#include ../../../crates/huub/examples/jobshop/main.rs:solve_with_branch_and_bound}}
```

## Running the example

The jobshop example is available in the Huub repository.
Instances are provided in a simple text format (see [Instance file format](#instance-file-format) below).

Run the example with:

```bash
# Solve an instance (makespan objective, default settings)
cargo run --example jobshop --release -- instances/2x2.jsp

# Solve with a 30-second time limit, print statistics, and verbose output
cargo run --example jobshop --release -- -t 30s -s -v instances/6x6.jsp

# Minimise total completion time instead
cargo run --example jobshop --release -- --objective-type total-completion-time instances/6x6.jsp
```

You can experiment with different branching strategies using the `--branching-strategy` flag:

```bash
# Use dynamic least-work strategy
cargo run --example jobshop --release -- --branching-strategy least-work instances/6x6.jsp
```

Use the command `cargo run --example jobshop -- --help` to get more information about the available options.

You can also run the tests with:

```bash
cargo test --example jobshop
```

## Instance file format

Instance files use a simple whitespace-separated text format:

```text
N M
m(0,0) d(0,0)  m(0,1) d(0,1)  ...  m(0,M-1) d(0,M-1)
m(1,0) d(1,0)  m(1,1) d(1,1)  ...  m(1,M-1) d(1,M-1)
...
m(N-1,0) d(N-1,0)  ...  m(N-1,M-1) d(N-1,M-1)
```

- **Line 1**: `N` (number of jobs) and `M` (number of machines), space-separated.
- **Lines 2 … N+1**: one line per job, containing `M` pairs of integers.
  Each pair is `machine_id processing_time`.
  The k-th pair describes the k-th operation of that job: it must run on `machine_id` for `processing_time` time units.
  Machine indices start at 0.

**Example** — `instances/2x2.jsp`

```text
2 2
0 3 1 2
1 4 0 1
```

- Job 0: first run on machine 0 for 3 units, then on machine 1 for 2 units.
- Job 1: first run on machine 1 for 4 units, then on machine 0 for 1 unit.
- Optimal makespan: **6**.
- Optimal total completion time: **11**.

### Included instances

| File | Jobs × Machines | Optimal makespan | Optimal total completion |
|------|-----------------|-----------------| -------------|
| `instances/2x2.jsp` | 2 × 2 | 6 | 11 |
| `instances/6x6.jsp` | 6 × 6 | 23 | 107 |

### Finding more instances

- **OR-Library** — the original collection by Beasley, Mattfeld and Vaessens; includes ft06/ft10/ft20, abz5–abz9, la01–la40, orb01–orb10, swv01–swv20, and the yn and ta families: <http://people.brunel.ac.uk/~mastjjb/jeb/orlib/jobshopinfo.html>

- **Taillard benchmarks** — 80 instances ranging from 15×15 to 100×20: <http://mistic.heig-vd.ch/taillard/problemes.dir/ordonnancement.dir/jobshop.dir/best_lb_up.txt>

All OR-Library files use exactly the same format as the instances here (first line: `N M`; then N lines of machine/duration pairs, 0-indexed machines), so they can be used directly.
