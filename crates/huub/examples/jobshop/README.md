# Job Shop Scheduling Example

This example demonstrates how to model and solve the
[Job Shop Scheduling Problem (JSSP)](https://en.wikipedia.org/wiki/Job-shop_scheduling)
using the **Huub** constraint programming library.

## Problem description

The JSSP is a classic combinatorial optimisation problem. There are **N jobs**
and **M machines**. Each job consists of a fixed sequence of operations; each
operation must be processed on a specific machine for a given duration.
The problem has the following constraints:

- **Precedence**: the operations of a job must be executed in order.
- **Disjunctive**: at most one operation may run on any machine at a time.

This example models both constraints and solves to optimality using Huub's
Lazy Clause Generation engine, supporting two objective functions:

| Objective | Description |
|-----------|-------------|
| `makespan` *(default)* | Minimise the time at which the last operation completes. |
| `total-completion-time` | Minimise the sum of per-job completion times. |

## Building and running

```bash
# Solve an instance (makespan objective, default settings)
cargo run --example jobshop -- instances/2x2.jsp

# Solve with a 30-second time limit, print statistics, and verbose output
cargo run --example jobshop -- -t 30s -s -v instances/6x6.jsp

# Minimise total completion time instead
cargo run --example jobshop -- --objective-type total-completion-time instances/6x6.jsp
```

Use the command `cargo run --example jobshop -- --help` to get more information
about the available options.

## Instance file format

Instance files use a simple whitespace-separated text format:

```
N M
m(0,0) d(0,0)  m(0,1) d(0,1)  ...  m(0,M-1) d(0,M-1)
m(1,0) d(1,0)  m(1,1) d(1,1)  ...  m(1,M-1) d(1,M-1)
...
m(N-1,0) d(N-1,0)  ...  m(N-1,M-1) d(N-1,M-1)
```

- **Line 1**: `N` (number of jobs) and `M` (number of machines), space-separated.
- **Lines 2 … N+1**: one line per job, containing `M` pairs of integers. Each
  pair is `machine_id processing_time`. The k-th pair describes the k-th
  operation of that job: it must run on `machine_id` for `processing_time` time
  units. Machine indices start at 0.

### Example — `instances/2x2.jsp`

```
2 2
0 3 1 2
1 4 0 1
```

- Job 0: first run on machine 0 for 3 units, then on machine 1 for 2 units.
- Job 1: first run on machine 1 for 4 units, then on machine 0 for 1 unit.
- Optimal makespan: **6**.
- Optimal total completion time: **11**.

## Running tests

The example has regression tests that parse and solve included instances.

```bash
cargo test --example jobshop
```

## Included instances

| File | Jobs × Machines | Optimal makespan | Optimal total completion | 
|------|-----------------|-----------------| -------------|
| `instances/2x2.jsp` | 2 × 2 | 6 | 11 |
| `instances/6x6.jsp` | 6 × 6 | 23 | 107 |

## Finding more instances

- **OR-Library** — the original collection by Beasley, Mattfeld and Vaessens;
  includes ft06/ft10/ft20, abz5–abz9, la01–la40, orb01–orb10, swv01–swv20,
  and the yn and ta families:
  <http://people.brunel.ac.uk/~mastjjb/jeb/orlib/jobshopinfo.html>

- **Taillard benchmarks** — 80 instances ranging from 15×15 to 100×20:
  <http://mistic.heig-vd.ch/taillard/problemes.dir/ordonnancement.dir/jobshop.dir/best_lb_up.txt>

All OR-Library files use exactly the same format as the instances here (first
line: `N M`; then N lines of machine/duration pairs, 0-indexed machines), so
they can be used directly.

[orlib]: http://people.brunel.ac.uk/~mastjjb/jeb/orlib/jobshopinfo.html
