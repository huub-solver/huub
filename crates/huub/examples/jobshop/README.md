# Job Shop Scheduling Example

This example demonstrates how to model and solve the [Job Shop Scheduling Problem (JSSP)](https://en.wikipedia.org/wiki/Job-shop_scheduling) using the **Huub** constraint programming library.

For a detailed description of the problem, instance file format, and benchmark instances, see the [Jobshop case study](https://huub.solutions/case-studies/jobshop.html) in the Huub documentation.

## Building and running

```bash
# Solve an instance (makespan objective, default settings)
cargo run --example jobshop --release -- instances/2x2.jsp

# Solve with a 30-second time limit, print statistics, and verbose output
cargo run --example jobshop --release -- -t 30s -s -v instances/6x6.jsp

# Minimise total completion time instead
cargo run --example jobshop --release -- --objective-type total-completion-time instances/6x6.jsp
```

Use the command `cargo run --example jobshop -- --help` to get more information about the available options.

## Running tests

The example has regression tests that parse and solve included instances.

```bash
cargo test --example jobshop
```

