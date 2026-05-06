# What is Huub?

Huub is an efficient library for developing constraint-based decision or optimization systems and applications with learning capabilities.
It combines the modelling strengths of constraint programming (CP) with the learning and proof machinery of Boolean satisfiability (SAT) solving.
Huub belongs to the solving family generally referred to as CP+SAT or Lazy Clause Generation (LCG) solvers.

Constraint programming and SAT solving come from different traditions, and each has its own strengths.
Constraint programming is a natural fit for modelling structured combinatorial problems: abstract decision variable types, complex constraints that capture patterns from problem classes including scheduling, packing, and configuration, and explicit search control.
SAT solving, on the other hand, excels at conflict analysis, clause learning, restart-based search, and extracting strong guidance from failure.
A CP+SAT solver aims to combine these two worlds.
Rather than choosing between high-level modelling power and conflict-driven reasoning, it uses both.

This viewpoint is central to Huub.
Huub is not merely a SAT solver with a thin modelling front-end, and it is not merely a classical constraint programming engine with a few SAT-inspired heuristics attached to it.
Instead, it is meant to be a solver in which propagation, explanation, clause learning, and search all play first-class roles.

In practice, this means that Huub works with decision variables and constraints that look familiar to a constraint programmer, while also maintaining the ability to explain deductions and failures in a form that can be given to a SAT engine.
When the solver encounters a conflict, it does not simply backtrack and forget what happened.
It analyses the failure, learns information from it, and uses that information to avoid making essentially the same mistake again.

This combination matters because combinatorial optimization problems are often too rich to encode comfortably as pure SAT, but also too difficult to solve well using propagation and chronological backtracking alone.
A CP+SAT solver can exploit the structure of high-level constraints while still benefitting from the learning mechanisms that have made modern SAT solving so effective.

Huub is also intended to be studied and extended.
The goal is not only to solve models well, but also to provide a clean and modular implementation that is suitable for practical use, experimentation with solver design, and implementation of new ideas.

The rest of this section serves as a first orientation.
It explains the two main ways in which Huub can be used, sketches the architecture of the system, and points to the main project resources that accompany the text.

## Using Huub

There are two main ways to use Huub, and it is helpful to distinguish them from the beginning because they lead into different parts of the documentation.
Some readers will approach Huub primarily as a solver.
They want to write decision or optimization models, run them, and understand how to obtain good solutions or good proofs of infeasibility.
Other readers will approach Huub as a library.
They want to construct models programmatically, integrate solving into an application, or understand and extend the internal machinery of the solver.

Both workflows are important, and both are supported by the same project.
But they answer different questions:
- If your question is “How do I formulate my problem and solve it with Huub?”, then you might best use Huub through [MiniZinc](https://www.minizinc.org/).
- If your question is “How do I integrate Huub into my application?” or “How do I extend Huub's behavior?”, then you should explore how to use Huub as a Rust library.

### From MiniZinc

If you are not planning on integrating Huub directly in your application or extending it, then [MiniZinc](https://www.minizinc.org/) is the natural starting point for most users.
MiniZinc provides a high-level modelling language with rich support for different types of decision variables, constraints, functional programming, and solver-independent experimentation.
If your main goal is to express and solve a combinatorial problem well, then this is usually the most convenient route into Huub.

In this workflow, you write a MiniZinc model, possibly together with instance data.
MiniZinc then compiles the model, checks it, and flattens it into Huub solver input.
Huub receives that input, constructs its internal representation of the problem, and then begins solving.
This mode of use has several practical advantages.

1. It gives access to Huub without requiring you to program directly against the Rust API.
  If you already know MiniZinc, you can begin by modelling immediately rather than by learning the structure of the crate.
2. It separates modelling concerns from implementation concerns.
  You can focus on which decision variables and constraints best capture your problem, while MiniZinc and Huub take care of rewriting constraints and decision types not directly supported by Huub.
3. It makes comparison easy.
  Because MiniZinc supports multiple solvers, you can test the same model with Huub and with other backends.
  This is often useful both for benchmarking and for understanding where Huub's CP+SAT behavior is especially effective.

This book is written with that modelling perspective in mind.
Even when later chapters discuss internals, the ultimate purpose is still to help the reader understand how solver behavior and model structure interact.

If this is how you want to use Huub, then continue to “[Using Huub from MiniZinc](./using-huub-from-minizinc.md)”.
It describes how to install Huub as a MiniZinc solver, and the additional functionality that Huub makes available from its MiniZinc library.

### From Rust

Huub is designed to be used as a Rust crate.
This is the right way to use it if you want to construct decision or optimization models programmatically, integrate solving into a Rust application, or work on solver components such as propagators, branchers, and search.
Using Huub from Rust gives much more direct control over the solving process.
You define how you build, transform, and solve the model inside your Rust program.
This is useful when the model is naturally generated by code, when solving must be embedded into a larger software system, or when you want to extend or fine-tune Huub's capabilities.

The installation instructions for the Rust crate can be found in “[Installing the Huub crate](./installing-the-huub-crate.md)”.
The remainder of the book, apart from “Using Huub from MiniZinc”, assumes that the reader is willing to engage with Huub as a Rust code base.

## Architecture

At a high level, the Huub library is split into two different layers: a modelling layer and a solver layer.
The modelling layer is responsible for describing a problem in a convenient way for the user, such that it can be understood and solved by the Huub library.
At this level, the concern is the meaning of the problem: what the decisions are and what relationships must hold.
When using this layer, a user will create a `Model` object that provides methods to define decision variables and constraints, but in a way where their underlying structure can easily be changed.
For example, constraints can be rewritten and the representation of decision variables can change from one type to another.

The solving layer, on the other hand, is designed for an efficient search process to take place.
This efficiency requires the `Solver` object, created in this layer, to be more rigid.
Constraints and decision variables will remain in the same shape for the full duration of the `Solver`'s lifetime.
Notably, this is also the layer that concerns itself with the “search goal”, such as maximizing or minimizing a certain variable, and the search/branching order, e.g. which values for which decision variables will be tried first.

This distinction is useful because the flexible modelling representation is a good place for preprocessing and simplification.
At the `Model` level, Huub can simplify constraints, unify different decision variables, and perform other preprocessing techniques that transform the problem into a form that is more convenient for solving.
Only once this process is complete does Huub create the more rigid `Solver` representation that will actually be searched.

The remaining chapters of the book can largely be divided according to the layers in the architecture.
The “Modelling” chapter is largely concerned with the modelling layer, discussing how to express and solve problems in Huub from a `Model` object.
The “Programming ...” chapters are mainly concerned with the solver layer, where propagation, branching, explanations, and search are implemented.

## Further references

This book is accompanied by code, examples, and external reference material.
Readers will typically move back and forth between the text and those resources, so it is useful to know from the beginning where they are.

**Examples.** The examples used in this documentation can be found in the [Huub repository](https://github.com/huub-solver/huub).
In particular, the Rust examples live under [`crates/huub/examples`](https://github.com/huub-solver/huub/tree/develop/crates/huub/examples/).
When an example in the text is based on runnable code, this is the first place to look.
Reading the example source alongside the surrounding discussion is often the quickest way to connect the ideas in the book with concrete solver usage.

**API Reference** The API reference for the Rust crate is available on [docs.rs](https://docs.rs/huub/latest/huub/) or locally using [`cargo doc`](https://doc.rust-lang.org/cargo/commands/cargo-doc.html).
The API reference serves a different purpose from this book.
The book is organized pedagogically: it introduces concepts in an order intended to be useful for learning.
The API reference is organized by modules, types, and functions.
When you already know what functionality you need, then the API reference is the best way to inspect the signatures and item-level documentation.
When you want to understand why a concept exists, how pieces fit together, or how to approach a modelling or implementation task, the book should usually be your first stop.

**Community Discussions** For help, questions, and discussion, use the [GitHub Discussions](https://github.com/huub-solver/huub/discussions).
This is the best place to ask questions about modelling with Huub, practical solver use, the design of the API, and the behavior of the implementation.
It is also the natural place to discuss documentation gaps, modelling idioms, and ideas for future extensions.
