# Huub Modelling Chapter - Outline

This document outlines the structure for the Huub modelling documentation chapter. It is based on the proven educational structure from the Gecode "Modeling and Programming with Gecode" book, adapted specifically for Huub's lazy clause generation approach.

## Structure Overview

The modelling chapter is organized into 5 parts that progress from basic to advanced concepts:

---

## Part 1: A first Huub model

**Goal:** Help users write and run their first Huub model.

- **First Huub model** — A simple introductory example with decision variables and constraints
- **Running the solver** — How to execute the model and retrieve results

**Note:** Installation and setup are covered in the Introduction chapter.

---

## Part 2: Decision variables

**Goal:** Teach users how to create and work with decision variables, including Huub-specific concepts.

- **Boolean decision variables** — Creating and working with Boolean decision variables
- **Integer decision variables** — Creating integer decision variables and configuring bounds, including understanding min/max bounds and domain representation
- **Solution queries** — Retrieving decision variable values and domain information after solving
- **View vs Decision** — Understanding the distinction between view representations and decision variables (Huub-specific)

---

## Part 3: Constraints

**Goal:** Teach how to model problems using constraints, from the modeling mindset through to building complete constraint models.

- **The constraint modeling mindset** — How to think about encoding a problem as constraints (what are we constraining, why, how do we express it?)
- **Using the builder pattern** — The mechanics of posting constraints in Huub
- **Building constraint models** — From basic relational constraints through arithmetic and logical constraints to global and aggregation constraints, with guidance on choosing the right formulation based on solver performance
- **Modeling common patterns** — Assignment problems, scheduling problems, and configuration problems with concrete examples
- **Choosing formulations wisely** — The principle that smaller custom variants shouldn't be created unless they represent a natural reasoning concept

---

## Part 5: Search, Branching, and Optimization

**Goal:** Explain how search works in Huub, how to direct the search strategy, and how to find optimal solutions.

- **How Huub Searches** — Depth-first search with backjumping (How the solver performs depth-first search and backtracks when conflicts are detected) and directing search at each node (The choice between directing decisions through user-defined branchers or leaving it to the SAT solver's built-in heuristics (VSIDS))
- **User-Directed Search** — Using the `intbrancher` and `boolbrancher`, setting Variable and value selection strategies, note you can program your custom brancher as further specified in another chapter.
- **Warm starting with `WarmStartingBrancher`** — How to initialize the search with a known partial or complete solution to guide the solver
- **Search Goals** — What `Solver` method do you use to *find any solution* or to *finding optimal solutions*
- **Search Tuning** — Tuning solver behavior through configuration parameters, including setting the restart policy and other SAT solver-level options such as branching direction and other search and (pre/in)-processing settings.
