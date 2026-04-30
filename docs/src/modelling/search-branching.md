# Search and Branching

Explain how search works in Huub, how to direct the search strategy, and how to find optimal solutions.

## How Huub Searches

Depth-first search with backjumping (How the solver performs depth-first search and backtracks when conflicts are detected) and directing search at each node (The choice between directing decisions through user-defined branchers or leaving it to the SAT solver's built-in heuristics (VSIDS)).

## User-Directed Search

Using the `intbrancher` and `boolbrancher`, setting variable and value selection strategies, and the ability to program your custom brancher as further specified in the Programming chapter.

## Warm starting with `WarmStartingBrancher`

How to initialize the search with a known partial or complete solution to guide the solver.

## Search Goals

What `Solver` method do you use to find any solution or to find optimal solutions.

## Search Tuning

Tuning solver behavior through configuration parameters, including setting the restart policy and other SAT solver-level options such as branching direction and other search and (pre/in)-processing settings.
