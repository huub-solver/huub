% Semantics of the `huub_*` predicates that can occur in the model that Huub
% emits at the start of search (the `.fzt` model of the preprocessing trace),
% or in the FlatZinc that Huub receives.
%
% The preprocessing checker treats these predicates as opaque, but its
% brute-force tier needs their meaning, e.g. to negate them. This file gives
% each of them a definition in terms of the MiniZinc standard library. Every
% `huub_*` spelling that Huub can emit must be defined here; the list of
% spellings is `spelling::ALL` in `crates/huub/src/model/preprocess.rs`, and a
% unit test checks that each has a definition. The spellings in which Huub only
% receives constraints (`huub_array_int_maximum` and `huub_regular`) are
% defined as well, since they occur in the checker's obligations about the
% received model.
%
% These definitions state what the constraints mean, and are not the
% definitions that Huub's MiniZinc library (`share/minizinc/huub`) uses to
% compile for Huub.

include "all_different.mzn";
include "circuit.mzn";
include "cumulative.mzn";
include "diffn.mzn";
include "diffn_k.mzn";
include "diffn_nonstrict.mzn";
include "diffn_nonstrict_k.mzn";
include "regular.mzn";
include "disjunctive_strict.mzn";
include "seq_precede_chain.mzn";
include "subcircuit.mzn";
include "table.mzn";
include "value_precede_chain.mzn";

predicate huub_all_different_int(array [int] of var int: x) = all_different(x);

% The literals that search assumes to hold. Huub enforces them as assumptions
% of the SAT solver rather than as constraints, to report the assumptions that
% cause unsatisfiability, but the solutions it finds satisfy all of them.
predicate huub_assume(array [int] of var bool: b) = forall(b);

predicate huub_array_int_maximum(var int: m, array [int] of var int: x) = m = max(x);

predicate huub_array_int_minimum(var int: m, array [int] of var int: x) = m = min(x);

% The clause of the positive literals `as` and the negative literals `bs` holds
% if and only if `r` holds.
predicate huub_bool_clause_reif(
	array [int] of var bool: as,
	array [int] of var bool: bs,
	var bool: r,
) = r <-> (exists(as) \/ exists(b in bs)(not b));

% The successors `x` form a single cycle, where the nodes are numbered from
% `offset`.
predicate huub_circuit(array [int] of var int: x, int: offset) =
	let {
		int: n = length(x);
	} in n = 0 \/ circuit(array1d(1..n, [x[i] - offset + 1 | i in index_set(x)]));

predicate huub_cumulative(
	array [int] of var int: s,
	array [int] of var int: d,
	array [int] of var int: r,
	var int: b,
) = cumulative(s, d, r, b);

predicate huub_diffn_int(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
) = diffn(x, y, dx, dy);

% The boxes are given object-major: the coordinates of box `i` in `dimensions`
% dimensions are consecutive.
predicate huub_diffn_k_int(
	array [int] of var int: box_posn,
	array [int] of var int: box_size,
	int: dimensions,
) =
	let {
		int: n = length(box_posn) div dimensions;
	} in diffn_k(
		array2d(1..n, 1..dimensions, box_posn),
		array2d(1..n, 1..dimensions, box_size),
	);

predicate huub_diffn_nonstrict_int(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
) = diffn_nonstrict(x, y, dx, dy);

predicate huub_diffn_nonstrict_k_int(
	array [int] of var int: box_posn,
	array [int] of var int: box_size,
	int: dimensions,
) =
	let {
		int: n = length(box_posn) div dimensions;
	} in diffn_nonstrict_k(
		array2d(1..n, 1..dimensions, box_posn),
		array2d(1..n, 1..dimensions, box_size),
	);

predicate huub_disjunctive_strict(array [int] of var int: s, array [int] of int: d) =
	disjunctive_strict(s, d);

% A propositional formula over the Boolean terms `atoms`, encoded in the
% integer array `ops`, in which every node occupies consecutive positions, and
% the root is at position 1. A node is one of:
%
% - `[0, i]`: the `i`-th element of `atoms`,
% - `[1, c]`: the negation of the node at position `c`,
% - `[2, n, c1, ..., cn]`: the conjunction of the nodes at positions `c1..cn`,
% - `[3, n, c1, ..., cn]`: their disjunction,
% - `[4, n, c1, ..., cn]`: whether an odd number of them holds,
% - `[5, n, c1, ..., cn]`: whether they are all equal,
% - `[6, a, b]`: the implication from node `a` to node `b`,
% - `[7, c, t, e]`: if node `c` holds then node `t`, else node `e`.
predicate huub_formula(array [int] of int: ops, array [int] of var bool: atoms) =
	huub_formula_node(ops, array1d(1..length(atoms), atoms), 1);

function var bool: huub_formula_node(
	array [int] of int: ops,
	array [int] of var bool: atoms,
	int: p,
) =
	if ops[p] = 0 then
		atoms[ops[p + 1]]
	elseif ops[p] = 1 then
		not huub_formula_node(ops, atoms, ops[p + 1])
	elseif ops[p] = 2 then
		forall(k in 1..ops[p + 1])(huub_formula_node(ops, atoms, ops[p + 1 + k]))
	elseif ops[p] = 3 then
		exists(k in 1..ops[p + 1])(huub_formula_node(ops, atoms, ops[p + 1 + k]))
	elseif ops[p] = 4 then
		xorall([huub_formula_node(ops, atoms, ops[p + 1 + k]) | k in 1..ops[p + 1]])
	elseif ops[p] = 5 then
		forall(k in 2..ops[p + 1])(
			huub_formula_node(ops, atoms, ops[p + 2])
				= huub_formula_node(ops, atoms, ops[p + 1 + k])
		)
	elseif ops[p] = 6 then
		huub_formula_node(ops, atoms, ops[p + 1]) -> huub_formula_node(ops, atoms, ops[p + 2])
	else
		let {
			var bool: c = huub_formula_node(ops, atoms, ops[p + 1]);
		} in (c -> huub_formula_node(ops, atoms, ops[p + 2]))
			/\ (not c -> huub_formula_node(ops, atoms, ops[p + 3]))
	endif;

% The transition table `d` of the automaton with `q` states and `s` input
% values is given row-major.
predicate huub_regular(
	array [int] of var int: x,
	int: q,
	int: s,
	array [int] of int: d,
	int: q0,
	set of int: f,
) = regular(x, q, s, array2d(1..q, 1..s, d), q0, f);

predicate huub_seq_precede_chain_int(array [int] of var int: x) = seq_precede_chain(x);

% The successors `x` form a single cycle among the nodes that are not their
% own successor, where the nodes are numbered from `offset`.
predicate huub_subcircuit(array [int] of var int: x, int: offset) =
	let {
		int: n = length(x);
	} in n = 0 \/ subcircuit(array1d(1..n, [x[i] - offset + 1 | i in index_set(x)]));

% The table `t` is given row-major, with one column per variable of `x`.
predicate huub_table_int(array [int] of var int: x, array [int] of int: t) =
	let {
		int: n = length(x);
	} in table(array1d(1..n, x), array2d(1..length(t) div n, 1..n, t));

predicate huub_value_precede_chain_int(array [int] of int: t, array [int] of var int: x) =
	value_precede_chain(t, x);
