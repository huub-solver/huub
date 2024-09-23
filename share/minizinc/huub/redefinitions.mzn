include "nosets.mzn";

predicate bool_lt(var bool: a, var bool: b) = not a /\ b;
predicate bool_lt_imp(var bool: a, var bool: b, var bool: r) = r -> (not a /\ b);
predicate bool_lt_reif(var bool: a, var bool: b, var bool: r) = r = (not a /\ b);

%%% NOTE: Rewrite simple integer comparison predicates to distinguish between
% views (that already have a literal representation), and actual constraints
% that have to be enforced and could be (more efficiently) half-reified.

predicate huub_int_eq(var int: a, var int: b);
predicate huub_int_eq_reif(var int: a, var int: b, var bool: r);
predicate huub_int_eq_imp(var int: a, var int: b, var bool: r);
predicate huub_int_eq_view(var int: x, int: i);
predicate huub_int_eq_view_reif(var int: x, int: i, var bool: r);
predicate int_eq(var int: a, var int: b) = huub_int_eq(a, b);
predicate int_eq(var int: a, int: b) = huub_int_eq_view(a, b);
predicate int_eq(int: a, var int: b) = huub_int_eq_view(b, a);

predicate huub_int_le(var int: a, var int: b);
predicate huub_int_le_reif(var int: a, var int: b, var bool: r);
predicate huub_int_le_imp(var int: a, var int: b, var bool: r);
predicate huub_int_ge_view(var int: x, int: i);
predicate huub_int_ge_view_reif(var int: x, int: i, var bool: r);
predicate huub_int_le_view(var int: x, int: i);
predicate huub_int_le_view_reif(var int: x, int: i, var bool: r);
predicate int_le(var int: a, var int: b) = huub_int_le(a, b);
predicate int_le(var int: a, int: b) = huub_int_le_view(a, b);
predicate int_le(int: a, var int: b) = huub_int_ge_view(b, a);

predicate huub_int_ne(var int: a, var int: b);
predicate huub_int_ne_reif(var int: a, var int: b, var bool: r);
predicate huub_int_ne_imp(var int: a, var int: b, var bool: r);
predicate huub_int_ne_view(var int: x, int: i);
predicate huub_int_ne_view_reif(var int: x, int: i, var bool: r);
predicate int_ne(var int: a, var int: b) = huub_int_ne(a, b);
predicate int_ne(var int: a, int: b) = huub_int_ne_view(a, b);
predicate int_ne(int: a, var int: b) = huub_int_ne_view(b, a);

predicate int_lin_eq_imp(
	array [int] of int: as,
	array [int] of var int: bs,
	int: c,
	var bool: r
);
predicate int_lin_le_imp(
	array [int] of int: as,
	array [int] of var int: bs,
	int: c,
	var bool: r
);
predicate int_lin_ne_imp(
	array [int] of int: as,
	array [int] of var int: bs,
	int: c,
	var bool: r
);

predicate int_mod(var int: a, var int: b, var int: c) =
	a=(a div b)*b+c;

%%% NOTE: because of a mistake in the MiniZinc standard library, the
% `warm_start` annotation is overloaded on the FlatZinc level, the following
% definitions disambiguate these annotations within Huub.

annotation warm_start_bool(array[int] of var bool: x, array[int] of bool: v);
annotation warm_start(array[int] of var bool: x, array[int] of bool: v) = warm_start_bool(x, v);
annotation warm_start_int(array[int] of var int: x, array[int] of int: v);
annotation warm_start(array[int] of var int: x, array[int] of int: v) = warm_start_int(x, v);
annotation warm_start_float(array[int] of var float: x, array[int] of float: v);
annotation warm_start(array[int] of var float: x, array[int] of float: v) = warm_start_float(x, v);
