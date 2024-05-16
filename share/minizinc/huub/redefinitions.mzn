include "nosets.mzn";

predicate bool_lt(var bool: a, var bool: b) = not a /\ b;
predicate bool_lt_imp(var bool: a, var bool: b, var bool: r) = r -> (not a /\ b);
predicate bool_lt_reif(var bool: a, var bool: b, var bool: r) = r = (not a /\ b);

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
