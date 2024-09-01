include "nosets.mzn";

predicate bool_lt(var bool: a, var bool: b) = not a /\ b;
predicate bool_lt_imp(var bool: a, var bool: b, var bool: r) = r -> (not a /\ b);
predicate bool_lt_reif(var bool: a, var bool: b, var bool: r) = r = (not a /\ b);

predicate int_abs(var int: a, var int: b) = b = [a,-a][1 + (a < 0)];

predicate int_eq_imp(var int: a, var int: b, var bool: r);
predicate int_le_imp(var int: a, var int: b, var bool: r);
predicate int_ne_imp(var int: a, var int: b, var bool: r);

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
	a=(a div b)*b+z;
