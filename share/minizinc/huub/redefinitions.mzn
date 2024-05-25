include "nosets.mzn";

predicate bool_lt(var bool: a, var bool: b) = not a /\ b;
predicate bool_lt_imp(var bool: a, var bool: b, var bool: r) = r -> (not a /\ b);
predicate bool_lt_reif(var bool: a, var bool: b, var bool: r) = r = (not a /\ b);

% Division and modulo helper function: x = y * q + r
function tuple(var int, var int): div_mod(var int: x, var int: y) =
let {
	set of int: dom_q =
		if lb(y)*ub(y)>0 then
			let {
				set of int: EP = { ub(x) div ub(y), ub(x) div lb(y), lb(x) div ub(y), lb(x) div lb(y) };
			} in min(EP)..max(EP)
		else
			let {
				int: mm = max(abs(lb(x)), abs(ub(x)));
			} in -mm..mm
		endif;
	var dom_q: q;
	int: by = max(abs(lb(y)), abs(ub(y)));
	var -by+1..by-1: r;
	constraint x = y * q + r;
	constraint (x >= 0) -> (r >= 0);
	constraint (x < 0) -> (r <= 0);
	var 1..max(abs(lb(y)), abs(ub(y))): w = abs(y),
	constraint w > r /\ w > -r,
} in (q, r);

predicate int_abs(var int: a, var int: b) = b = [a,-a][1 + (a < 0)];

predicate int_div(var int: a, var int: b, var int: c) =
let {
	any: tup = div_mod(a, b);
} in c = tup.1;

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
let {
	any: tup = div_mod(a, b);
} in c = tup.2;
