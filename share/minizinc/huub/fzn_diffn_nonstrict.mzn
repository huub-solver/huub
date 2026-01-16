predicate huub_diffn_nonstrict_int(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
);

predicate fzn_diffn_nonstrict(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
) = huub_diffn_nonstrict_int(x, y, dx, dy);
