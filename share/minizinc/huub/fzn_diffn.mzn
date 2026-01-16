predicate huub_diffn_int(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
);

predicate fzn_diffn(
	array [int] of var int: x,
	array [int] of var int: y,
	array [int] of var int: dx,
	array [int] of var int: dy,
) = huub_diffn_int(x, y, dx, dy);
