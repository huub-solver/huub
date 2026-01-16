predicate huub_diffn_nonstrict_k_int(
	array [int] of var int: box_posn,
	array [int] of var int: box_size,
	int: dimensions
);

predicate fzn_diffn_nonstrict_k(
	array [int, int] of var int: box_posn,
	array [int, int] of var int: box_size
) = let {
		int: dimensions = max(index_set_2of2(box_posn));
	} in huub_diffn_nonstrict_k_int(array1d(box_posn), array1d(box_size), dimensions);
