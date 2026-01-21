predicate fzn_cumulative(
	array[int] of var int: s,
	array[int] of var int: d,
	array[int] of var int: r,
	var int: b,
) = assert(
		index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
		"cumulative: the 3 array arguments must have identical index sets",
	)
	/\ forall(i in index_set(d))(d[i] >= 0 /\ r[i] >= 0)
	/\	huub_cumulative(s, d, r, b);

predicate huub_cumulative(array[int] of var int: s, array[int] of var int: d, array[int] of var int: r, var int: b);
