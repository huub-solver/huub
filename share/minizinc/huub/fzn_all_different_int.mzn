predicate huub_all_different_int(array[int] of var int: x);
predicate fzn_all_different_int(array[int] of var int: x) =
	huub_all_different_int(x);
