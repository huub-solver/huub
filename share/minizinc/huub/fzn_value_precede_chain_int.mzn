predicate huub_value_precede_chain_int(array [int] of int: t, array [int] of var int: x);
predicate fzn_value_precede_chain_int(array [int] of int: t, array [int] of var int: x) =
	huub_value_precede_chain_int(t, x);
