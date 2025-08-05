predicate huub_seq_precede_chain_int(array[int] of var int: x);
predicate fzn_seq_precede_chain_int(array[int] of var int: x) =
	huub_seq_precede_chain_int(x);
