predicate huub_circuit(array[int] of var int: x);
predicate fzn_circuit(array[int] of var int: x) =
	huub_circuit(x);
