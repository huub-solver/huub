include "seq_precede_chain.mzn";

predicate huub_value_precede_chain_int(array [int] of int: t, array [int] of var int: x);
predicate fzn_value_precede_chain_int(array [int] of int: t, array [int] of var int: x) =
	if length(t) = 0 then
		true
	elseif min(index_set(t)) = 1 /\
		forall (i in index_set(t)) (t[i] = i) /\
		max(t) = ub_array(x) then
		seq_precede_chain(x)
	else
		huub_value_precede_chain_int(t, x)
	endif;
