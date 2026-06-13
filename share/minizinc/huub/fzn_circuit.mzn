predicate huub_circuit(array [int] of var int: x, int: offset);

predicate fzn_circuit(array [int] of var int: x) =
  if length(x) = 0 then true
  else huub_circuit(x, min(index_set(x))) endif;
