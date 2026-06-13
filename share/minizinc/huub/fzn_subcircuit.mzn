predicate huub_subcircuit(array [int] of var int: x, int: offset);

predicate fzn_subcircuit(array [int] of var int: x) =
  if length(x) = 0 then true
  else huub_subcircuit(x, min(index_set(x))) endif;
