predicate huub_diffn_k_int(
  array [int, int] of var int: box_posn,
  array [int, int] of var int: box_size,
);

predicate fzn_diffn_k(
  array [int, int] of var int: box_posn,
  array [int, int] of var int: box_size,
) = 
    huub_diffn_k_int(box_posn, box_size);
