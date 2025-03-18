predicate huub_diffn_nonstrict_k(
  array [int, int] of var int: box_posn,
  array [int, int] of var int: box_size,
);

predicate fzn_diffn_nonstrict_k(
  array [int, int] of var int: box_posn,
  array [int, int] of var int: box_size,
) =
    huub_diffn_nonstrict_k(box_posn, box_size);
