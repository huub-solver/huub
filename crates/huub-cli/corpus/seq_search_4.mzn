include "all_different.mzn";

var 1..10: w;
var 1..10: x;
var 1..10: y;
var 1..10: z;

var bool: p;
var bool: q;

constraint p <-> w < 5 /\ x > 5;
constraint q <-> y < 5 /\ z > 5;

constraint all_different([w, x, y, z]);

solve :: seq_search([
    seq_search([
      int_search([w, x], input_order, indomain_min, complete),
      bool_search([p, q], input_order, indomain_max, complete)
    ]),
    int_search([y, z], input_order, indomain_max, complete)
]) satisfy;
