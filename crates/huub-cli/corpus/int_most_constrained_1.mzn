var 1..3: x;
var 1..3: y;
var 1..3: z;
constraint x != z;
constraint y != z;
solve :: int_search([x, y, z], most_constrained, indomain_min, complete) satisfy;
