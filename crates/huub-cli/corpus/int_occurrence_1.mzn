var 1..3: x;
var 1..3: y;
var 1..3: z;
constraint x != y;
constraint y != z;
solve :: int_search([x, y, z], occurrence, indomain_min, complete) satisfy;
