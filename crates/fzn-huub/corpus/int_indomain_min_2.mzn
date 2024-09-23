var 1..5: x;
var 1..3: y;
solve :: int_search([x, y], first_fail, indomain_min, complete) satisfy;

constraint x != y;
