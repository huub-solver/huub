var 1..5: x;
var 3..5: y;
solve :: int_search([x, y], first_fail, indomain_max, complete) satisfy;

constraint x != y;
