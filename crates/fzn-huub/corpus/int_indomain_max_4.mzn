var 1..5: x;
var 1..10: y;
solve :: int_search([x, y], largest, indomain_max, complete) satisfy;

constraint x != y;
