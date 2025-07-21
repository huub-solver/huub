var 1..5: x;
var 1..5: y;
solve :: int_search([x, y], input_order, indomain_min, complete) satisfy;

constraint x != y;
