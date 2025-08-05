var bool: x;
var bool: y;

constraint x != y;

solve :: bool_search([x, y], input_order, indomain_max, complete) satisfy;
