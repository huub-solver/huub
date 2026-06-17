var {1, 2, 3}: x;
var {1, 5, 6}: y;
constraint x != y;
solve :: int_search([x, y], max_regret, indomain_min, complete) satisfy;
