var 1..9: x;
var 1..9: y;
solve :: int_search([x, y], input_order, indomain_median, complete) satisfy;

constraint x < y;

% output [assert(
%     fix(x) in 4..5 /\ fix(y) in 7..8,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
