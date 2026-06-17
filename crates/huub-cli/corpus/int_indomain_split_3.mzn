var 1..5: x;
var 1..5: y;
solve :: int_search([x, y], input_order, indomain_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 1 /\ fix(y) = 2,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
