var 1..5: x;
var 1..5: y;
solve :: int_search([x, y], input_order, indomain_reverse_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 5 /\ fix(y) = 4,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
