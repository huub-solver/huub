var 1..5: x;
var 3..5: y;
solve :: int_search([x, y], first_fail, indomain_reverse_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 4 /\ fix(y) = 5,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
