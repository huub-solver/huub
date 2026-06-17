var 1..5: x;
var 1..3: y;
solve :: int_search([x, y], first_fail, indomain_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 2 /\ fix(y) = 1,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
