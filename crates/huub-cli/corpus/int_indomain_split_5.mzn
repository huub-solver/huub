var 3..5: x;
var 1..5: y;
solve :: int_search([x, y], smallest, indomain_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 3 /\ fix(y) = 1,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
