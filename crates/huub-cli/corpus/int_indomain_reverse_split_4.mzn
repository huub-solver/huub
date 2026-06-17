var 1..6: x;
var 1..5: y;
solve :: int_search([x, y], largest, indomain_reverse_split, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) = 6 /\ fix(y) = 5,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
