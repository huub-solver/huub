var 1..20: x;
var 6..12: y;
solve :: int_search([x, y], largest, indomain_median, complete) satisfy;

constraint x != y;

% output [assert(
%     fix(x) in 9..11 /\ fix(y) in 8..10,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
