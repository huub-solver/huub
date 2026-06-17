var 1..20: x;
var 1..9: y;
solve :: int_search([x, y], first_fail, indomain_median, complete) satisfy;

constraint x > y;

% output [assert(
%     fix(x) in 10..14 /\ fix(y) in 3..6,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
