var 1..20: x;
var 1..18: y;
solve :: int_search([x, y], anti_first_fail, indomain_median, complete) satisfy;

constraint x < y;

% output [assert(
%     fix(x) in 8..11 /\ fix(y) in 9..14,
%     "Did not follow search annotation",
%     "x = \(x);\ny = \(y);\n"
% )];
