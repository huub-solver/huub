var 1..10: x;
var 1..10: y;

var bool: p;
var bool: q;

constraint p <-> x > 5;
constraint q <-> y > 5;

constraint x != y;

solve :: seq_search([
    bool_search([p, q], input_order, indomain_min, complete),
    int_search([x, y], input_order, indomain_max, complete)
]) satisfy;

output [assert(
    not fix(p) /\ not fix(q) /\ fix(x) = 5 /\ fix(y) = 4,
    "Did not follow search annotation",
    "x = \(x);\ny = \(y);\np = \(p);\nq = \(q);\n"
)];
