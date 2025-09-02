var 1..10: x;
var 1..10: y;

var bool: p;
var bool: q;

constraint p <-> x > 5;
constraint q <-> y > 5;

constraint x != y;

solve :: seq_search([
    bool_search([p, q], input_order, indomain_max, complete),
    int_search([x, y], input_order, indomain_min, complete)
]) satisfy;

output [assert(
    fix(p) /\ fix(q) /\ fix(x) = 6 /\ fix(y) = 7,
    "Did not follow search annotation",
    "x = \(x);\ny = \(y);\np = \(p);\nq = \(q);\n"
)];
