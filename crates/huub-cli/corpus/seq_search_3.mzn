var 1..9: a;
var 1..5: b;
var 1..3: c;
var 1..8: d;

constraint a > b <-> c > d;

solve :: seq_search([
    int_search([a, b], anti_first_fail, indomain_min, complete),
    int_search([c, d], largest, indomain_max, complete)
]) satisfy;

output [assert(
    fix([a, b, c, d]) = [1, 1, 3, 8],
    "Did not follow search annotation",
    "a = \(a);\nb = \(b);\nc = \(c);\nd = \(d);\n"
)];
