var 1..2: p;
var 1..3: q;
var 1..3: a;
var 1..3: b;
constraint p != q;
constraint q != a;
constraint q != b;
constraint a != b;
solve :: int_search([p, q, a, b], dom_w_deg, indomain_min, complete) satisfy;
