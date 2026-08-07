include "globals.mzn";

% A 1-based `circuit` and a 0-based `subcircuit`, so both offsets reach the
% `huub_circuit` / `huub_subcircuit` decoding path.
array [1..4] of var 1..4: x;
array [0..2] of var 0..2: y;

constraint circuit(x);
constraint subcircuit(y);

% Node 1 does not follow node 0, and node 0 lies on the sub-cycle.
constraint x[1] != 2;
constraint y[0] != 0;

solve satisfy;
