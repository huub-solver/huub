include "cumulative.mzn";
array[1..4] of var 0..2: s;
constraint cumulative(s, [2, 1, 2, 1], [1, 2, 1, 1], 2);
solve satisfy;
