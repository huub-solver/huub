#![allow(clippy::tests_outside_test_module)]

mod helpers;

use helpers::{assert_all_solutions, assert_optimal};

assert_optimal!(jobshop, |sol: &str| {
	// Only optimal solution
	const OPT: &str = "t_end = 61;\nX_INTRODUCED_0_ = [0,30,54,22,32,47,0,28,45];";
	sol.contains(OPT)
});
assert_all_solutions!(sudoku);
assert_all_solutions!(unification);
