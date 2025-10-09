//! A collection of integration tests that open files containing FlatZinc JSON,
//! run the solver on the problem, and check the results.

#![expect(
	unused_crate_dependencies,
	reason = "only dependencies for testing are used in this file"
)]
mod helpers;

#[cfg(test)]
mod tests {
	use crate::helpers::{
		assert_all_optimal, assert_all_solutions, assert_first_solution, assert_optimal,
		assert_search_order, assert_unsat,
	};

	assert_all_solutions!(array_var_int_element);
	assert_all_solutions!(sudoku_p0);
	assert_all_solutions!(unification);
	assert_all_solutions!(unify_element_1);
	assert_all_solutions!(unify_element_2);
	assert_all_solutions!(unify_with_view_1);
	assert_all_solutions!(unify_with_view_2);
	assert_all_solutions!(unify_with_view_3);
	assert_all_solutions!(unify_with_view_4);

	assert_all_optimal!(simple_sum);

	assert_first_solution!(seq_search_1);
	assert_first_solution!(seq_search_2);
	assert_first_solution!(seq_search_3);
	assert_first_solution!(seq_search_4);
	assert_first_solution!(warm_start_fail);
	assert_first_solution!(warm_start_in_seq_search);
	assert_first_solution!(warm_start_success);

	assert_optimal!(unbounded);

	assert_search_order!(bool_indomain_max);
	assert_search_order!(bool_indomain_min);
	assert_search_order!(int_indomain_max_1);
	assert_search_order!(int_indomain_max_2);
	assert_search_order!(int_indomain_max_3);
	assert_search_order!(int_indomain_max_4);
	assert_search_order!(int_indomain_max_5);
	assert_search_order!(int_indomain_min_1);
	assert_search_order!(int_indomain_min_2);
	assert_search_order!(int_indomain_min_3);
	assert_search_order!(int_indomain_min_4);
	assert_search_order!(int_indomain_min_5);

	assert_unsat!(int_lin_eq_prop);

	// ../benches/fzn_huub_benchmarks
	assert_first_solution!(amaze3_2012_03_19);
	assert_first_solution!(steiner_t3_k4_N8);
	assert_first_solution!(steiner_t6_k6_N7);
	assert_first_solution!(sudoku_p48);

	assert_optimal!(ccmcp_3_20_0);
	assert_optimal!(rcpsp_01);
	assert_optimal!(rcpsp_02);
	assert_optimal!(rcpsp_03);
	assert_optimal!(mrcpsp_j10_10_1);
	assert_optimal!(mrcpsp_j10_10_2);
	assert_optimal!(mrcpsp_j10_10_3);
	assert_optimal!(jobshop_la02);
	assert_optimal!(jobshop_la03);
	assert_optimal!(jobshop_la04);
	assert_optimal!(jobshop_la05);
	assert_optimal!(jobshop_newspaper);
	assert_optimal!(peaceable_queens_n5_q3);
	assert_optimal!(portal_10_9_10);
	assert_optimal!(radiation_i6_9);
	assert_optimal!(radiation_i8_9);
	assert_optimal!(svrp_s4_v2_c3);
}
