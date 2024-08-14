mod helpers;

#[cfg(test)]
mod tests {
	use crate::helpers::{
		assert_all_solutions, assert_first_solution, assert_optimal, assert_search_order,
	};
	assert_all_solutions!(sudoku);
	assert_all_solutions!(unification);

	assert_all_solutions!(array_var_int_element);

	assert_all_solutions!(xor);

	assert_optimal!(jobshop);

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

	assert_first_solution!(seq_search_1);
	assert_first_solution!(seq_search_2);
	assert_first_solution!(seq_search_3);
	assert_first_solution!(seq_search_4);
}
