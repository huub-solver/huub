//! A Benchmarking framework for the command line huub solver.
//!
//! Note that these benchmarks run through the full solver, providing the
//! instances as file input, and reading the output from its output stream. The
//! total time taken is repeatedly measured.
#![expect(
	unused_crate_dependencies,
	reason = "only dependencies for benchmarking are used in this file"
)]

#[path = "../tests/helpers/mod.rs"]
mod helpers;

use std::path::PathBuf;

use expect_test::expect_file;

use crate::helpers::check_final;

const OPTIMIZATION_INSTANCES: &[&str] = &[
	"ccmcp_3_20_0",
	"rcpsp_01",
	"rcpsp_02",
	"rcpsp_03",
	"mrcpsp_j10_10_1",
	"mrcpsp_j10_10_2",
	"mrcpsp_j10_10_3",
	"jobshop_la02",
	"jobshop_la03",
	"jobshop_la04",
	"jobshop_la05",
	"jobshop_newspaper",
	"peaceable_queens_n5_q3",
	"portal_10_9_10",
	"radiation_i6_9",
	"radiation_i8_9",
	"svrp_s4_v2_c3",
];

const SATISFACTION_INSTANCES: &[&str] = &[
	"amaze3_2012_03_19",
	"steiner_t3_k4_N8",
	"steiner_t6_k6_N7",
	"sudoku_p48",
];

/// Entry point for the executable that runs the benchmarks.
fn main() {
	// Run registered benchmarks.
	divan::main();
}

/// Benchmark an optimization problem (finding the optimal solution).
///
/// Note that it is assumed that the solver will always find the same optimal
/// solution, which is then checked.
#[divan::bench(args = OPTIMIZATION_INSTANCES)]
fn optimization(instance: &str) {
	let base = PathBuf::from("./corpus/").join(instance);
	let fzn = base.with_extension("fzn.json");
	let sol = base.with_extension("sol").canonicalize().unwrap();
	check_final(&fzn, true, expect_file![&sol]);
}

/// Benchmark a satisfaction problem (finding any correct solution).
///
/// Note that it is assumed that the solver will always find the same solution,
/// which is then checked.
#[divan::bench(args = SATISFACTION_INSTANCES)]
fn satisfaction(instance: &str) {
	let base = PathBuf::from("./corpus/").join(instance);
	let fzn = base.with_extension("fzn.json");
	let sol = base.with_extension("sol").canonicalize().unwrap();
	check_final(&fzn, false, expect_file![&sol]);
}
