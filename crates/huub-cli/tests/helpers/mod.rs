//! Shared helpers for the CLI integration tests and benchmarks.

#![expect(
	unused_imports,
	reason = "module is shared between benchmarks and integration tests"
)]

/// Define an integration test that checks every optimal solution emitted by the
/// solver.
macro_rules! assert_all_optimal {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_optimal(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				true,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}

/// Define an integration test that checks every solution emitted by the solver.
macro_rules! assert_all_solutions {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_solutions(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				true,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}

/// Define an integration test that checks the UNSAT core emitted by the solver.
macro_rules! assert_core {
	($file:ident, $status:expr, $core:expr) => {
		#[test]
		fn $file() {
			$crate::helpers::check_core(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				$status,
				$core,
			)
		}
	};
}

/// Define an integration test that checks only the first solution emitted by
/// the solver.
macro_rules! assert_first_solution {
	($file:ident) => {
		#[test]
		#[allow(non_snake_case, reason = "depends on data filename")]
		fn $file() {
			$crate::helpers::check_final(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				false,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}

/// Define an integration test that checks the final optimal solution emitted by
/// the solver.
macro_rules! assert_optimal {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_final(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				true,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}

/// Define an integration test that checks the solver's solution order exactly.
macro_rules! assert_search_order {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_solutions(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				false,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}

/// Define an integration test that checks an instance is unsatisfiable.
macro_rules! assert_unsat {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_unsat(&std::path::PathBuf::from(format!(
				"./corpus/{}.fzn.json",
				stringify!($file)
			)))
		}
	};
}

use std::{
	env::{consts::EXE_SUFFIX, current_exe, var_os, vars},
	ffi::OsString,
	iter,
	path::{Path, PathBuf},
	process::Command,
};

pub(crate) use assert_all_optimal;
pub(crate) use assert_all_solutions;
pub(crate) use assert_core;
pub(crate) use assert_first_solution;
pub(crate) use assert_optimal;
pub(crate) use assert_search_order;
pub(crate) use assert_unsat;
use expect_test::ExpectFile;
use huub_cli::Cli;

/// The FlatZinc marker that terminates a complete search.
pub(crate) const FZN_COMPLETE: &str = "==========\n";

/// The FlatZinc marker that separates consecutive solutions.
const FZN_SEPARATOR: &str = "----------\n";

/// The FlatZinc marker that reports an unsatisfiable instance.
pub(crate) const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

/// Run the solver in all-optimal mode and compare the emitted solutions against
/// an expectation.
pub(crate) fn check_all_optimal(file: &Path, sort: bool, solns: ExpectFile) {
	let args: &[OsString] = &["--all-optimal".into(), file.into()];
	let output = run_solver(args);
	let stdout = String::from_utf8(output).unwrap();
	assert!(!stdout.is_empty(), "Solver did not produce any output");
	let mut stdout: Vec<&str> = stdout.split(FZN_SEPARATOR).collect();
	let marker = stdout.pop().unwrap(); // complete marker
	if sort {
		stdout.sort();
	}
	stdout.push(marker);
	let stdout = stdout.join(FZN_SEPARATOR);
	solns.assert_eq(&stdout);
}

/// Run the solver in all-solutions mode and compare the emitted solutions
/// against an expectation.
pub(crate) fn check_all_solutions(file: &Path, sort: bool, solns: ExpectFile) {
	let args: &[OsString] = &["--all-solutions".into(), file.into()];
	let output = run_solver(args);
	let stdout = String::from_utf8(output).unwrap();
	assert!(!stdout.is_empty(), "Solver did not produce any output");
	let mut stdout: Vec<&str> = stdout.split(FZN_SEPARATOR).collect();
	let marker = stdout.pop().unwrap(); // complete marker
	if sort {
		stdout.sort();
	}
	stdout.push(marker);
	let stdout = stdout.join(FZN_SEPARATOR);
	solns.assert_eq(&stdout);
}

/// Run the solver once and assert that the FlatZinc output contains a
/// `%%%mzn-core: [<expected>]` line. The check is order-insensitive: the
/// reported core is split on `, ` and compared to `expected` as multisets.
///
/// `expected_status_marker` must equal one of [`FZN_UNSATISFIABLE`] or
/// [`FZN_COMPLETE`]; the solver's final line is verified to match it so the
/// test fails loudly if the model becomes satisfiable for an unrelated reason.
pub(crate) fn check_core(file: &Path, expected_status_marker: &str, expected_core: &[&str]) {
	let output = run_solver(vec![file.as_os_str()]);
	let stdout = String::from_utf8(output).unwrap();
	let core_line = stdout
		.lines()
		.find(|l| l.starts_with("%%%mzn-core: "))
		.unwrap_or_else(|| panic!("solver did not emit a `%%%mzn-core:` line:\n{stdout}"));
	let body = core_line
		.trim_start_matches("%%%mzn-core: ")
		.trim_start_matches('[')
		.trim_end_matches(']');
	let mut actual: Vec<&str> = if body.is_empty() {
		Vec::new()
	} else {
		body.split(", ").collect()
	};
	actual.sort();
	let mut expected: Vec<&str> = expected_core.to_vec();
	expected.sort();
	assert_eq!(
		actual, expected,
		"unexpected `%%%mzn-core` contents:\n{stdout}"
	);
	assert!(
		stdout
			.trim_end()
			.ends_with(expected_status_marker.trim_end()),
		"solver did not finish with expected marker `{expected_status_marker}`:\n{stdout}"
	);
}

/// Run the solver once and compare the final reported solution against an
/// expectation.
pub(crate) fn check_final(file: &Path, expect_optimal: bool, expect_sol: ExpectFile) {
	let output = run_solver([file]);
	let stdout = String::from_utf8(output).unwrap();
	let mut slice: &str = stdout.as_str();
	if expect_optimal {
		assert!(
			slice.ends_with(FZN_COMPLETE),
			"Solution did not end with a complete marker:\n{slice}"
		);
		slice = &slice[..slice.len() - FZN_COMPLETE.len()];
	}
	assert!(
		slice.ends_with(FZN_SEPARATOR),
		"Solution did not end with a separator:\n{slice}",
	);
	slice = &slice[..slice.len() - FZN_SEPARATOR.len()];
	expect_sol.assert_eq(slice);
}

/// Run the solver once and assert that it reports the instance as
/// unsatisfiable.
pub(crate) fn check_unsat(file: &Path) {
	let output = run_solver([file]);
	let stdout = String::from_utf8(output).unwrap();
	let slice: &str = stdout.as_str();
	assert!(
		slice.ends_with(FZN_UNSATISFIABLE),
		"Solver did not finish with unsat marker:\n{slice}"
	);
}

/// Run the solver on the given instance and return the output as raw bytes.
fn run_solver<I: Into<OsString>>(args: impl IntoIterator<Item = I>) -> Vec<u8> {
	let args = iter::once(OsString::from("huub")).chain(args.into_iter().map(Into::into));
	let cli = Cli::try_parse_from(args).unwrap();
	let mut out = Vec::new();
	let mut cli = cli.with_stdout(&mut out);
	cli.run()
		.expect("unexpected error while running the solver");
	drop(cli);
	out
}
