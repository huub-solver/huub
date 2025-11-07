#![allow(
	dead_code,
	reason = "module is shared between benchmarks and integration tests"
)]
#![allow(
	unused_imports,
	reason = "module is shared between benchmarks and integration tests"
)]
#![allow(
	unused_macros,
	reason = "module is shared between benchmarks and integration tests"
)]

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
	io::Write,
	path::{Path, PathBuf},
	process::Command,
};

pub(crate) use assert_all_optimal;
pub(crate) use assert_all_solutions;
pub(crate) use assert_first_solution;
pub(crate) use assert_optimal;
pub(crate) use assert_search_order;
pub(crate) use assert_unsat;
use expect_test::ExpectFile;
use huub_cli::Cli;
use pico_args::Arguments;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

#[derive(Debug, Clone, Copy)]
/// Output stream that immediately discards all data.
struct DummyOutput;

pub(crate) fn check_all_optimal(file: &Path, sort: bool, solns: ExpectFile) {
	let args: &[OsString] = &["--all-optimal".into(), file.into()];
	let output = run_solver(args);
	let stdout = String::from_utf8(output).unwrap();
	assert!(!stdout.is_empty(), "Solver did not produce any output");
	let mut stdout: Vec<&str> = stdout.split(FZN_SEPERATOR).collect();
	let marker = stdout.pop().unwrap(); // complete marker
	if sort {
		stdout.sort();
	}
	stdout.push(marker);
	let stdout = stdout.join(FZN_SEPERATOR);
	solns.assert_eq(&stdout);
}

pub(crate) fn check_all_solutions(file: &Path, sort: bool, solns: ExpectFile) {
	let args: &[OsString] = &["--all-solutions".into(), file.into()];
	let output = run_solver(args);
	let stdout = String::from_utf8(output).unwrap();
	assert!(!stdout.is_empty(), "Solver did not produce any output");
	let mut stdout: Vec<&str> = stdout.split(FZN_SEPERATOR).collect();
	let marker = stdout.pop().unwrap(); // complete marker
	if sort {
		stdout.sort();
	}
	stdout.push(marker);
	let stdout = stdout.join(FZN_SEPERATOR);
	solns.assert_eq(&stdout);
}

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
		slice.ends_with(FZN_SEPERATOR),
		"Solution did not end with a seperator:\n{slice}",
	);
	slice = &slice[..slice.len() - FZN_SEPERATOR.len()];
	expect_sol.assert_eq(slice);
}

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
	let args = Arguments::from_vec(args.into_iter().map(|arg| arg.into()).collect());
	let cli: Cli<_, _> = args.try_into().unwrap();
	let mut out = Vec::new();
	let mut cli = cli.with_stdout(&mut out).with_stderr(|| DummyOutput, false);
	cli.run()
		.expect("unexpected error while running the solver");
	out
}

impl Write for DummyOutput {
	fn flush(&mut self) -> std::io::Result<()> {
		Ok(())
	}
	fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
		Ok(buf.len())
	}
}
