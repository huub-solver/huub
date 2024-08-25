use std::{
	env::{consts::EXE_SUFFIX, current_exe, var_os, vars},
	path::PathBuf,
	process::Command,
};

use expect_test::ExpectFile;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

fn cargo_bin(name: &str) -> PathBuf {
	let env_var = format!("CARGO_BIN_EXE_{}", name);
	var_os(env_var).map(|p| p.into()).unwrap_or_else(|| {
		let target_dir = current_exe()
			.map(|mut path| {
				let _ = path.pop();
				if path.ends_with("deps") {
					let _ = path.pop();
				}
				path
			})
			.unwrap();
		target_dir.join(format!("{}{}", name, EXE_SUFFIX))
	})
}

fn cargo_cmd<S: AsRef<str>>(name: S) -> Command {
	let path = cargo_bin(name.as_ref());
	if path.is_file() {
		let cargo_runner: Option<Vec<_>> = vars()
			.find(|(k, _)| k.starts_with("CARGO_TARGET_") && k.ends_with("_RUNNER"))
			.map(|(_, runner)| runner.split(' ').map(str::to_string).collect());
		if let Some(runner) = cargo_runner {
			let mut cmd = Command::new(&runner[0]);
			let _ = cmd.args(&runner[1..]).arg(path);
			cmd
		} else {
			Command::new(path)
		}
	} else {
		panic!("Unable to find cargo binary")
	}
}

pub(crate) fn check_all_solutions(file: &str, sort: bool, solns: ExpectFile) {
	let output = fzn_huub(&["-a", file]).output().unwrap();
	assert!(
		output.status.success(),
		"Solver did not finish with success exit code"
	);
	let stdout = String::from_utf8(output.stdout).unwrap();
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

pub(crate) fn check_final(file: &str, expect_optimal: bool, expect_sol: ExpectFile) {
	let output = fzn_huub(&[file]).output().unwrap();
	assert!(
		output.status.success(),
		"Solver did not finish with success exit code"
	);
	let stdout = String::from_utf8(output.stdout).unwrap();
	let mut slice: &str = stdout.as_str();
	if expect_optimal {
		assert!(
			slice.ends_with(FZN_COMPLETE),
			"Solver did not finish with complete marker"
		);
		slice = &slice[..slice.len() - FZN_COMPLETE.len()];
	}
	assert!(
		slice.ends_with(FZN_SEPERATOR),
		"Solution did not end with a seperator"
	);
	slice = &slice[..slice.len() - FZN_SEPERATOR.len()];
	expect_sol.assert_eq(slice);
}

pub(crate) fn check_unsat(file: &str) {
	let output = fzn_huub(&[file]).output().unwrap();
	assert!(
		output.status.success(),
		"Solver did not finish with success exit code"
	);
	let stdout = String::from_utf8(output.stdout).unwrap();
	let slice: &str = stdout.as_str();
	assert!(
		slice.ends_with(FZN_UNSATISFIABLE),
		"Solver did not finish with unsat marker"
	);
}

pub(crate) fn fzn_huub(args: &[&str]) -> Command {
	let mut cmd = cargo_cmd(env!("CARGO_PKG_NAME"));
	let _ = cmd.args(args);
	cmd
}

macro_rules! assert_all_solutions {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_solutions(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				true,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}
pub(crate) use assert_all_solutions;

macro_rules! assert_unsat {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_unsat(&format!("./corpus/{}.fzn.json", stringify!($file)))
		}
	};
}
pub(crate) use assert_unsat;

macro_rules! assert_optimal {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_final(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				true,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}
pub(crate) use assert_optimal;

macro_rules! assert_search_order {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_solutions(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				false,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}
pub(crate) use assert_search_order;

macro_rules! assert_first_solution {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_final(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				false,
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}
pub(crate) use assert_first_solution;

/// References for the dependencies used by the executable
mod main_depencencies {
	use ctrlc as _;
	use flatzinc_serde as _;
	use humantime as _;
	use huub as _;
	use pico_args as _;
	use serde_json as _;
	use tracing as _;
	use tracing_subscriber as _;
	use ustr as _;
}
