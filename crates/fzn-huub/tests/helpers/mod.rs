use assert_cmd::Command;
use expect_test::ExpectFile;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
// const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

pub(crate) fn fzn_huub(args: &[&str]) -> Command {
	let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
	let _ = cmd.args(args);
	cmd
}

pub(crate) fn check_all_solutions(file: &str, solns: ExpectFile) {
	let output = fzn_huub(&["-a", file]).output().unwrap();
	assert!(
		output.status.success(),
		"Solver did not finish with success exit code"
	);
	let stdout = String::from_utf8(output.stdout).unwrap();
	assert!(!stdout.is_empty(), "Solver did not produce any output");
	let mut stdout: Vec<&str> = stdout.split(FZN_SEPERATOR).collect();
	let marker = stdout.pop().unwrap(); // complete marker
	stdout.sort();
	stdout.push(marker);
	let stdout = stdout.join(FZN_SEPERATOR);
	solns.assert_eq(&stdout);
}

pub(crate) fn check_optimal(file: &str, check_sol: impl FnOnce(&str) -> bool) {
	let mut end = String::from(FZN_SEPERATOR);
	end.push_str(FZN_COMPLETE);
	let output = fzn_huub(&[file]).output().unwrap();
	assert!(
		output.status.success(),
		"Solver did not finish with success exit code"
	);
	let stdout = String::from_utf8(output.stdout).unwrap();
	assert!(
		stdout.ends_with(&end),
		"Solver did not finish with complete marker"
	);
	let sol = &stdout[..stdout.len() - end.len()];
	assert!(
		check_sol(sol),
		"Solution check on the optimal solution failed"
	);
}

macro_rules! assert_all_solutions {
	($file:ident) => {
		#[test]
		fn $file() {
			$crate::helpers::check_all_solutions(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				expect_test::expect_file![&format!("../corpus/{}.sol", stringify!($file))],
			)
		}
	};
}
pub(crate) use assert_all_solutions;

macro_rules! assert_optimal {
	($file:ident, $check:expr) => {
		#[test]
		fn $file() {
			$crate::helpers::check_optimal(
				&format!("./corpus/{}.fzn.json", stringify!($file)),
				$check,
			)
		}
	};
}
pub(crate) use assert_optimal;

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
