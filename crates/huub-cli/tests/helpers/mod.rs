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

/// Define an integration test that checks the solver produces a well-formed
/// proof for an instance in both the DRCP and the VeriPB (`.pbp`) proof
/// formats.
///
/// The `$conclusion` argument indicates whether the DRCP proof is expected to
/// contain a conclusion, which is the case for unsatisfiable instances and for
/// optimization instances that are solved to completion, but not for
/// satisfiable decision instances.
macro_rules! assert_proof {
	($name:ident, $file:ident, $conclusion:expr) => {
		#[test]
		fn $name() {
			$crate::helpers::check_proof(
				&std::path::PathBuf::from(format!("./corpus/{}.fzn.json", stringify!($file))),
				$conclusion,
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
pub(crate) use assert_proof;
pub(crate) use assert_search_order;
pub(crate) use assert_unsat;
use drcp_format::{Step, reader::ProofReader};
use expect_test::ExpectFile;
use huub_cli::Cli;
use rustc_hash::FxHashSet;

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

/// Assert that the given DRCP proof parses, contains at least one step (and a
/// conclusion when `expect_conclusion` is set), and that every atom code used
/// in a premise or consequent is defined.
fn check_drcp(proof: &str, expect_conclusion: bool) {
	// Collect the atom codes defined in the proof.
	let defined: FxHashSet<i32> = proof
		.lines()
		.filter_map(|l| l.strip_prefix("a "))
		.filter_map(|l| l.split_whitespace().next())
		.filter_map(|c| c.parse().ok())
		.collect();

	let mut reader = ProofReader::<_, i64>::new(proof.as_bytes());
	let mut steps = 0;
	let mut has_conclusion = false;
	while let Some(step) = reader.next_step().expect("DRCP proof should parse") {
		steps += 1;
		if matches!(step, Step::Conclusion(_)) {
			has_conclusion = true;
		}
	}
	// A proof that concludes (unsatisfiability or a dual bound) must contain the
	// steps that support it.
	if expect_conclusion {
		assert!(steps > 0, "DRCP proof did not contain any steps:\n{proof}");
	}
	assert_eq!(
		has_conclusion, expect_conclusion,
		"unexpected presence of a DRCP conclusion:\n{proof}"
	);

	// Guard against silently losing variable names: when the proof defines any
	// atoms, at least one must be named.
	let defines_atom = |l: &str| l.starts_with("a ");
	let defines_named_atom = |l: &str| {
		l.strip_prefix("a ")
			.and_then(|l| l.split_once('['))
			.is_some_and(|(_, atom)| atom.starts_with(|c: char| c.is_ascii_alphabetic()))
	};
	assert!(
		!proof.lines().any(defines_atom) || proof.lines().any(defines_named_atom),
		"DRCP proof defines no named atoms (all synthesized):\n{proof}"
	);

	// Every atom code used in a premise or consequent must be defined. For both
	// inference (`i`) and deduction (`n`) steps, the premise atom codes appear
	// before the `0` separator; for inference steps a single consequent atom
	// code follows the separator. The remaining tokens (deduction antecedent
	// step identifiers and `c:`/`l:` hints) are not atom codes.
	for line in proof.lines() {
		let kind = line.chars().next();
		if !matches!(kind, Some('i') | Some('n')) {
			continue;
		}
		let mut tokens = line.split_whitespace().skip(2).peekable();
		// Premise atom codes, up to the `0` separator.
		for tok in tokens.by_ref() {
			if tok == "0" {
				break;
			}
			let code: i32 = tok.parse().expect("premise should be an atom code");
			assert!(
				defined.contains(&code.abs()),
				"DRCP proof uses undefined atom code {code}:\n{proof}"
			);
		}
		// The consequent atom code of an inference step, if present.
		if kind == Some('i')
			&& let Some(tok) = tokens.peek()
			&& let Ok(code) = tok.parse::<i32>()
		{
			assert!(
				defined.contains(&code.abs()),
				"DRCP proof uses undefined atom code {code}:\n{proof}"
			);
		}
	}
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

/// Run the solver on the given instance with proof logging enabled in both the
/// DRCP and VeriPB (`.pbp`) formats, and assert that the produced proofs are
/// well-formed.
///
/// For DRCP, the proof is parsed using the `drcp-format` reader and is required
/// to contain at least one step and a conclusion. The companion atom
/// definitions must cover every literal code used in the proof. For VeriPB, the
/// proof is required to have the expected header and conclusion lines.
pub(crate) fn check_proof(file: &Path, expect_conclusion: bool) {
	let dir = std::env::temp_dir().join(format!(
		"huub-proof-{}-{}",
		file.file_stem().unwrap().to_string_lossy(),
		std::process::id()
	));
	std::fs::create_dir_all(&dir).unwrap();

	// Check the DRCP proof.
	let drcp_path = dir.join("proof.drcp");
	let _ = run_solver([
		OsString::from("--proof"),
		drcp_path.clone().into(),
		file.into(),
	]);
	// The atom definitions are written to a companion `.lits` file; a checker
	// reads them before the proof, so concatenate them ahead of the steps.
	let drcp = std::fs::read_to_string(&drcp_path).unwrap();
	let lits = std::fs::read_to_string(drcp_path.with_extension("lits")).unwrap();
	check_drcp(&format!("{lits}{drcp}"), expect_conclusion);

	// Check the VeriPB proof.
	let pbp_path = dir.join("proof.pbp");
	let _ = run_solver([
		OsString::from("--proof"),
		pbp_path.clone().into(),
		file.into(),
	]);
	let pbp = std::fs::read_to_string(&pbp_path).unwrap();
	assert!(
		pbp.starts_with("pseudo-Boolean proof version 3.0\nf 0 ;\n"),
		"VeriPB proof missing the expected header:\n{pbp}"
	);
	assert!(
		pbp.trim_end().ends_with("end pseudo-Boolean proof ;"),
		"VeriPB proof missing the expected conclusion:\n{pbp}"
	);

	std::fs::remove_dir_all(&dir).unwrap();
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
