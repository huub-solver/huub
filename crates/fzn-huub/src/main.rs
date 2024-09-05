#![allow(
	unused_crate_dependencies,
	reason = "other dependencies are used in the lib.rs file"
)]
use std::{convert::Infallible, fs, path::PathBuf, process::ExitCode};

use fzn_huub::Cli;
use pico_args::Arguments;

const CLI_HELP: &str = r#"USAGE
  $ fzn-huub [-a] [-i] [-s] [-t <value>] [-v] FILE

ARGUMENTS
  FILE    File name of the FlatZinc JSON input file.

FLAGS
                      === STANDARD FLATZINC OPTIONS ===
  -a, --all-solutions             Find all possible solutions for the given (satisfaction) instance.
  -i, --intermediate-solutions    Display all intermediate solutions found during the search.
  -f, --free-search               Allow the solver to adjust any search options as it judges best.
                                  This flag overrides all other search-related flags.
  -s, --statistics                Print statistics about the solving process.
  -t, --time-limit <value>        Set a time limit for the solver. The value can be a number of
                                  milliseconds or a human-readable duration string.
  -v, --verbose                   Display addtional information about actions taken by the solver.
                                  Can be used multiple times to increase verbosity.
                                  (0: INFO, 1: DEBUG, 2: TRACE)

                      === INITIALIZATION OPTIONS ===
  --int-eager-limit               Set the maximum cardinality for which all order literals to
                                  represent an integer variable are created eagerly.
                                  (default: 255)

                      === SOLVING OPTIONS ===
  --vsids-after <value>           Switch to the VSIDS search heuristic after a certain number of
                                  conflicts. (overwritten by --toggle-vsids and --vsids-only)
  --toggle-vsids                  Switch between the activity-based search heuristic and the user-
                                  specific search heuristic after every restart.
                                  (overwritten by --vsids-only)
  --vsids-only                    Only use the activity-based search heuristic provided by the SAT
                                  solver. Ignore the user-specific search heuristic.


                      === BEHAVIOUR OPTIONS ===
  --log-file <FILE>	              Output log messages from the solver to a file, instead of stderr.

DESCRIPTION
  Create a Huub Solver instance tailored to a given FlatZinc JSON input file and solve the problem.

  Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and maintainability in
  addition to speed. LCG solvers are a class of solvers that can be used to solve decision and
  optimization problems. They are characterized by their ability to dynamically add new Boolean
  variables and clauses to a Boolean Satisfiability (SAT) solver during the search process. This
  allows the solver exploit SAT solver's ability to learn from failures during the search process,
  without having to encode the full problem into Boolean variables and clauses.

  Head to https://huub.solutions/ for more information about Huub.

EXAMPLES
  Try and solve the `inst3.fzn.json` FlatZinc JSON input file with a time limit of 10 minutes.

    $ fzn-huub --time-limit 10min inst3.fzn.json

  Solve the `schedule.fzn.json` FlatZinc JSON input file and display all intermediate solutions using
  the MiniZinc output model `schedule.ozn`.

    $ fzn-huub -i schedule.fzn.json | minizinc --ozn-file schedule.ozn
"#;

/// fzn-huub entry point
///
/// This function performs command-line parsing and starts the solving process
/// based on the arguments found.
fn main() -> ExitCode {
	// Parse commandline arguments
	let mut args = Arguments::from_env();
	if args.contains(["-h", "--help"]) {
		print!("{}", CLI_HELP);
		return ExitCode::SUCCESS;
	}

	let log_file = args
		.opt_value_from_os_str("--log-file", |s| -> Result<PathBuf, Infallible> {
			Ok(s.into())
		})
		.unwrap();
	let mut cli: Cli<_, _> = match args.try_into() {
		Ok(cli) => cli,
		Err(e) => {
			eprintln!("Error: {}", e);
			return ExitCode::FAILURE;
		}
	};
	let result = match log_file {
		Some(log_file) => {
			let mut cli = cli.with_stderr(
				move || {
					fs::OpenOptions::new()
						.create(true)
						.append(true)
						.open(&log_file)
						.expect("Failed to open log file")
				},
				false,
			);
			cli.run()
		}
		None => cli.run(),
	};
	if let Err(e) = result {
		eprintln!("Error: {}", e);
		return ExitCode::FAILURE;
	}
	ExitCode::SUCCESS
}
