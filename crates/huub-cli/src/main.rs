//! huub-cli is a command-line interface (CLI) for the Huub solver.
//!
//! The `main.rs` file only provides an entrypoint for the executable, all other
//! functionality is contained in the `lib.rs` file, to allow testing the
//! functionality as a library.

#![allow(
	unused_crate_dependencies,
	reason = "other dependencies are used in the lib.rs file"
)]

use std::process::ExitCode;

use huub_cli::Cli;

/// huub entry point
///
/// This function performs command-line parsing and starts the solving process
/// based on the arguments found.
fn main() -> ExitCode {
	let mut cli = match Cli::try_parse_from(std::env::args_os()) {
		Ok(parsed) => parsed,
		Err(err) => {
			let exit_code = err.exit_code();
			err.print().expect("unable to write clap error output");
			return ExitCode::from(u8::try_from(exit_code).unwrap_or(1));
		}
	};
	let result = cli.run();
	if let Err(e) = result {
		eprintln!("Error: {e}");
		return ExitCode::FAILURE;
	}
	ExitCode::SUCCESS
}
