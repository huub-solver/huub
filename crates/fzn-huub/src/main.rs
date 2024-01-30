use std::{fs::File, io::BufReader, path::PathBuf, time::Duration};

use clap::Parser;
use flatzinc_serde::{Domain, FlatZinc, Type};
use miette::{IntoDiagnostic, Result, WrapErr};
use tracing::Level;
use tracing_subscriber::fmt::{time::uptime, SubscriberBuilder};

/// fzn-huub entry point
///
/// This function performs command-line parsing and starts the solving process
/// based on the arguments found.
fn main() -> Result<()> {
	// Parse commandline arguments
	let args = Args::parse();

	// Enable tracing functionality
	let with_level = |builder: SubscriberBuilder| -> SubscriberBuilder {
		if args.verbose != 0 {
			builder.with_max_level(match args.verbose {
				1 => Level::INFO,
				_ => Level::DEBUG,
			})
		} else {
			builder
		}
	};
	with_level(tracing_subscriber::fmt())
		.with_timer(uptime())
		.finish();

	// Parse FlatZinc JSON file
	let rdr = BufReader::new(
		File::open(&args.path)
			.into_diagnostic()
			.wrap_err(format!("Unable to open file “{}”", args.path.display()))?,
	);
	let fzn: FlatZinc = serde_json::from_reader(rdr)
		.into_diagnostic()
		.wrap_err(format!(
			"Unable to parse file “{}” as FlatZinc JSON",
			args.path.display()
		))?;

	for (name, var) in fzn.variables {
		match var.ty {
			Type::Bool => println!("{} = false;", name),
			Type::Int => println!(
				"{} = {}",
				name,
				if let Some(Domain::Int(dom)) = var.domain {
					*dom.lower_bound().unwrap()
				} else {
					0
				}
			),
			Type::Float => unimplemented!("Floating point decision variables are not supported"),
			Type::IntSet => unimplemented!("Integet set variables are not supported"),
		}
	}
	println!("----------");
	Ok(())
}

/// FlatZinc command line interface for the Huub solver
///
/// This interface is intended to connect Huub with MiniZinc
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
	/// Path to the FlatZinc JSON input file
	#[arg(required = true)]
	path: PathBuf,

	/// Output intermediate solutions
	#[arg(short, long)]
	intermediate_solutions: bool,

	/// Print solving statistics
	#[arg(short, long)]
	statistics: bool,

	/// Solving time limit
	#[arg(short, long, value_parser = parse_time_limit)]
	time_limit: Option<Duration>,

	/// Level of verbosity
	#[arg(short, long, action = clap::ArgAction::Count)]
	verbose: u8,
}

/// Parse time duration for the time limit flag
///
/// This function can uses [`humantime::parse_duration`], but assumes a single
/// millisecond measurement if no unit is provided.
fn parse_time_limit(s: &str) -> Result<Duration, humantime::DurationError> {
	if let Ok(ms) = s.parse() {
		Ok(Duration::from_millis(ms))
	} else {
		humantime::parse_duration(s)
	}
}
