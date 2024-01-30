use std::{fs::File, io::BufReader, path::PathBuf, time::Duration};

use clap::Parser;
use flatzinc_serde::{FlatZinc, Literal};
use huub::{SimplifiedBool, SimplifiedVariable, Solver, Valuation, Value, Variable};
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

	let (mut slv, var_map) = Solver::from_fzn(&fzn)
		.into_diagnostic()
		.wrap_err("Error while processing FlatZinc".to_string())?;

	let print_var = |value: &dyn Valuation, var: &SimplifiedVariable| match var {
		SimplifiedVariable::Bool(SimplifiedBool::Lit(l)) => {
			format!(
				"{}",
				value(Variable::Bool(l.var()))
					.map(|b| {
						let Value::Bool(b) = b;
						if l.is_negated() {
							!b
						} else {
							b
						}
					})
					.unwrap()
			)
		}
		SimplifiedVariable::Bool(SimplifiedBool::Val(b)) => format!("{b}"),
	};
	let print_lit = |value: &dyn Valuation, lit: &Literal| match lit {
		Literal::Int(i) => format!("{i}"),
		Literal::Float(f) => format!("{f}"),
		Literal::Identifier(ident) => print_var(value, &var_map[ident]),
		Literal::Bool(b) => format!("{b}"),
		Literal::IntSet(is) => is
			.into_iter()
			.map(|r| format!("{}..{}", r.start(), r.end()))
			.collect::<Vec<_>>()
			.join(" union "),
		Literal::FloatSet(fs) => fs
			.into_iter()
			.map(|r| format!("{}..{}", r.start(), r.end()))
			.collect::<Vec<_>>()
			.join(" union "),
		Literal::String(s) => s.clone(),
	};
	slv.solve(|value| {
		for ident in &fzn.output {
			if let Some(arr) = fzn.arrays.get(ident) {
				println!(
					"{ident} = [{}]",
					arr.contents
						.iter()
						.map(|lit| print_lit(value, lit))
						.collect::<Vec<_>>()
						.join(",")
				)
			} else {
				println!("{ident} = {}", print_var(value, &var_map[ident]))
			}
		}
		println!("----------");
	});
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
