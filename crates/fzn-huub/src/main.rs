mod tracing;

use std::{
	collections::{BTreeMap, HashMap},
	fs::File,
	io::{self, BufReader},
	num::NonZeroI32,
	path::PathBuf,
	sync::{Arc, Mutex},
	time::Duration,
};

use clap::Parser;
use flatzinc_serde::{FlatZinc, Literal};
use huub::{
	SimplifiedBool, SimplifiedInt, SimplifiedVariable, SolveResult, Solver, Valuation, Value,
};
use miette::{IntoDiagnostic, Result, WrapErr};

use ::tracing::Level;
use tracing_subscriber::fmt::time::uptime;

use tracing::FmtLitFields;

/// fzn-huub entry point
///
/// This function performs command-line parsing and starts the solving process
/// based on the arguments found.
fn main() -> Result<()> {
	// Parse commandline arguments
	let args = Args::parse();

	// Enable tracing functionality
	let lit_reverse_map: Arc<Mutex<HashMap<NonZeroI32, String>>> = Arc::default();
	let int_reverse_map: Arc<Mutex<HashMap<usize, String>>> = Arc::default();
	tracing_subscriber::fmt()
		.with_max_level(match args.verbose {
			0 => Level::INFO,
			1 => Level::DEBUG,
			_ => Level::TRACE, // 2 or more
		})
		.with_writer(io::stderr)
		.with_timer(uptime())
		.map_fmt_fields(|fmt| {
			FmtLitFields::new(fmt, lit_reverse_map.clone(), int_reverse_map.clone())
		})
		.init();

	// Parse FlatZinc JSON file
	let rdr = BufReader::new(
		File::open(&args.path)
			.into_diagnostic()
			.wrap_err_with(|| format!("Unable to open file “{}”", args.path.display()))?,
	);
	let fzn: FlatZinc = serde_json::from_reader(rdr)
		.into_diagnostic()
		.wrap_err_with(|| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				args.path.display()
			)
		})?;

	// Convert FlatZinc model to internal Solver representation
	let (mut slv, var_map): (Solver, _) = Solver::from_fzn(&fzn)
		.into_diagnostic()
		.wrap_err("Error while processing FlatZinc")?;

	// Create reverse map for solver variables if required
	if args.verbose > 0 {
		let mut lit_map = HashMap::new();
		let mut int_map = HashMap::new();
		for (name, v) in var_map.iter() {
			match v {
				SimplifiedVariable::Bool(SimplifiedBool::Lit(l)) => {
					l.add_to_reverse_map(&mut lit_map, name)
				}
				SimplifiedVariable::Int(SimplifiedInt::Var(r)) => {
					r.add_to_lit_reverse_map(&slv, &mut lit_map, name);
					r.add_to_int_reverse_map(&mut int_map, name);
				}
				_ => {}
			}
		}
		*lit_reverse_map.lock().unwrap() = lit_map;
		*int_reverse_map.lock().unwrap() = int_map;
	}

	// Run the solver!
	match slv.solve(|value| {
		for ident in &fzn.output {
			if let Some(arr) = fzn.arrays.get(ident) {
				println!(
					"{ident} = [{}]",
					arr.contents
						.iter()
						.map(|lit| print_lit(value, &var_map, lit))
						.collect::<Vec<_>>()
						.join(",")
				)
			} else {
				println!("{ident} = {}", print_var(value, &var_map[ident]))
			}
		}
		println!("----------");
	}) {
		SolveResult::Sat => {}
		SolveResult::Unsat => {
			println!("=====UNSATISFIABLE=====")
		}
		SolveResult::Unknown => {
			println!("=====UNKNOWN=====")
		}
	}
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

fn print_var(value: &dyn Valuation, var: &SimplifiedVariable) -> String {
	match var {
		SimplifiedVariable::Bool(SimplifiedBool::Lit(l)) => {
			format!(
				"{}",
				value(l.into())
					.map(|b| {
						let Value::Bool(b) = b else { unreachable!() };
						b
					})
					.unwrap()
			)
		}
		SimplifiedVariable::Bool(SimplifiedBool::Val(b)) => format!("{b}"),
		SimplifiedVariable::Int(SimplifiedInt::Var(i)) => {
			format!(
				"{}",
				value(i.into())
					.map(|v| {
						let Value::Int(v) = v else { unreachable!() };
						v
					})
					.unwrap()
			)
		}
		SimplifiedVariable::Int(SimplifiedInt::Val(i)) => format!("{i}"),
	}
}

fn print_lit(
	value: &dyn Valuation,
	var_map: &BTreeMap<String, SimplifiedVariable>,
	lit: &Literal,
) -> String {
	match lit {
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
	}
}
