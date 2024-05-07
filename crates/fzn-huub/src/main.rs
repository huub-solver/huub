mod tracing;

use std::{
	collections::HashMap,
	fmt::Debug,
	fs::File,
	io::{self, BufReader},
	num::NonZeroI32,
	path::PathBuf,
	sync::{Arc, Mutex},
	time::{Duration, Instant},
};

use ::tracing::Level;
use clap::Parser;
use flatzinc_serde::{FlatZinc, Literal};
use huub::{
	FlatZincError, ReformulationError, SlvTermSignal, SolveResult, Solver, SolverView, Valuation,
};
use miette::{IntoDiagnostic, Result, WrapErr};
use tracing::{FmtLitFields, LitName};
use tracing_subscriber::fmt::time::uptime;
use ustr::{ustr, Ustr, UstrMap};

/// fzn-huub entry point
///
/// This function performs command-line parsing and starts the solving process
/// based on the arguments found.
fn main() -> Result<()> {
	// Parse commandline arguments
	let args = Args::parse();

	// Enable tracing functionality
	let lit_reverse_map: Arc<Mutex<HashMap<NonZeroI32, LitName>>> = Arc::default();
	let int_reverse_map: Arc<Mutex<Vec<Ustr>>> = Arc::default();
	tracing_subscriber::fmt()
		.with_max_level(match args.verbose {
			0 => Level::INFO,
			1 => Level::DEBUG,
			_ => Level::TRACE, // 2 or more
		})
		.with_writer(io::stderr)
		.with_timer(uptime())
		.map_fmt_fields(|fmt| {
			FmtLitFields::new(
				fmt,
				Arc::clone(&lit_reverse_map),
				Arc::clone(&int_reverse_map),
			)
		})
		.init();

	let start = Instant::now();
	let deadline = args.time_limit.map(|t| start + t);

	// Parse FlatZinc JSON file
	let rdr = BufReader::new(
		File::open(&args.path)
			.into_diagnostic()
			.wrap_err_with(|| format!("Unable to open file “{}”", args.path.display()))?,
	);
	let fzn: FlatZinc<Ustr> = serde_json::from_reader(rdr)
		.into_diagnostic()
		.wrap_err_with(|| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				args.path.display()
			)
		})?;

	// Convert FlatZinc model to internal Solver representation
	let res = Solver::from_fzn(&fzn);
	// Resolve any errors that may have occurred during the conversion
	let (mut slv, var_map): (Solver, UstrMap<SolverView>) = match res {
		Err(FlatZincError::ReformulationError(ReformulationError::TrivialUnsatisfiable)) => {
			println!("{}", FZN_UNSATISFIABLE);
			return Ok(());
		}
		Err(err) => {
			return Err(err)
				.into_diagnostic()
				.wrap_err("Error while processing FlatZinc")
		}
		Ok((slv, var_map)) => (slv, var_map.into_iter().collect()),
	};

	// Create reverse map for solver variables if required
	if args.verbose > 0 {
		let mut bool_var_map = HashMap::new();
		let mut int_lit_map = HashMap::new();
		let mut int_map = vec![ustr(""); slv.num_int_vars()];
		for (name, v) in var_map.iter() {
			match v {
				SolverView::Bool(bv) => bv.add_to_reverse_map(&mut bool_var_map, *name),
				SolverView::Int(iv) => {
					iv.add_to_lit_reverse_map(&slv, &mut int_lit_map);
					iv.add_to_int_reverse_map(&mut int_map, *name);
				}
			}
		}
		*lit_reverse_map.lock().unwrap() = bool_var_map
			.into_iter()
			.map(|(k, (i, p))| (k, LitName::BoolVar(i, p)))
			.chain(
				int_lit_map
					.into_iter()
					.map(|(k, (i, m))| (k, LitName::IntLit(i, m))),
			)
			.collect();
		*int_reverse_map.lock().unwrap() = int_map;
	}

	// Set time limit if required
	if let Some(deadline) = deadline {
		slv.set_terminate_callback(Some(|| {
			if Instant::now() >= deadline {
				SlvTermSignal::Terminate
			} else {
				SlvTermSignal::Continue
			}
		}));
	}

	// Run the solver!
	let print_sol = |value: &dyn Valuation, fzn: &FlatZinc<Ustr>, var_map: &UstrMap<SolverView>| {
		for ident in &fzn.output {
			if let Some(arr) = fzn.arrays.get(ident) {
				println!(
					"{ident} = [{}];",
					arr.contents
						.iter()
						.map(|lit| print_lit(value, &var_map, lit))
						.collect::<Vec<_>>()
						.join(",")
				)
			} else {
				println!("{ident} = {};", value(var_map[ident]).unwrap())
			}
		}
		println!("{}", FZN_SEPERATOR);
	};
	let res = if args.all_solutions {
		let vars: Vec<_> = fzn
			.output
			.iter()
			.flat_map(|ident| {
				if let Some(arr) = fzn.arrays.get(ident) {
					arr.contents
						.iter()
						.filter_map(|lit| {
							if let Literal::Identifier(ident) = lit {
								Some(var_map[ident])
							} else {
								None
							}
						})
						.collect()
				} else {
					vec![var_map[ident]]
				}
			})
			.collect();
		slv.all_solutions(&vars, |value| print_sol(value, &fzn, &var_map))
	} else {
		slv.solve(|value| print_sol(value, &fzn, &var_map))
	};
	match res {
		SolveResult::Satisfied => {}
		SolveResult::Unsatisfiable => {
			println!("{}", FZN_UNSATISFIABLE);
		}
		SolveResult::Unknown => {
			println!("{}", FZN_UNKNOWN)
		}
		SolveResult::Complete => {
			println!("{}", FZN_COMPLETE)
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

	/// Output all (satisfiable) solutions
	#[arg(short, long)]
	all_solutions: bool,

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

fn print_lit(value: &dyn Valuation, var_map: &UstrMap<SolverView>, lit: &Literal<Ustr>) -> String {
	match lit {
		Literal::Int(i) => format!("{i}"),
		Literal::Float(f) => format!("{f}"),
		Literal::Identifier(ident) => {
			format!("{}", value(var_map[ident]).unwrap())
		}
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

const FZN_COMPLETE: &str = "==========";
const FZN_SEPERATOR: &str = "----------";
const FZN_UNKNOWN: &str = "=====UNKNOWN=====";
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====";
