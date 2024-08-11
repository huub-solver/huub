mod trace;

use std::{
	collections::HashMap,
	convert::Infallible,
	fmt::{self, Debug, Display},
	fs::File,
	io::BufReader,
	num::NonZeroI32,
	path::PathBuf,
	process::ExitCode,
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc, Mutex,
	},
	time::{Duration, Instant},
};

use flatzinc_serde::{FlatZinc, Literal, Method};
use huub::{
	FlatZincError, Goal, InitConfig, LitMeaning, ReformulationError, SlvTermSignal, SolveResult,
	Solver, SolverView, Valuation,
};
use pico_args::Arguments;
use tracing::{subscriber::set_global_default, warn};
use ustr::{ustr, Ustr, UstrMap};

use crate::trace::LitName;

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
const FZN_COMPLETE: &str = "==========";
const FZN_SEPERATOR: &str = "----------";
const FZN_UNKNOWN: &str = "=====UNKNOWN=====";
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====";

/// FlatZinc command line interface for the Huub solver
///
/// This interface is intended to connect Huub with MiniZinc
#[derive(Debug)]
struct Cli {
	/// Path to the FlatZinc JSON input file
	path: PathBuf,
	/// Output all (satisfiable) solutions
	all_solutions: bool,
	/// Output intermediate solutions
	intermediate_solutions: bool,
	/// Allow the solver to adjust search configuration
	free_search: bool,
	/// Print solving statistics
	statistics: bool,
	/// Solving time limit
	time_limit: Option<Duration>,
	/// Level of verbosity
	verbose: u8,
	/// Log file
	log_file: Option<PathBuf>,

	// --- Initialization configuration ---
	/// Cardinatility cutoff for eager order literals
	int_eager_limit: Option<usize>,

	// --- Solving configuration ---
	/// Switch to the VSIDS heuristic after a certain number of conflicts
	vsids_after: Option<u32>,
	/// Alternate between the SAT and VSIDS heuristic after every restart
	toggle_vsids: bool,
	/// Only use the SAT VSIDS heuristic for search
	vsids_only: bool,
}

/// Solution struct to display the results of the solver
struct Solution<'a> {
	value: &'a dyn Valuation,
	fzn: &'a FlatZinc<Ustr>,
	var_map: &'a UstrMap<SolverView>,
}

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
	let cli: Cli = match args.try_into() {
		Ok(cli) => cli,
		Err(e) => {
			eprintln!("Error: {}", e);
			return ExitCode::FAILURE;
		}
	};
	if let Err(e) = cli.run() {
		eprintln!("Error: {}", e);
		return ExitCode::FAILURE;
	}
	ExitCode::SUCCESS
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

impl Cli {
	fn run(&self) -> Result<(), String> {
		// Enable tracing functionality
		let lit_reverse_map: Arc<Mutex<HashMap<NonZeroI32, LitName>>> = Arc::default();
		let int_reverse_map: Arc<Mutex<Vec<Ustr>>> = Arc::default();
		let subscriber = trace::create_subscriber(
			self.verbose,
			self.log_file.clone(),
			Arc::clone(&lit_reverse_map),
			Arc::clone(&int_reverse_map),
		);
		set_global_default(subscriber)
			.map_err(|e| format!("unable to initialize tracing framework: {}", e))?;

		let start = Instant::now();
		let deadline = self.time_limit.map(|t| start + t);

		// Parse FlatZinc JSON file
		let rdr = BufReader::new(
			File::open(&self.path)
				.map_err(|_| format!("Unable to open file “{}”", self.path.display()))?,
		);
		let fzn: FlatZinc<Ustr> = serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?;

		// Convert FlatZinc model to internal Solver representation
		let res = Solver::from_fzn(&fzn, &self.init_config());
		// Resolve any errors that may have occurred during the conversion
		let (mut slv, var_map): (Solver, UstrMap<SolverView>) = match res {
			Err(FlatZincError::ReformulationError(ReformulationError::TrivialUnsatisfiable)) => {
				println!("{}", FZN_UNSATISFIABLE);
				return Ok(());
			}
			Err(err) => {
				return Err(err.to_string());
			}
			Ok((slv, var_map)) => (slv, var_map.into_iter().collect()),
		};

		if self.statistics {
			let stats = slv.init_statistics();
			println!("%%%mzn-stat: blockType={:?}", "init");
			println!("%%%mzn-stat: intVariables={:?}", stats.int_vars());
			println!("%%%mzn-stat: propagators={:?}", stats.propagators());
			println!(
				"%%%mzn-stat: initTime={:?}",
				Instant::now().duration_since(start).as_secs_f64()
			);
			println!("%%%mzn-stat-end");
		}

		// Create reverse map for solver variables if required
		if self.verbose > 0 {
			let mut lit_map = HashMap::new();
			let mut int_map = vec![ustr(""); slv.init_statistics().int_vars()];
			for (name, v) in var_map.iter() {
				match v {
					SolverView::Bool(bv) => {
						if let Some(info) = bv.reverse_map_info() {
							let _ = lit_map.insert(info, LitName::BoolVar(*name, true));
							let _ = lit_map.insert(-info, LitName::BoolVar(*name, false));
						}
					}
					SolverView::Int(iv) => {
						let (pos, is_view) = iv.int_reverse_map_info();
						if let Some(i) = pos {
							if !is_view || int_map[i].is_empty() {
								int_map[i] = *name;
								for (lit, meaning) in iv.lit_reverse_map_info(&slv) {
									let _ = lit_map.insert(lit, LitName::IntLit(i, meaning));
								}
							} else {
								debug_assert!(iv
									.lit_reverse_map_info(&slv)
									.iter()
									.all(|(lit, _)| { lit_map.contains_key(lit) }));
							}
						} else {
							debug_assert!(is_view);
							for (lit, meaning) in iv.lit_reverse_map_info(&slv) {
								let _ = lit_map.entry(lit).or_insert_with(|| {
									let (op, val) = match meaning {
										LitMeaning::Eq(v) => ("=", v),
										LitMeaning::NotEq(v) => ("!=", v),
										LitMeaning::GreaterEq(v) => (">=", v),
										LitMeaning::Less(v) => ("<", v),
									};
									LitName::BoolVar(format!("{name}{op}{val}").into(), true)
								});
							}
						}
					}
				}
			}
			*lit_reverse_map.lock().unwrap() = lit_map;
			*int_reverse_map.lock().unwrap() = int_map;
		}

		// Set Solver Configuration
		if self.free_search {
			slv.set_toggle_vsids(true);
		} else {
			slv.set_vsids_only(self.vsids_only);
			slv.set_toggle_vsids(self.toggle_vsids);
			slv.set_vsids_after(self.vsids_after);
		}

		// Determine Goal and Objective
		let start_solve = Instant::now();
		let goal = if fzn.solve.method != Method::Satisfy {
			let obj_expr = fzn.solve.objective.as_ref().unwrap();
			if let Literal::Identifier(ident) = obj_expr {
				Some((
					if fzn.solve.method == Method::Minimize {
						Goal::Minimize
					} else {
						Goal::Maximize
					},
					if let SolverView::Int(iv) = var_map[ident] {
						iv
					} else {
						todo!()
					},
				))
			} else {
				None
			}
		} else {
			None
		};

		// Set termination conditions for solver
		let interrupt_handling = goal.is_some() && !self.intermediate_solutions;
		let interrupted = Arc::new(AtomicBool::new(false));
		match (interrupt_handling, deadline) {
			(true, Some(deadline)) => {
				let interrupted = Arc::clone(&interrupted);
				slv.set_terminate_callback(Some(move || {
					if interrupted.load(Ordering::SeqCst) || Instant::now() >= deadline {
						SlvTermSignal::Terminate
					} else {
						SlvTermSignal::Continue
					}
				}));
			}
			(true, None) => {
				let interrupted = Arc::clone(&interrupted);
				slv.set_terminate_callback(Some(move || {
					if interrupted.load(Ordering::SeqCst) {
						SlvTermSignal::Terminate
					} else {
						SlvTermSignal::Continue
					}
				}));
			}
			(false, Some(deadline)) => {
				slv.set_terminate_callback(Some(move || {
					if Instant::now() >= deadline {
						SlvTermSignal::Terminate
					} else {
						SlvTermSignal::Continue
					}
				}));
			}
			_ => {}
		};

		// Run the solver!
		let res = match goal {
			Some((goal, obj)) => {
				if self.all_solutions {
					warn!("--all-solutions is ignored when optimizing, use --intermediate-solutions or --all-optimal-solutions instead")
				}
				if self.intermediate_solutions {
					slv.branch_and_bound(obj, goal, |value| {
						print!(
							"{}",
							Solution {
								value,
								fzn: &fzn,
								var_map: &var_map
							}
						)
					})
				} else {
					// Set up Ctrl-C handler (to allow printing last solution)
					if let Err(err) = ctrlc::set_handler(move || {
						interrupted.store(true, Ordering::SeqCst);
					}) {
						warn!("unable to set Ctrl-C handler: {}", err);
					}

					let mut last_sol = String::new();
					let res = slv.branch_and_bound(obj, goal, |value| {
						last_sol = Solution {
							value,
							fzn: &fzn,
							var_map: &var_map,
						}
						.to_string()
					});
					print!("{}", last_sol);
					res
				}
			}
			None if self.all_solutions => {
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
				slv.all_solutions(&vars, |value| {
					print!(
						"{}",
						Solution {
							value,
							fzn: &fzn,
							var_map: &var_map
						}
					)
				})
			}
			None => slv.solve(|value| {
				print!(
					"{}",
					Solution {
						value,
						fzn: &fzn,
						var_map: &var_map
					}
				)
			}),
		};
		// output solving statistics
		if self.statistics {
			let stats = slv.search_statistics();
			println!("%%%mzn-stat: blockType={:?}", "complete");
			println!(
				"%%%mzn-stat: solveTime={}",
				(Instant::now() - start_solve).as_secs_f64()
			);
			println!("%%%mzn-stat: failures={:?}", stats.conflicts());
			println!("%%%mzn-stat: peakDepth={:?}", stats.peak_depth());
			println!("%%%mzn-stat: propagations={:?}", stats.propagations());
			println!("%%%mzn-stat: restarts={:?}", stats.restarts());
			println!("%%%mzn-stat-end");
		}
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

	fn init_config(&self) -> InitConfig {
		let mut config = InitConfig::default();
		if let Some(eager_limit) = self.int_eager_limit {
			config = config.with_int_eager_limit(eager_limit);
		}
		config
	}
}

impl TryFrom<Arguments> for Cli {
	type Error = String;
	fn try_from(mut args: Arguments) -> Result<Self, Self::Error> {
		let mut verbose = 0;
		while args.contains(["-v", "--verbose"]) {
			verbose += 1;
		}

		let cli = Cli {
			all_solutions: args.contains(["-a", "--all-solutions"]),
			intermediate_solutions: args.contains(["-i", "--intermediate-solutions"]),
			free_search: args.contains(["-f", "--free-search"]),
			statistics: args.contains(["-s", "--statistics"]),
			time_limit: args
				.opt_value_from_fn(["-t", "--time-limit"], parse_time_limit)
				.map_err(|e| e.to_string())?,

			int_eager_limit: args
				.opt_value_from_str("--int-eager-limit")
				.map_err(|e| e.to_string())?,

			toggle_vsids: args.contains("--toggle-vsids"),
			vsids_only: args.contains("--vsids-only"),
			vsids_after: args
				.opt_value_from_str("--vsids-after")
				.map_err(|e| e.to_string())?,

			log_file: args
				.opt_value_from_os_str("--log-file", |s| -> Result<PathBuf, Infallible> {
					Ok(s.into())
				})
				.map_err(|e| e.to_string())?,

			verbose,
			path: args
				.free_from_os_str(|s| -> Result<PathBuf, &'static str> { Ok(s.into()) })
				.map_err(|e| e.to_string())?,
		};

		let remaining = args.finish();
		match remaining.len() {
			0 => Ok(()),
			1 => Err(format!(
				"unexpected argument: '{}'",
				remaining[0].to_string_lossy()
			)),
			_ => Err(format!(
				"unexpected arguments: {}",
				remaining
					.into_iter()
					.map(|s| format!("'{}'", s.to_string_lossy()))
					.collect::<Vec<_>>()
					.join(", ")
			)),
		}?;
		Ok(cli)
	}
}

impl Solution<'_> {
	fn print_lit(&self, lit: &Literal<Ustr>) -> String {
		match lit {
			Literal::Int(i) => format!("{i}"),
			Literal::Float(f) => format!("{f}"),
			Literal::Identifier(ident) => {
				format!("{}", (self.value)(self.var_map[ident]).unwrap())
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
}

impl Display for Solution<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for ident in &self.fzn.output {
			if let Some(arr) = self.fzn.arrays.get(ident) {
				writeln!(
					f,
					"{ident} = [{}];",
					arr.contents
						.iter()
						.map(|lit| self.print_lit(lit))
						.collect::<Vec<_>>()
						.join(",")
				)?
			} else {
				writeln!(
					f,
					"{ident} = {};",
					(self.value)(self.var_map[ident]).unwrap()
				)?
			}
		}
		writeln!(f, "{}", FZN_SEPERATOR)
	}
}

#[cfg(test)]
mod tests {
	// Used in integration tests
	use expect_test as _;
}
