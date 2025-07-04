//! FlatZinc command line interface for the Huub solver.

/// Write a message to an output stream, similar to `print!`.
///
/// Note that this differs from `write!` in that it will panic if writing to the
/// stream fails.
macro_rules! output {
	($($arg:tt)*) => {
		write!($($arg)*).expect("unable to write to output stream")
	};
}

/// Write a message to an output stream with an added newline, similar to
/// `println!`.
///
/// Note that this differs from `write!` in that it will panic if writing to the
/// stream fails.
macro_rules! outputln {
	($($arg:tt)*) => {
		writeln!($($arg)*).expect("unable to write to output stream")
	};
}

mod trace;

use std::{
	collections::HashMap,
	ffi::OsStr,
	fmt::{self, Debug, Display},
	fs::File,
	io::{self, BufReader},
	num::NonZeroI32,
	path::PathBuf,
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc, Mutex,
	},
	time::{Duration, Instant},
};

use flatzinc_serde::{FlatZinc, Literal, Method};
use huub::{
	actions::DecisionActions,
	flatzinc::FlatZincError,
	reformulate::{InitConfig, ReformulationError},
	solver::{BoolView, Goal, IntLitMeaning, IntView, SolveResult, Solver, Valuation, Value, View},
	xcsp3::Xcsp3Error,
	SlvTermSignal,
};
use pico_args::Arguments;
use quick_xml as _;
use tracing::{subscriber::set_default, warn};
use tracing_subscriber::fmt::MakeWriter;
use ustr::{ustr, Ustr, UstrMap};
use xcsp3_serde::Instance as Xcsp3Instance;

use crate::trace::LitName;

/// Status message to output when it is proven that no more/better solutions can
/// be found.
const FZN_COMPLETE: &str = "==========";
/// Seperator to output between solutions.
const FZN_SEPERATOR: &str = "----------";
/// Status message to output when no solution is found within the time limit,
/// but the problem is not proven to be unsatisfiable.
const FZN_UNKNOWN: &str = "=====UNKNOWN=====";
/// Status message to output when a problem is proven to be unsatisfiable.
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====";

/// FlatZinc command line interface for the Huub solver
///
/// This interface is intended to connect Huub with MiniZinc
#[derive(Debug)]
pub struct Cli<Stdout, Stderr> {
	/// Path to the FlatZinc JSON input file
	path: PathBuf,
	/// Output all (satisfiable) solutions
	all_solutions: bool,
	/// Output all optimal solutions
	all_optimal: bool,
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

	// --- Initialization configuration ---
	/// Cardinatility cutoff for eager order literals
	int_eager_limit: Option<usize>,

	// --- Search configuration ---
	/// Whether solver is allowed to restart
	restart: bool,
	/// Alternate between the SAT and VSIDS heuristic after every restart
	toggle_vsids: bool,
	/// Switch to the VSIDS heuristic after a certain number of conflicts
	vsids_after_conflict: Option<u32>,
	/// Whether to switch to the VSIDS heuristic after a restart
	vsids_after_restart: bool,
	/// Only use the SAT VSIDS heuristic for search
	vsids_only: bool,

	// -- Preprocessing/Inprocessing configuration ---
	/// Whether to enable the globally blocked clause elimination (conditioning)
	conditioning: bool,
	/// Whether to enable inprocessing during search in the oracle solver
	inprocessing: bool,
	/// The number of preprocessing rounds in the oracle solver
	preprocessing: Option<usize>,
	/// Whether to enable the failed literal probing in the oracle solver.
	probing: bool,
	/// Whether to enable the global forward subsumption in the oracle solver.
	subsumption: bool,
	/// Whether to enable the bounded variable elimination in the oracle solver.
	variable_elimination: bool,
	/// Whether the vivification heuristic is enabled
	vivification: bool,

	// --- Output configuration ---
	/// Output stream for (intermediate) solutions and statistics
	///
	/// Note that this stream will be parsed by MiniZinc
	stdout: Stdout,
	/// Output stream for other messages (errors, warnings, debug, etc.)
	stderr: Stderr,
	/// Whether to use ANSI color codes in the output (only for stderr)
	ansi_color: bool,

	// --- Derived information ---
	/// Format of the input file, for which the output is matched.
	format: Format,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// Input and output format
enum Format {
	/// FlatZinc (JSON)
	FlatZinc,
	/// XCSP3 (XML)
	Xcsp3,
}

/// Output definition for the problem
struct Output {
	/// List of single variables with their names
	singletons: Vec<(Ustr, View)>,
	/// List of arrays of variables with their (array) names
	arrays: Vec<(Ustr, Vec<View>)>,
}

/// Solution struct to display the results of the solver
struct Solution<'a> {
	/// What format to use to output a solution
	format: Format,
	/// Mapping from solver views to solution values
	value: &'a dyn Valuation,
	/// Output definition of the problem
	output: &'a Output,
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

/// Set the termination conditions of the [`Solver`] instance.
fn solver_set_terminate(
	solver: &mut Solver,
	interrupted: &Arc<AtomicBool>,
	interrupt_handling: bool,
	deadline: Option<Instant>,
) {
	match (interrupt_handling, deadline) {
		(true, Some(deadline)) => {
			let interrupted = Arc::clone(interrupted);
			solver.set_terminate_callback(Some(move || {
				if interrupted.load(Ordering::SeqCst) || Instant::now() >= deadline {
					SlvTermSignal::Terminate
				} else {
					SlvTermSignal::Continue
				}
			}));
		}
		(true, None) => {
			let interrupted = Arc::clone(interrupted);
			solver.set_terminate_callback(Some(move || {
				if interrupted.load(Ordering::SeqCst) {
					SlvTermSignal::Terminate
				} else {
					SlvTermSignal::Continue
				}
			}));
		}
		(false, Some(deadline)) => {
			solver.set_terminate_callback(Some(move || {
				if Instant::now() >= deadline {
					SlvTermSignal::Terminate
				} else {
					SlvTermSignal::Continue
				}
			}));
		}
		_ => {}
	};
}

impl<Stdout, Stderr> Cli<Stdout, Stderr>
where
	Stdout: io::Write,
	Stderr: Clone + for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
{
	/// Distill the initialization configution, used to initialize the Huub
	/// solver, from the given command line arguments.
	fn init_config(&self) -> InitConfig {
		let mut config = InitConfig::default();
		if let Some(eager_limit) = self.int_eager_limit {
			config = config.with_int_eager_limit(eager_limit);
		}
		if let Some(preprocessing) = self.preprocessing {
			config = config.with_preprocessing(preprocessing);
		}
		config = config
			.with_conditioning(self.conditioning)
			.with_inprocessing(self.inprocessing)
			.with_probing(self.probing)
			.with_restart(self.free_search || self.restart)
			.with_subsumption(self.subsumption)
			.with_variable_elimination(self.variable_elimination)
			.with_vivification(self.vivification);

		config
	}

	/// Run the Huub solver in accordance to the given command line arguments.
	pub fn run(&mut self) -> Result<(), String> {
		// Enable tracing functionality
		let lit_reverse_map: Arc<Mutex<HashMap<NonZeroI32, LitName>>> = Arc::default();
		let int_reverse_map: Arc<Mutex<Vec<Ustr>>> = Arc::default();
		let subscriber = trace::create_subscriber(
			self.verbose,
			self.stderr.clone(),
			self.ansi_color,
			Arc::clone(&lit_reverse_map),
			Arc::clone(&int_reverse_map),
		);
		let _guard = set_default(subscriber);

		let start = Instant::now();
		let deadline = self.time_limit.map(|t| start + t);

		// Parse FlatZinc JSON file
		let rdr = BufReader::new(
			File::open(&self.path)
				.map_err(|_| format!("Unable to open file “{}”", self.path.display()))?,
		);

		let (mut slv, var_map, output, goal) = match self.format {
			Format::FlatZinc => {
				let fzn: FlatZinc<Ustr> = serde_json::from_reader(rdr).map_err(|_| {
					format!(
						"Unable to parse file “{}” as FlatZinc JSON",
						self.path.display()
					)
				})?;
				// Convert FlatZinc model to internal Solver representation
				let (slv, var_map, fzn_stats) =
					match Solver::from_fzn::<Ustr, UstrMap<View>>(&fzn, &self.init_config()) {
						// Resolve any errors that may have occurred during the conversion
						Err(FlatZincError::ReformulationError(
							ReformulationError::TrivialUnsatisfiable,
						)) => {
							outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
							return Ok(());
						}
						Err(err) => {
							return Err(err.to_string());
						}
						Ok(x) => x,
					};

				if self.statistics {
					let stats = slv.init_statistics();
					self.print_statistics_block(
						"init",
						&[
							("intVariables", &stats.int_vars()),
							("propagators", &stats.propagators()),
							("unifiedVariables", &fzn_stats.unified_variables()),
							("extractedViews", &fzn_stats.extracted_views()),
							(
								"initTime",
								&Instant::now().duration_since(start).as_secs_f64(),
							),
						],
					);
				}

				let output = Output::from_fzn(&fzn, &var_map);

				let goal = if fzn.solve.method != Method::Satisfy {
					let obj_expr = fzn.solve.objective.as_ref().unwrap();
					if let Literal::Identifier(ident) = obj_expr {
						Some((
							if fzn.solve.method == Method::Minimize {
								Goal::Minimize
							} else {
								Goal::Maximize
							},
							if let View::Int(iv) = var_map[ident] {
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

				(slv, var_map, output, goal)
			}
			Format::Xcsp3 => {
				let instance: Xcsp3Instance<Ustr> =
					quick_xml::de::from_reader(rdr).map_err(|err| {
						format!(
							"Unable to parse file “{}” as XCSP3 XML: {}",
							self.path.display(),
							err
						)
					})?;
				let (slv, mut var_map, fzn_stats, goal) = match Solver::from_xcsp3::<
					Ustr,
					UstrMap<Vec<View>>,
				>(&instance, &self.init_config())
				{
					// Resolve any errors that may have occurred during the conversion
					Err(Xcsp3Error::ReformulationError(
						ReformulationError::TrivialUnsatisfiable,
					)) => {
						outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
						return Ok(());
					}
					Err(err) => {
						if matches!(
							err,
							Xcsp3Error::UnsupportedConstraint(_)
								| Xcsp3Error::UnsupportedFeature(_)
								| Xcsp3Error::UnsupportedType(_)
						) {
							outputln!(self.stdout, "s UNSUPPORTED");
						}
						return Err(err.to_string());
					}
					Ok(x) => x,
				};

				if self.statistics {
					let stats = slv.init_statistics();
					self.print_statistics_block(
						"init",
						&[
							("intVariables", &stats.int_vars()),
							("propagators", &stats.propagators()),
							("unifiedVariables", &fzn_stats.unified_variables()),
							("extractedViews", &fzn_stats.extracted_views()),
							(
								"initTime",
								&Instant::now().duration_since(start).as_secs_f64(),
							),
						],
					);
				}

				(
					slv,
					Default::default(),
					Output {
						singletons: instance
							.variables
							.iter()
							.map(|v| (v.identifier, var_map[&v.identifier][0]))
							.collect(),
						arrays: instance
							.arrays
							.iter()
							.map(|a| {
								(
									format!("{}{}", a.identifier, "[]".repeat(a.size.len())).into(),
									var_map.remove(&a.identifier).unwrap(),
								)
							})
							.collect(),
					},
					goal,
				)
			}
		};

		// Create reverse map for solver variables if required
		if self.verbose > 0 {
			let mut lit_map = HashMap::new();
			let mut int_map = vec![ustr(""); slv.init_statistics().int_vars()];
			let mut keys: Vec<_> = var_map.keys().collect();
			keys.sort();
			for name in keys {
				let v = var_map[name];
				match v {
					View::Bool(bv) => {
						if let Some(info) = bv.reverse_map_info() {
							let _ = lit_map.insert(info, LitName::BoolVar(*name, true));
							let _ = lit_map.insert(-info, LitName::BoolVar(*name, false));
						}
					}
					View::Int(iv) => {
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
										IntLitMeaning::Eq(v) => ("=", v),
										IntLitMeaning::NotEq(v) => ("!=", v),
										IntLitMeaning::GreaterEq(v) => (">=", v),
										IntLitMeaning::Less(v) => ("<", v),
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
		drop(var_map);

		// Flat list of output variables (used to create no-goods)
		let output_vars: Vec<_> = output.iter_vars().collect();

		// Set Solver Configuration
		if self.free_search {
			slv.set_vsids_after_conflict(Some(1000));
		} else {
			slv.set_vsids_only(self.vsids_only);
			slv.set_toggle_vsids(self.toggle_vsids);
			slv.set_vsids_after_conflict(self.vsids_after_conflict);
			slv.set_vsids_after_restart(self.vsids_after_restart);
		}

		// Set termination conditions for solver
		let start_solve = Instant::now();
		let interrupt_handling = goal.is_some() && !self.intermediate_solutions;
		let interrupted = Arc::new(AtomicBool::new(false));
		solver_set_terminate(&mut slv, &interrupted, interrupt_handling, deadline);

		// Run the solver!
		let (res, stats) = match goal {
			Some((goal, obj)) => {
				if self.all_solutions {
					warn!("--all-solutions is ignored when optimizing, use --intermediate-solutions or --all-optimal instead");
					self.all_solutions = false;
				}
				let mut no_good_vals = vec![
					Value::Bool(false);
					if self.all_optimal {
						output_vars.len()
					} else {
						0
					}
				];
				let all_opt_slv = if self.all_optimal {
					Some(slv.clone())
				} else {
					None
				};
				let (status, stats, obj_val) = if self.intermediate_solutions {
					slv.branch_and_bound(obj, goal, |value| {
						if self.format == Format::Xcsp3 {
							outputln!(self.stdout, "o {}", value(obj.into()));
						}
						output!(
							self.stdout,
							"{}",
							Solution {
								value,
								format: self.format,
								output: &output,
							}
						);
						if self.all_optimal {
							for (i, &var) in output_vars.iter().enumerate() {
								no_good_vals[i] = value(var);
							}
						}
					})
				} else {
					// Set up Ctrl-C handler (to allow printing last solution)
					if let Err(err) = ctrlc::set_handler({
						let interrupted = Arc::clone(&interrupted);
						move || {
							interrupted.store(true, Ordering::SeqCst);
						}
					}) {
						warn!("unable to set Ctrl-C handler: {}", err);
					}

					let mut last_sol = String::new();
					let res = slv.branch_and_bound(obj, goal, |value| {
						if self.format == Format::Xcsp3 {
							outputln!(self.stdout, "o {}", value(obj.into()));
						}
						last_sol = Solution {
							value,
							format: self.format,
							output: &output,
						}
						.to_string();
						if self.all_optimal {
							for (i, &var) in output_vars.iter().enumerate() {
								no_good_vals[i] = value(var);
							}
						}
					});
					output!(self.stdout, "{}", last_sol);
					res
				};
				if status == SolveResult::Complete && self.all_optimal {
					let mut slv = all_opt_slv.unwrap();
					solver_set_terminate(&mut slv, &interrupted, interrupt_handling, deadline);
					// Ensure all following solutions have the same objective value as the
					// first optimal solution
					let Some(obj_val) = obj_val else {
						unreachable!()
					};
					let obj_lit = slv.get_int_lit(obj, IntLitMeaning::Eq(obj_val));
					slv.add_clause([obj_lit]).unwrap();
					// Ensure all following solutions are different from the first optimal
					// solution
					if slv.add_no_good(&output_vars, &no_good_vals).is_err() {
						(SolveResult::Complete, stats)
					} else {
						// Find remaining optimal solutions
						let (res, stats_all) = slv.all_solutions(&output_vars, |value| {
							output!(
								self.stdout,
								"{}",
								Solution {
									value,
									format: self.format,
									output: &output,
								}
							);
						});
						(res, stats + stats_all)
					}
				} else {
					(status, stats)
				}
			}
			None if self.all_solutions => slv.all_solutions(&output_vars, |value| {
				output!(
					self.stdout,
					"{}",
					Solution {
						value,
						format: self.format,
						output: &output,
					}
				);
			}),
			None => {
				let res = slv.solve(|value| {
					output!(
						self.stdout,
						"{}",
						Solution {
							value,
							format: self.format,
							output: &output,
						}
					);
				});
				(res, slv.search_statistics())
			}
		};
		// Output final solving statistics
		if self.statistics {
			self.print_statistics_block(
				"complete",
				&[
					("solveTime", &(Instant::now() - start_solve).as_secs_f64()),
					("failures", &stats.conflicts()),
					("peakDepth", &stats.peak_depth()),
					("propagations", &stats.cp_propagations()),
					("restarts", &stats.restarts()),
					("oracleDecisions", &stats.oracle_decisions()),
					("userDecisions", &stats.user_decisions()),
				],
			);
		}
		// Print the final solving status
		self.print_result_status(res);
		Ok(())
	}

	/// Print a status message for the given [`SolveResult`] in the enabled
	/// format.
	fn print_result_status(&mut self, result: SolveResult) {
		match self.format {
			Format::FlatZinc => match result {
				SolveResult::Satisfied => {}
				SolveResult::Unsatisfiable => {
					outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
				}
				SolveResult::Unknown => {
					outputln!(self.stdout, "{}", FZN_UNKNOWN);
				}
				SolveResult::Complete => {
					outputln!(self.stdout, "{}", FZN_COMPLETE);
				}
			},
			Format::Xcsp3 => match result {
				SolveResult::Satisfied => {
					outputln!(self.stdout, "s SATISFIABLE");
				}
				SolveResult::Unsatisfiable => {
					outputln!(self.stdout, "s UNSATISFIABLE");
				}
				SolveResult::Unknown => {
					outputln!(self.stdout, "s UNKNOWN");
				}
				SolveResult::Complete if self.all_solutions => {
					outputln!(self.stdout, "s ALL SATISFIABLE");
				}
				SolveResult::Complete if self.all_optimal => {
					outputln!(self.stdout, "s ALL OPTIMAL");
				}
				SolveResult::Complete => {
					outputln!(self.stdout, "s OPTIMUM FOUND");
				}
			},
		}
	}

	/// Print a statistics block formulated for the chosen format
	fn print_statistics_block(&mut self, name: &str, stats: &[(&str, &dyn Debug)]) {
		match self.format {
			Format::FlatZinc => {
				outputln!(self.stdout, "%%%mzn-stat: blockType={:?}", name);
				for stat in stats {
					outputln!(self.stdout, "%%%mzn-stat: {}={:?}", stat.0, stat.1);
				}
				outputln!(self.stdout, "%%%mzn-stat-end");
			}
			Format::Xcsp3 => {
				for stat in stats {
					outputln!(self.stdout, "d {} {:?}", stat.0, stat.1);
				}
			}
		}
	}

	/// Set the writer that is used for error, warning, and other logging
	/// messages.
	pub fn with_stderr<W>(self, stderr: W, ansi_color: bool) -> Cli<Stdout, W>
	where
		W: Clone + for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
	{
		Cli {
			stderr,
			ansi_color,
			// Copy the rest of the fields
			path: self.path,
			all_solutions: self.all_solutions,
			all_optimal: self.all_optimal,
			intermediate_solutions: self.intermediate_solutions,
			free_search: self.free_search,
			statistics: self.statistics,
			time_limit: self.time_limit,
			verbose: self.verbose,
			int_eager_limit: self.int_eager_limit,
			restart: self.restart,
			toggle_vsids: self.toggle_vsids,
			preprocessing: self.preprocessing,
			inprocessing: self.inprocessing,
			vivification: self.vivification,
			subsumption: self.subsumption,
			variable_elimination: self.variable_elimination,
			probing: self.probing,
			conditioning: self.conditioning,
			vsids_after_conflict: self.vsids_after_conflict,
			vsids_after_restart: self.vsids_after_restart,
			vsids_only: self.vsids_only,
			stdout: self.stdout,
			format: self.format,
		}
	}

	/// Set the writer that is used for the standard (solution) output.
	pub fn with_stdout<W: io::Write>(self, stdout: W) -> Cli<W, Stderr> {
		Cli {
			stdout,
			// Copy the rest of the fields
			path: self.path,
			all_solutions: self.all_solutions,
			all_optimal: self.all_optimal,
			intermediate_solutions: self.intermediate_solutions,
			free_search: self.free_search,
			statistics: self.statistics,
			time_limit: self.time_limit,
			verbose: self.verbose,
			int_eager_limit: self.int_eager_limit,
			restart: self.restart,
			toggle_vsids: self.toggle_vsids,
			preprocessing: self.preprocessing,
			inprocessing: self.inprocessing,
			vivification: self.vivification,
			subsumption: self.subsumption,
			variable_elimination: self.variable_elimination,
			probing: self.probing,
			conditioning: self.conditioning,
			vsids_after_conflict: self.vsids_after_conflict,
			vsids_after_restart: self.vsids_after_restart,
			vsids_only: self.vsids_only,
			stderr: self.stderr,
			ansi_color: self.ansi_color,
			format: self.format,
		}
	}
}

impl TryFrom<Arguments> for Cli<io::Stdout, fn() -> io::Stderr> {
	type Error = String;

	fn try_from(mut args: Arguments) -> Result<Self, Self::Error> {
		let mut verbose = 0;
		while args.contains(["-v", "--verbose"]) {
			verbose += 1;
		}

		let parse_bool_arg = |s: &str| match s {
			"true" | "on" | "1" => Ok(true),
			"false" | "off" | "0" => Ok(false),
			_ => Err(format!(
				"expected 'true','false','on','off','0', or '1', found '{}'",
				s
			)),
		};

		let mut cli = Cli {
			all_solutions: args.contains(["-a", "--all-solutions"]),
			all_optimal: args.contains("--all-optimal"),
			intermediate_solutions: args.contains(["-i", "--intermediate-solutions"]),
			free_search: args.contains(["-f", "--free-search"]),
			statistics: args.contains(["-s", "--statistics"]),
			time_limit: args
				.opt_value_from_fn(["-t", "--time-limit"], parse_time_limit)
				.map_err(|e| e.to_string())?,

			int_eager_limit: args
				.opt_value_from_str("--int-eager-limit")
				.map_err(|e| e.to_string())?,

			restart: args
				.opt_value_from_fn("--restart", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			toggle_vsids: args.contains("--toggle-vsids"),
			vsids_after_conflict: args
				.opt_value_from_str("--vsids-after-conflict")
				.map_err(|e| e.to_string())?,
			vsids_after_restart: args.contains("--vsids-after-restart"),
			vsids_only: args.contains("--vsids-only"),

			conditioning: args
				.opt_value_from_fn("--conditioning", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			inprocessing: args
				.opt_value_from_fn("--inprocessing", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			preprocessing: args
				.opt_value_from_str("--preprocessing")
				.map_err(|e| e.to_string())?,
			probing: args
				.opt_value_from_fn("--probing", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			variable_elimination: args
				.opt_value_from_fn("--variable-elimination", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			vivification: args
				.opt_value_from_fn("--vivify", parse_bool_arg)
				.map(|x| x.unwrap_or(false)) // TODO: investigate whether this can be re-enabled
				.map_err(|e| e.to_string())?,
			subsumption: args
				.opt_value_from_fn("--subsumption", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,

			verbose,
			path: args
				.free_from_os_str(|s| -> Result<PathBuf, &'static str> { Ok(s.into()) })
				.map_err(|e| e.to_string())?,

			stdout: io::stdout(),
			#[expect(trivial_casts, reason = "doesn't compile without the case")]
			stderr: io::stderr as fn() -> io::Stderr,
			ansi_color: true,

			format: Format::FlatZinc, // Set to default
		};

		// Check whether there are any unexpected arguments remaining
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

		// Initialize the correct input format based on the file extension.
		match cli.path.extension().and_then(OsStr::to_str) {
			Some("xml") => {
				cli.format = Format::Xcsp3;
			}
			_ => {
				if !cli.path.ends_with(".fzn.json") {
					warn!(
						"Model file with unknown extension “{}”, assuming FlatZinc JSON file",
						cli.path.to_string_lossy()
					);
				}
			}
		}

		Ok(cli)
	}
}

impl Output {
	/// Iterate over all variables mentioned in the output specifications, both
	/// single variables and variables contained in arrays.
	fn iter_vars(&self) -> impl Iterator<Item = View> + '_ {
		self.singletons.iter().map(|(_, var)| *var).chain(
			self.arrays
				.iter()
				.flat_map(|(_, vars)| vars.iter().copied()),
		)
	}

	/// Extract the output definition from a [`FlatZinc`] instance.
	fn from_fzn(fzn: &FlatZinc<Ustr>, var_map: &UstrMap<View>) -> Self {
		let mut arrays = Vec::new();
		let mut singletons = Vec::new();
		for &ident in &fzn.output {
			match fzn.arrays.get(&ident) {
				Some(arr) => {
					let vars = arr
						.contents
						.iter()
						.map(|x| match x {
							Literal::Int(i) => IntView::from(*i).into(),
							Literal::Identifier(ident) => var_map[ident],
							Literal::Bool(b) => BoolView::from(*b).into(),
							_ => unimplemented!("unsupported output type"),
						})
						.collect();
					arrays.push((ident, vars));
				}
				None => singletons.push((ident, var_map[&ident])),
			}
		}
		Self { arrays, singletons }
	}
}

impl Display for Solution<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.format {
			Format::FlatZinc => {
				for &(ident, var) in &self.output.singletons {
					writeln!(f, "{ident} = {};", (self.value)(var))?;
				}
				for (ident, vars) in &self.output.arrays {
					writeln!(
						f,
						"{ident} = [{}];",
						vars.iter()
							.map(|var| format!("{}", (self.value)(*var)))
							.collect::<Vec<_>>()
							.join(",")
					)?;
				}
				writeln!(f, "{}", FZN_SEPERATOR)
			}
			Format::Xcsp3 => {
				writeln!(f, "v <instantiation>")?;
				write!(f, "v <list> ")?;
				for i in self
					.output
					.singletons
					.iter()
					.map(|(i, _)| i)
					.chain(self.output.arrays.iter().map(|(i, _)| i))
				{
					write!(f, "{} ", i)?;
				}
				writeln!(f, "</list>")?;
				write!(f, "v <values> ")?;
				for i in self
					.output
					.singletons
					.iter()
					.map(|(_, v)| v)
					.chain(self.output.arrays.iter().flat_map(|(_, vs)| vs))
				{
					write!(f, "{} ", (*self.value)(*i))?;
				}
				writeln!(f, "</values>")?;
				writeln!(f, "v </instantiation>")
			}
		}
	}
}

#[cfg(test)]
mod tests {
	// Used by integration testing and benchmarks
	use divan as _;
	use expect_test as _;
}
