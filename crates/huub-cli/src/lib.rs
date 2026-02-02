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

mod interned_str;
mod trace;

use std::{
	fmt::{self, Debug, Display},
	fs::File,
	io::{self, BufReader},
	num::NonZeroI32,
	path::PathBuf,
	sync::{
		Arc, Mutex,
		atomic::{AtomicBool, Ordering},
	},
	time::{Duration, Instant},
};

use flatzinc_serde::{FlatZinc, Literal};
use huub::{
	Goal, TerminationSignal,
	actions::IntDecisionActions,
	lower::{InitConfig, LoweringError},
	model::deserialize::flatzinc::FlatZincError,
	solver::{AnyView, IntLitMeaning, Solution, Solver, Status, Value},
};
use mimalloc::MiMalloc;
use pico_args::Arguments;
use rustc_hash::FxHashMap;
use tracing::{subscriber::set_default, warn};
use tracing_subscriber::fmt::MakeWriter;

use crate::{interned_str::InternedStr, trace::LitName};

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

/// Use [`MiMalloc`] as the global allocator.
#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

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
	/// Whether to enable inprocessing during search in the SAT solver
	inprocessing: bool,
	/// The number of preprocessing rounds in the SAT solver
	preprocessing: Option<usize>,
	/// Whether to enable the failed literal probing in the SAT solver.
	probing: bool,
	/// Whether to enable asking for explanation clauses for all literals
	/// propagated on the level of a conflict.
	reason_eager: bool,
	/// Whether to enable the global forward subsumption in the SAT solver.
	subsumption: bool,
	/// Whether to enable the bounded variable elimination in the SAT solver.
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
}

/// Solution struct to display the results of the solver
struct SolutionWrap<'a> {
	/// FlatZinc instance
	fzn: &'a FlatZinc<InternedStr>,
	/// Mapping from solver views to solution values
	sol: Solution<'a>,
	/// Mapping from FlatZinc identifiers to solver views
	var_map: &'a FxHashMap<InternedStr, AnyView>,
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

/// Print a statistics block formulated for MiniZinc
fn print_statistics_block<W: io::Write>(stream: &mut W, name: &str, stats: &[(&str, &dyn Debug)]) {
	outputln!(stream, "%%%mzn-stat: blockType={:?}", name);
	for stat in stats {
		outputln!(stream, "%%%mzn-stat: {}={:?}", stat.0, stat.1);
	}
	outputln!(stream, "%%%mzn-stat-end");
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
			.with_reason_eager(self.reason_eager)
			.with_restart(self.free_search || self.restart)
			.with_subsumption(self.subsumption)
			.with_variable_elimination(self.variable_elimination)
			.with_vivification(self.vivification);

		config
	}

	/// Run the Huub solver in accordance to the given command line arguments.
	pub fn run(&mut self) -> Result<(), String> {
		// Enable tracing functionality
		let lit_reverse_map: Arc<Mutex<FxHashMap<NonZeroI32, LitName>>> = Arc::default();
		let int_reverse_map: Arc<Mutex<Vec<InternedStr>>> = Arc::default();
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
		let fzn: FlatZinc<InternedStr> = serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?;

		// Convert FlatZinc model to internal Solver representation and resolve any
		// errors that may have occurred during the conversion
		let (mut slv, meta) = match Solver::from_fzn(&fzn, &self.init_config()) {
			Err(FlatZincError::ReformulationError(
				LoweringError::Simplification(_) | LoweringError::Lowering(_),
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
			print_statistics_block(
				&mut self.stdout,
				"init",
				&[
					("intVariables", &stats.int_vars()),
					("propagators", &stats.propagators()),
					("unifiedVariables", &meta.stats.unified_variables()),
					("extractedViews", &meta.stats.extracted_views()),
					(
						"initTime",
						&Instant::now().duration_since(start).as_secs_f64(),
					),
				],
			);
		}

		// Create reverse map for solver variables if required
		if self.verbose > 0 {
			let mut lit_map = lit_reverse_map.lock().unwrap();
			let mut int_map = int_reverse_map.lock().unwrap();
			debug_assert!(int_map.is_empty());
			*int_map = vec![InternedStr::default(); slv.init_statistics().int_vars()];
			for (name, v) in &meta.names {
				match v {
					AnyView::Bool(bv) => {
						if let Some(info) = bv.reverse_map_info() {
							lit_map.insert(info, LitName::BoolVar(*name, true));
							lit_map.insert(-info, LitName::BoolVar(*name, false));
						}
					}
					AnyView::Int(iv) => {
						let (pos, is_view) = iv.int_reverse_map_info();
						if let Some(i) = pos {
							if !is_view || int_map[i as usize].is_empty() {
								int_map[i as usize] = *name;
								for (lit, meaning) in iv.lit_reverse_map_info(&slv) {
									lit_map.insert(lit, LitName::IntLit(i, meaning));
								}
							} else {
								debug_assert!(
									iv.lit_reverse_map_info(&slv)
										.iter()
										.all(|(lit, _)| { lit_map.contains_key(lit) })
								);
							}
						} else {
							debug_assert!(is_view);
							for (lit, meaning) in iv.lit_reverse_map_info(&slv) {
								lit_map.entry(lit).or_insert_with(|| {
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
		}

		// Set Solver Configuration
		if self.free_search {
			slv.set_vsids_after_conflict(Some(1000));
		} else {
			slv.set_vsids_only(self.vsids_only);
			slv.set_toggle_vsids(self.toggle_vsids);
			slv.set_vsids_after_conflict(self.vsids_after_conflict);
			slv.set_vsids_after_restart(self.vsids_after_restart);
		}

		let start_solve = Instant::now();
		// Set termination conditions for solver
		let interrupt_handling = meta.goal.is_some() && !self.intermediate_solutions;
		let interrupted = Arc::new(AtomicBool::new(false));
		match (interrupt_handling, deadline) {
			(true, Some(deadline)) => {
				let interrupted = Arc::clone(&interrupted);
				slv.set_terminate_callback(Some(move || {
					if interrupted.load(Ordering::SeqCst) || Instant::now() >= deadline {
						TerminationSignal::Terminate
					} else {
						TerminationSignal::Continue
					}
				}));
			}
			(true, None) => {
				let interrupted = Arc::clone(&interrupted);
				slv.set_terminate_callback(Some(move || {
					if interrupted.load(Ordering::SeqCst) {
						TerminationSignal::Terminate
					} else {
						TerminationSignal::Continue
					}
				}));
			}
			(false, Some(deadline)) => {
				slv.set_terminate_callback(Some(move || {
					if Instant::now() >= deadline {
						TerminationSignal::Terminate
					} else {
						TerminationSignal::Continue
					}
				}));
			}
			_ => {}
		};

		// Variables that the user is interested in
		let output_vars: Vec<_> = fzn
			.output
			.iter()
			.flat_map(|ident| {
				if let Some(arr) = fzn.arrays.get(ident) {
					arr.contents
						.iter()
						.filter_map(|lit| {
							if let Literal::Identifier(ident) = lit {
								Some(meta.names[ident])
							} else {
								None
							}
						})
						.collect()
				} else {
					vec![meta.names[ident]]
				}
			})
			.collect();
		// Run the solver!
		let (res, stats) = match meta.goal {
			Some(goal) => {
				if self.all_solutions {
					warn!(
						"--all-solutions is ignored when optimizing, use --intermediate-solutions or --all-optimal instead"
					);
				}
				let mut no_good_vals = vec![
					Value::Bool(false);
					if self.all_optimal {
						output_vars.len()
					} else {
						0
					}
				];
				// TODO: Fix statistics
				let all_opt_slv = if self.all_optimal {
					Some(slv.clone())
				} else {
					None
				};
				let (status, stats, obj_val) = if self.intermediate_solutions {
					slv.branch_and_bound(goal, |sol| {
						output!(
							self.stdout,
							"{}",
							SolutionWrap {
								sol,
								fzn: &fzn,
								var_map: &meta.names
							}
						);
						if self.all_optimal {
							for (i, var) in output_vars.iter().enumerate() {
								no_good_vals[i] = var.val(sol);
							}
						}
					})
				} else {
					// Set up Ctrl-C handler (to allow printing last solution)
					if let Err(err) = ctrlc::set_handler(move || {
						interrupted.store(true, Ordering::SeqCst);
					}) {
						warn!("unable to set Ctrl-C handler: {}", err);
					}

					let mut last_sol = String::new();
					let res = slv.branch_and_bound(goal, |sol| {
						last_sol = SolutionWrap {
							sol,
							fzn: &fzn,
							var_map: &meta.names,
						}
						.to_string();
						if self.all_optimal {
							for (i, var) in output_vars.iter().enumerate() {
								no_good_vals[i] = var.val(sol);
							}
						}
					});
					output!(self.stdout, "{}", last_sol);
					res
				};
				if status == Status::Complete && self.all_optimal {
					let mut slv = all_opt_slv.unwrap();
					// Ensure all following solutions have the same objective value as the
					// first optimal solution
					let Some(obj_val) = obj_val else {
						unreachable!()
					};
					match goal {
						Goal::Minimize(obj) | Goal::Maximize(obj) => {
							let obj_lit = obj.lit(&mut slv, IntLitMeaning::Eq(obj_val));
							slv.add_clause([obj_lit]).unwrap();
						}
						_ => panic!("unknown optimization goal"),
					}
					// Ensure all following solutions are different from the first optimal
					// solution
					if slv.add_no_good(&output_vars, &no_good_vals).is_err() {
						(Status::Complete, stats)
					} else {
						// Find remaining optimal solutions
						let (res, stats_all) = slv.all_solutions(&output_vars, |sol| {
							output!(
								self.stdout,
								"{}",
								SolutionWrap {
									sol,
									fzn: &fzn,
									var_map: &meta.names
								}
							);
						});
						(res, stats + stats_all)
					}
				} else {
					(status, stats)
				}
			}
			None if self.all_solutions => slv.all_solutions(&output_vars, |sol| {
				output!(
					self.stdout,
					"{}",
					SolutionWrap {
						sol,
						fzn: &fzn,
						var_map: &meta.names
					}
				);
			}),
			None => {
				let res = slv.solve(|sol| {
					output!(
						self.stdout,
						"{}",
						SolutionWrap {
							sol,
							fzn: &fzn,
							var_map: &meta.names
						}
					);
				});
				(res, slv.search_statistics())
			}
		};
		// output solving statistics
		if self.statistics {
			print_statistics_block(
				&mut self.stdout,
				"complete",
				&[
					("solveTime", &(Instant::now() - start_solve).as_secs_f64()),
					("failures", &stats.conflicts()),
					("peakDepth", &stats.peak_depth()),
					("propagations", &stats.cp_propagations()),
					("restarts", &stats.restarts()),
					("satDecisions", &stats.sat_decisions()),
					("userDecisions", &stats.user_decisions()),
				],
			);
		}
		match res {
			Status::Satisfied => {}
			Status::Unsatisfiable => {
				outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
			}
			Status::Unknown => {
				outputln!(self.stdout, "{}", FZN_UNKNOWN);
			}
			Status::Complete => {
				outputln!(self.stdout, "{}", FZN_COMPLETE);
			}
		}
		Ok(())
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
			reason_eager: self.reason_eager,
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
			reason_eager: self.reason_eager,
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
				"expected 'true','false','on','off','0', or '1', found '{s}'"
			)),
		};

		let cli = Cli {
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

			reason_eager: args
				.opt_value_from_fn("--reason-eager", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
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

impl SolutionWrap<'_> {
	/// Method used to print a literal that is part of a solution.
	fn print_lit(&self, lit: &Literal<InternedStr>) -> String {
		match lit {
			Literal::Int(i) => format!("{i}"),
			Literal::Float(f) => format!("{f}"),
			Literal::Identifier(ident) => {
				format!("{}", self.var_map[ident].val(self.sol))
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

impl Display for SolutionWrap<'_> {
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
				)?;
			} else {
				writeln!(f, "{ident} = {};", self.var_map[ident].val(self.sol))?;
			}
		}
		writeln!(f, "{FZN_SEPERATOR}")
	}
}

#[cfg(test)]
mod tests {
	// Used by integration testing and benchmarks
	use divan as _;
	use expect_test as _;
}
