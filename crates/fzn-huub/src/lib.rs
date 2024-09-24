mod trace;

use std::{
	collections::HashMap,
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
	FlatZincError, FlatZincStatistics, Goal, InitConfig, LitMeaning, ReformulationError,
	SlvTermSignal, SolveResult, Solver, SolverView, Valuation,
};
use pico_args::Arguments;
use tracing::{subscriber::set_default, warn};
use tracing_subscriber::fmt::MakeWriter;
use ustr::{ustr, Ustr, UstrMap};

use crate::trace::LitName;

const FZN_COMPLETE: &str = "==========";
const FZN_SEPERATOR: &str = "----------";
const FZN_UNKNOWN: &str = "=====UNKNOWN=====";
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====";

macro_rules! outputln {
	($($arg:tt)*) => {
		writeln!($($arg)*).expect("unable to write to output stream")
	};
}
macro_rules! output {
	($($arg:tt)*) => {
		write!($($arg)*).expect("unable to write to output stream")
	};
}

/// FlatZinc command line interface for the Huub solver
///
/// This interface is intended to connect Huub with MiniZinc
#[derive(Debug)]
pub struct Cli<Stdout, Stderr> {
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

	// --- Initialization configuration ---
	/// Cardinatility cutoff for eager order literals
	int_eager_limit: Option<usize>,

	// --- Solving configuration ---
	/// Whether solver is allowed to restart
	restart: bool,
	/// Alternate between the SAT and VSIDS heuristic after every restart
	toggle_vsids: bool,
	/// Whether the vivification heuristic is enabled
	vivification: bool,
	/// Switch to the VSIDS heuristic after a certain number of conflicts
	vsids_after: Option<u32>,
	/// Only use the SAT VSIDS heuristic for search
	vsids_only: bool,

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
struct Solution<'a> {
	value: &'a dyn Valuation,
	fzn: &'a FlatZinc<Ustr>,
	var_map: &'a UstrMap<SolverView>,
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
	fn init_config(&self) -> InitConfig {
		let mut config = InitConfig::default();
		if let Some(eager_limit) = self.int_eager_limit {
			config = config.with_int_eager_limit(eager_limit);
		}
		config = config
			.with_restart(self.free_search || self.restart)
			.with_vivification(self.vivification);
		config
	}

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
		let fzn: FlatZinc<Ustr> = serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?;

		// Convert FlatZinc model to internal Solver representation
		let res = Solver::from_fzn(&fzn, &self.init_config());
		// Resolve any errors that may have occurred during the conversion
		let (mut slv, var_map, fzn_stats): (Solver, UstrMap<SolverView>, FlatZincStatistics) =
			match res {
				Err(FlatZincError::ReformulationError(
					ReformulationError::TrivialUnsatisfiable,
				)) => {
					outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
					return Ok(());
				}
				Err(err) => {
					return Err(err.to_string());
				}
				Ok((slv, var_map, fzn_stats)) => (slv, var_map.into_iter().collect(), fzn_stats),
			};

		if self.statistics {
			let stats = slv.init_statistics();
			print_statistics_block(
				&mut self.stdout,
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
					warn!("--all-solutions is ignored when optimizing, use --intermediate-solutions or --all-optimal-solutions instead");
				}
				if self.intermediate_solutions {
					slv.branch_and_bound(obj, goal, |value| {
						output!(
							self.stdout,
							"{}",
							Solution {
								value,
								fzn: &fzn,
								var_map: &var_map
							}
						);
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
						.to_string();
					});
					output!(self.stdout, "{}", last_sol);
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
					output!(
						self.stdout,
						"{}",
						Solution {
							value,
							fzn: &fzn,
							var_map: &var_map
						}
					);
				})
			}
			None => slv.solve(|value| {
				output!(
					self.stdout,
					"{}",
					Solution {
						value,
						fzn: &fzn,
						var_map: &var_map
					}
				);
			}),
		};
		// output solving statistics
		if self.statistics {
			let stats = slv.search_statistics();
			print_statistics_block(
				&mut self.stdout,
				"complete",
				&[
					("solveTime", &(Instant::now() - start_solve).as_secs_f64()),
					("failures", &stats.conflicts()),
					("peakDepth", &stats.peak_depth()),
					("propagations", &stats.propagations()),
					("restarts", &stats.restarts()),
					("oracleDecisions", &stats.oracle_decisions()),
					("userDecisions", &stats.user_decisions()),
				],
			);
		}
		match res {
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
		}
		Ok(())
	}

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
			intermediate_solutions: self.intermediate_solutions,
			free_search: self.free_search,
			statistics: self.statistics,
			time_limit: self.time_limit,
			verbose: self.verbose,
			int_eager_limit: self.int_eager_limit,
			restart: self.restart,
			toggle_vsids: self.toggle_vsids,
			vivification: self.vivification,
			vsids_after: self.vsids_after,
			vsids_only: self.vsids_only,
			stdout: self.stdout,
		}
	}

	pub fn with_stdout<W: io::Write>(self, stdout: W) -> Cli<W, Stderr> {
		Cli {
			stdout,
			// Copy the rest of the fields
			path: self.path,
			all_solutions: self.all_solutions,
			intermediate_solutions: self.intermediate_solutions,
			free_search: self.free_search,
			statistics: self.statistics,
			time_limit: self.time_limit,
			verbose: self.verbose,
			int_eager_limit: self.int_eager_limit,
			restart: self.restart,
			toggle_vsids: self.toggle_vsids,
			vivification: self.vivification,
			vsids_after: self.vsids_after,
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
				"expected 'true','false','on','off','0', or '1', found '{}'",
				s
			)),
		};

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

			restart: args
				.opt_value_from_fn("--restart", parse_bool_arg)
				.map(|x| x.unwrap_or(false))
				.map_err(|e| e.to_string())?,
			toggle_vsids: args.contains("--toggle-vsids"),
			vivification: args
				.opt_value_from_fn("--vivify", parse_bool_arg)
				.map(|x| x.unwrap_or(false)) // TODO: investigate whether this can be re-enabled
				.map_err(|e| e.to_string())?,
			vsids_only: args.contains("--vsids-only"),
			vsids_after: args
				.opt_value_from_str("--vsids-after")
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
				)?;
			} else {
				writeln!(
					f,
					"{ident} = {};",
					(self.value)(self.var_map[ident]).unwrap()
				)?;
			}
		}
		writeln!(f, "{}", FZN_SEPERATOR)
	}
}

#[cfg(test)]
mod tests {
	// Used by integration testing and benchmarks
	use codspeed_criterion_compat as _;
	use expect_test as _;
}
