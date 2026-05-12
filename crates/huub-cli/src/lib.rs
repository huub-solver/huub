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

mod cli;
mod trace;

use std::{
	fmt::{self, Debug, Display},
	io,
	num::NonZeroI32,
	sync::{
		Arc, Mutex,
		atomic::{AtomicBool, Ordering},
	},
	time::Instant,
};

use flatzinc_serde::{FlatZinc, Literal, NamedRef, Variable, helpers::ArcKey};
use huub::{
	lower::LoweringError,
	model::deserialize::{
		Goal,
		flatzinc::{FlatZincError, FznIdent, HuubFlatZinc},
	},
	solver::{
		AnyView, SearchStrategy, Solution, Solver, Status, SwitchTrigger, TerminationSignal,
		Valuation,
	},
};
use mimalloc::MiMalloc;
use rustc_hash::FxHashMap;
use tracing::{subscriber::set_default, warn};

pub use crate::cli::Cli;
use crate::{
	cli::{CliSearchStrategy, CliSearchTrigger},
	trace::{LitName, VarRef},
};

/// Status message to output when it is proven that no more/better solutions can
/// be found.
const FZN_COMPLETE: &str = "==========";
/// Separator to output between solutions.
const FZN_SEPARATOR: &str = "----------";
/// Status message to output when no solution is found within the time limit,
/// but the problem is not proven to be unsatisfiable.
const FZN_UNKNOWN: &str = "=====UNKNOWN=====";
/// Status message to output when a problem is proven to be unsatisfiable.
const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====";

/// Use [`MiMalloc`] as the global allocator.
#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Solution struct to display the results of the solver
struct SolutionWrap<'a> {
	/// FlatZinc instance
	fzn: &'a FlatZinc<FznIdent>,
	/// Mapping from solver views to solution values
	sol: Solution<'a>,
	/// Mapping from FlatZinc identifiers to solver views
	var_map: &'a FxHashMap<ArcKey<Variable<FznIdent>>, AnyView>,
}

/// Print a statistics block formulated for MiniZinc
fn print_statistics_block<W: io::Write>(stream: &mut W, name: &str, stats: &[(&str, &dyn Debug)]) {
	outputln!(stream, "%%%mzn-stat: blockType={:?}", name);
	for stat in stats {
		outputln!(stream, "%%%mzn-stat: {}={:?}", stat.0, stat.1);
	}
	outputln!(stream, "%%%mzn-stat-end");
}

impl<'a> Cli<'a> {
	/// Run the Huub solver in accordance to the given command line arguments.
	pub fn run(&mut self) -> Result<(), String> {
		let (trace_writer, ansi_color) = self.trace_writer()?;
		let trace_targets = self.trace_targets();
		let lit_reverse_map: Arc<Mutex<FxHashMap<NonZeroI32, LitName>>> = Arc::default();
		let int_reverse_map: Arc<Mutex<Vec<Option<VarRef>>>> = Arc::default();
		let subscriber = trace::create_subscriber(
			self.verbose,
			&trace_targets,
			trace_writer,
			ansi_color,
			Arc::clone(&lit_reverse_map),
			Arc::clone(&int_reverse_map),
		);
		let _guard = set_default(subscriber);

		let start = Instant::now();
		let deadline = self.time_limit.map(|t| start + t);

		let rdr = io::BufReader::new(
			std::fs::File::open(&self.path)
				.map_err(|_| format!("Unable to open file “{}”", self.path.display()))?,
		);
		let fzn: FlatZinc<_> = serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?;

		let (mut slv, meta): (Solver, _) = match fzn
			.lower()
			.int_eager_limit(self.int_eager_limit)
			.preprocessing(self.preprocessing)
			.conditioning(self.conditioning)
			.inprocessing(self.inprocessing)
			.probing(self.probing)
			.reason_eager(self.reason_eager)
			.restart(self.free_search || self.restart)
			.subsumption(self.subsumption)
			.variable_elimination(self.variable_elimination)
			.vivification(self.vivification)
			.to_solver()
		{
			Err(FlatZincError::ReformulationError(
				LoweringError::Simplification(_) | LoweringError::Lowering(_),
			)) => {
				outputln!(self.stdout, "{}", FZN_UNSATISFIABLE);
				return Ok(());
			}
			Err(err) => return Err(err.to_string()),
			Ok(x) => x,
		};

		if self.statistics {
			let stats = slv.init_statistics();
			print_statistics_block(
				&mut self.stdout,
				"init",
				&[
					("boolDecisions", &stats.bool_decisions),
					("intDecisions", &stats.int_decisions),
					("propagators", &stats.propagators),
					("unifiedDecisions", &meta.stats.unified_decisions),
					("extractedViews", &meta.stats.extracted_views),
					(
						"initTime",
						&Instant::now().duration_since(start).as_secs_f64(),
					),
				],
			);
		}

		if self.verbose > 0 {
			let mut lit_map = lit_reverse_map.lock().unwrap();
			let mut int_map = int_reverse_map.lock().unwrap();
			debug_assert!(int_map.is_empty());
			*int_map = vec![None; slv.init_statistics().int_decisions];
			for (var, v) in &meta.names {
				match v {
					AnyView::Bool(bv) => {
						let var: VarRef = var.clone().into();
						if let Some(info) = bv.reverse_map_info() {
							lit_map.insert(info, LitName::BoolVar(Arc::clone(&var), true));
							lit_map.insert(-info, LitName::BoolVar(var, false));
						}
					}
					AnyView::Int(iv) => {
						let var: VarRef = var.clone().into();
						let (pos, is_view) = iv.int_reverse_map_info();
						if let Some(i) = pos {
							if !is_view || int_map[i as usize].is_none() {
								int_map[i as usize] = Some(Arc::clone(&var));
								for (lit, meaning) in iv.lit_reverse_map_info(&slv) {
									lit_map.insert(lit, LitName::IntLit(Arc::clone(&var), meaning));
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
								lit_map
									.entry(lit)
									.or_insert_with(|| LitName::IntLit(Arc::clone(&var), meaning));
							}
						}
					}
				}
			}
		}

		let trigger = match self.search_trigger {
			CliSearchTrigger::Conflicts => SwitchTrigger::Conflicts,
			CliSearchTrigger::Restarts => SwitchTrigger::Restarts,
		};
		let trigger = trigger(self.search_interval);
		let strategy = match self.search_strategy {
			_ if self.free_search => SearchStrategy::Transition(SwitchTrigger::Conflicts(1000)),
			CliSearchStrategy::Branchers => SearchStrategy::Branchers,
			CliSearchStrategy::Sat => SearchStrategy::Sat,
			CliSearchStrategy::Transition => SearchStrategy::Transition(trigger),
			CliSearchStrategy::Interleaved => SearchStrategy::Interleaved(trigger),
		};
		slv.set_search_strategy(strategy);

		let start_solve = Instant::now();
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

		let output_vars: Vec<_> = fzn
			.output
			.iter()
			.flat_map(|named_ref| match named_ref {
				NamedRef::Variable(var) => vec![meta.names[&var.cloned_key()]],
				NamedRef::Array(arr) => arr
					.contents
					.iter()
					.filter_map(|lit| {
						if let Literal::Variable(var) = lit {
							Some(meta.names[&var.cloned_key()])
						} else {
							None
						}
					})
					.collect(),
			})
			.collect();
		let res = match meta.goal {
			Some(goal) => {
				if self.all_solutions {
					warn!(
						target: "solver",
						"ignore --all-solutions when optimizing; use --intermediate-solutions or --all-optimal instead"
					);
				}
				if self.intermediate_solutions {
					let solve = slv
						.solve()
						.bind_using_clauses(true)
						.on_solution(|sol| {
							output!(
								self.stdout,
								"{}",
								SolutionWrap {
									sol,
									fzn: &fzn,
									var_map: &meta.names
								}
							);
						})
						.maybe_all_solutions(self.all_optimal.then(|| output_vars.clone()));
					match goal {
						Goal::Minimize(obj) => solve.minimize(obj),
						Goal::Maximize(obj) => solve.maximize(obj),
						_ => panic!("unknown optimization goal"),
					}
					.0
				} else {
					if let Err(err) = ctrlc::set_handler(move || {
						interrupted.store(true, Ordering::SeqCst);
					}) {
						warn!(target: "solver", error = %err, "unable to set ctrl-c handler");
					}

					let obj_dcn = match goal {
						Goal::Minimize(obj) => obj,
						Goal::Maximize(obj) => obj,
						_ => panic!("unknown optimization goal"),
					};
					let mut last_obj = None;
					let mut last_sol = String::new();
					let solve = slv
						.solve()
						.bind_using_clauses(!self.all_optimal)
						.on_solution(|sol| {
							if last_obj == Some(obj_dcn.val(sol)) {
								if !last_sol.is_empty() {
									output!(self.stdout, "{}", last_sol);
									last_sol = String::new();
								}
								output!(
									self.stdout,
									"{}",
									SolutionWrap {
										sol,
										fzn: &fzn,
										var_map: &meta.names
									}
								);
							} else {
								last_sol = SolutionWrap {
									sol,
									fzn: &fzn,
									var_map: &meta.names,
								}
								.to_string();
								last_obj = Some(obj_dcn.val(sol));
							}
						})
						.maybe_all_solutions(self.all_optimal.then(|| output_vars.clone()));
					let (status, _obj) = match goal {
						Goal::Minimize(obj) => solve.minimize(obj),
						Goal::Maximize(obj) => solve.maximize(obj),
						_ => panic!("unknown optimization goal"),
					};
					if !last_sol.is_empty() {
						output!(self.stdout, "{}", last_sol);
					}
					status
				}
			}
			None => slv
				.solve()
				.bind_using_clauses(true)
				.on_solution(|sol| {
					output!(
						self.stdout,
						"{}",
						SolutionWrap {
							sol,
							fzn: &fzn,
							var_map: &meta.names
						}
					);
				})
				.maybe_all_solutions(self.all_solutions.then(|| output_vars.clone()))
				.satisfy(),
		};
		if self.statistics {
			let stats = slv.solver_statistics();
			print_statistics_block(
				&mut self.stdout,
				"complete",
				&[
					("solveTime", &(Instant::now() - start_solve).as_secs_f64()),
					("failures", &stats.conflicts),
					("restarts", &stats.restarts),
					("peakDepth", &stats.peak_depth),
					("cpPropagatorCalls", &stats.cp_propagator_calls),
					("satSearchDirectives", &stats.sat_search_directives),
					("userSearchDirectives", &stats.user_search_directives),
					("eagerLiterals", &stats.eager_literals),
					("lazyLiterals", &stats.lazy_literals),
				],
			);
		}
		match res {
			Status::Satisfied => {}
			Status::Unsatisfiable => outputln!(self.stdout, "{}", FZN_UNSATISFIABLE),
			Status::Unknown => outputln!(self.stdout, "{}", FZN_UNKNOWN),
			Status::Complete => outputln!(self.stdout, "{}", FZN_COMPLETE),
		}
		Ok(())
	}
}

impl SolutionWrap<'_> {
	/// Method used to print a literal that is part of a solution.
	fn print_lit(&self, lit: &Literal<FznIdent>) -> String {
		match lit {
			Literal::Int(i) => format!("{i}"),
			Literal::Float(f) => format!("{f}"),
			Literal::Variable(var) => {
				format!("{}", self.var_map[&var.cloned_key()].val(self.sol))
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
		for named_ref in &self.fzn.output {
			match named_ref {
				NamedRef::Variable(var) => writeln!(
					f,
					"{} = {};",
					var.name,
					self.var_map[&var.cloned_key()].val(self.sol)
				)?,
				NamedRef::Array(arr) => writeln!(
					f,
					"{} = [{}];",
					arr.name,
					arr.contents
						.iter()
						.map(|lit| self.print_lit(lit))
						.collect::<Vec<_>>()
						.join(",")
				)?,
			}
		}
		writeln!(f, "{FZN_SEPARATOR}")
	}
}
