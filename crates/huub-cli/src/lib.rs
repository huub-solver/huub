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
	cell::RefCell,
	fmt::{self, Debug, Display},
	io,
	sync::{
		Arc,
		atomic::{AtomicBool, Ordering},
	},
	time::Instant,
};

use flatzinc_serde::{FlatZinc, Literal, Method, NamedRef, Variable, helpers::ArcKey};
use huub::{
	lower::LoweringError,
	model::deserialize::{
		Goal,
		flatzinc::{FlatZincError, FznIdent, HuubFlatZinc},
	},
	solver::{
		AnyView, AssumptionChecker, SearchStrategy, Solution, Solver, Status, SwitchTrigger,
		TerminationSignal, Valuation, View,
	},
};
use mimalloc::MiMalloc;
use rustc_hash::FxHashMap;
use tracing::{subscriber::set_default, warn};

pub use crate::cli::Cli;
use crate::{
	cli::{CliSearchStrategy, CliSearchTrigger},
	trace::ReverseMap,
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

		let rdr = io::BufReader::new(
			std::fs::File::open(&self.path)
				.map_err(|_| format!("Unable to open file “{}”", self.path.display()))?,
		);
		let fzn: Arc<FlatZinc<_>> = Arc::new(serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?);

		let map = ReverseMap::new();
		let subscriber = trace::create_subscriber(
			self.verbose,
			&trace_targets,
			trace_writer,
			ansi_color,
			&map,
			Arc::clone(&fzn),
		);
		let _guard = set_default(subscriber);

		let start = Instant::now();
		let deadline = self.time_limit.map(|t| start + t);

		let (mut slv, meta): (Solver, _) = match fzn
			.lower()
			.int_eager_limit(self.int_eager_limit)
			.preprocessing(self.cadical.preprocessing)
			.conditioning(self.cadical.conditioning)
			.inprocessing(self.cadical.inprocessing)
			.probing(self.cadical.probing)
			.reason_eager(self.cadical.reason_eager)
			.reduce_interval(self.cadical.reduce_interval)
			.reduce_type(self.cadical.reduce_type.into())
			.restart(self.free_search || self.restart)
			.subsumption(self.cadical.subsumption)
			.variable_elimination(self.cadical.variable_elimination)
			.vivification(self.cadical.vivification)
			.preprocessing_light(self.cadical.preprocessing_light)
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

		// Assumption interface: every `huub_assume` constraint in the FlatZinc
		// instance contributes its array elements to `meta.assumptions`. The
		// CLI forwards them to the solver via `.assuming(...)` and prints the
		// failing subset (the "core") as a `%%%mzn-core` line when the solver
		// reports UNSAT or proves optimality.
		let assumption_views: Vec<View<bool>> = meta.assumptions.iter().map(|(_, v)| *v).collect();
		let has_assumptions = !assumption_views.is_empty();
		// FlatZinc identifier of the objective decision, used to label the
		// boundary literal that appears in the core on `Status::Complete`.
		let obj_name: Option<&str> = match &fzn.solve.method {
			Method::Minimize(Literal::Variable(v)) | Method::Maximize(Literal::Variable(v)) => {
				Some(&v.name)
			}
			_ => None,
		};
		// Populated from inside the `on_failure` callback with the labels of
		// the user assumptions that the solver attributed to the failure.
		let unsat_core: RefCell<Option<Vec<String>>> = RefCell::default();
		let make_on_failure = || {
			|checker: &dyn AssumptionChecker| {
				*unsat_core.borrow_mut() = Some(
					meta.assumptions
						.iter()
						.filter_map(|(label, view)| {
							if checker.fail(*view) {
								Some(label.clone())
							} else {
								None
							}
						})
						.collect(),
				);
			}
		};

		let (status, obj_val) = match meta.goal {
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
						.assuming(assumption_views)
						.maybe_on_failure(has_assumptions.then(|| make_on_failure()))
						.maybe_all_solutions(self.all_optimal.then(|| output_vars.clone()));
					match goal {
						Goal::Minimize(obj) => solve.minimize(obj),
						Goal::Maximize(obj) => solve.maximize(obj),
						_ => panic!("unknown optimization goal"),
					}
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
						.assuming(assumption_views)
						.maybe_on_failure(has_assumptions.then(|| make_on_failure()))
						.maybe_all_solutions(self.all_optimal.then(|| output_vars.clone()));
					let ret = match goal {
						Goal::Minimize(obj) => solve.minimize(obj),
						Goal::Maximize(obj) => solve.maximize(obj),
						_ => panic!("unknown optimization goal"),
					};
					if !last_sol.is_empty() {
						output!(self.stdout, "{}", last_sol);
					}
					ret
				}
			}
			None => {
				let status = slv
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
					.assuming(assumption_views)
					.maybe_on_failure(has_assumptions.then(|| make_on_failure()))
					.maybe_all_solutions(self.all_solutions.then(|| output_vars.clone()))
					.satisfy();
				(status, None)
			}
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
		if let Some(mut core) = unsat_core.into_inner() {
			// If `Status::Complete` for an optimisation problem we annotate
			// the core with the objective literal.
			if status == Status::Complete {
				let (name, val) = (obj_name.unwrap_or("objective"), obj_val.unwrap());
				let bound_label = match &fzn.solve.method {
					Method::Minimize(_) => format!("{name} < {val}"),
					Method::Maximize(_) => format!("{name} >= {}", val + 1),
					Method::Satisfy => unreachable!(),
				};
				core.push(bound_label);
			}
			outputln!(self.stdout, "%%%mzn-core: [{}]", core.join(", "));
		}
		match status {
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
