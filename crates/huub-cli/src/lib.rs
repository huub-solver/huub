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
mod interned_str;
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

use flatzinc_serde::{FlatZinc, Literal};
use huub::{
	Goal, TerminationSignal,
	actions::IntDecisionActions,
	lower::LoweringError,
	model::deserialize::flatzinc::FlatZincError,
	solver::{
		AnyView, IntLitMeaning, SearchStrategy, Solution, Solver, Status, SwitchTrigger, Value,
	},
};
use mimalloc::MiMalloc;
use rustc_hash::FxHashMap;
use tracing::{subscriber::set_default, warn};

pub use crate::cli::Cli;
use crate::{
	cli::{CliSearchStrategy, CliSearchTrigger},
	interned_str::InternedStr,
	trace::LitName,
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
	fzn: &'a FlatZinc<InternedStr>,
	/// Mapping from solver views to solution values
	sol: Solution<'a>,
	/// Mapping from FlatZinc identifiers to solver views
	var_map: &'a FxHashMap<InternedStr, AnyView>,
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
		let int_reverse_map: Arc<Mutex<Vec<InternedStr>>> = Arc::default();
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
		let fzn: FlatZinc<InternedStr> = serde_json::from_reader(rdr).map_err(|_| {
			format!(
				"Unable to parse file “{}” as FlatZinc JSON",
				self.path.display()
			)
		})?;

		let (mut slv, meta) = match Solver::from_fzn(&fzn, &self.init_config()) {
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
		let (res, stats) = match meta.goal {
			Some(goal) => {
				if self.all_solutions {
					warn!(
						target: "solver",
						"ignore --all-solutions when optimizing; use --intermediate-solutions or --all-optimal instead"
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
					if let Err(err) = ctrlc::set_handler(move || {
						interrupted.store(true, Ordering::SeqCst);
					}) {
						warn!(target: "solver", error = %err, "unable to set ctrl-c handler");
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
					if slv.add_no_good(&output_vars, &no_good_vals).is_err() {
						(Status::Complete, stats)
					} else {
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
			Status::Unsatisfiable => outputln!(self.stdout, "{}", FZN_UNSATISFIABLE),
			Status::Unknown => outputln!(self.stdout, "{}", FZN_UNKNOWN),
			Status::Complete => outputln!(self.stdout, "{}", FZN_COMPLETE),
		}
		Ok(())
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
		writeln!(f, "{FZN_SEPARATOR}")
	}
}
