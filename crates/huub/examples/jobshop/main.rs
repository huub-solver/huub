//! # Job Shop Scheduling Example using Huub
//!
//! This project demonstrates how to model and solve the Job Shop Scheduling
//! Problem (JSSP) using the Huub constraint programming library. The JSSP is a
//! classic optimization problem where multiple jobs, each consisting of a
//! sequence of operations, must be scheduled on a set of machines. Each
//! operation requires a specific machine for a given processing time,
//! and no two operations can use the same machine simultaneously.
//!
//! The solver supports two objective functions:
//! - **Makespan**: Minimize the maximum completion time across all jobs.
//! - **Total Completion Time**: Minimize the sum of completion times for all
//!   jobs.
//!
//! This example parses a JSSP instance from a text file, builds the scheduling
//! model with precedence and disjunctive constraints, and solves it using
//! Huub's Lazy Clause Generation engine. Various solver options and statistics
//! are available via command-line flags.

mod brancher;
mod model;

use std::{
	fmt::{self, Display},
	path::PathBuf,
	sync::{
		Arc,
		atomic::{AtomicBool, Ordering},
	},
	time::{Duration, Instant},
};

use clap::{ArgAction, Parser, ValueEnum, builder::BoolishValueParser};
use huub::{
	Goal, TerminationSignal,
	lower::InitConfig,
	solver::{IntValuation, SearchStrategy, Solver, SwitchTrigger},
};

use crate::{
	brancher::{BranchingStrategy, StaticBranching},
	model::{Instance, JobShopModel, ObjectiveType, Solution},
};

/// Parses a time duration for the time limit flag.
/// If no unit is provided, assumes milliseconds.
fn parse_time_limit(s: &str) -> Result<Duration, humantime::DurationError> {
	if let Ok(ms) = s.parse() {
		Ok(Duration::from_millis(ms))
	} else {
		humantime::parse_duration(s)
	}
}

#[derive(Debug, Parser)]
#[command(
	name = "jobshop",
	about = "Solve a job-shop scheduling instance with Huub.",
	disable_help_subcommand = true
)]
/// The parsed command-line options for the jobshop solver.
struct Cli {
	/// Path to the JSP instance file.
	#[arg(value_name = "FILE")]
	path: PathBuf,
	/// Whether to print statistics after solving.
	#[arg(short, long)]
	statistics: bool,
	/// Whether to instruct CaDiCaL to use eager reasons for propagation.
	#[arg(
		long,
		action = ArgAction::Set,
		value_parser = BoolishValueParser::new(),
		value_name = "bool",
		default_value_t = InitConfig::default().reason_eager()
	)]
	reason_eager: bool,
	/// The time limit before stopping the solver.
	#[arg(short = 't', long, value_parser = parse_time_limit, value_name = "duration")]
	time_limit: Option<Duration>,
	/// The maximal domain size before switching from eager to lazy literals for
	/// the integer decision variables.
	#[arg(
		long,
		value_name = "usize",
		default_value_t = InitConfig::default().int_eager_limit()
	)]
	int_eager_limit: usize,
	/// Whether to enable restarting.
	#[arg(
		long,
		action = ArgAction::Set,
		value_parser = BoolishValueParser::new(),
		value_name = "bool",
		default_value_t = InitConfig::default().restart()
	)]
	restart: bool,
	/// Set the overarching search strategy used by the solver.
	#[arg(long, value_enum, value_name = "strategy", default_value_t = SearchMode::Branchers)]
	search_strategy: SearchMode,
	/// Set the search trigger used by the solver, required if
	/// `--search-strategy` is “transition” or “interleaved”.
	#[arg(long, value_enum, value_name = "trigger", default_value_t = SearchTrigger::Conflicts, hide_default_value = true, required_if_eq_any = [("search_strategy", "transition"), ("search_strategy", "interleaved")])]
	search_trigger: SearchTrigger,
	/// Set the required trigger interval for search strategy “transition” or
	/// “interleaved”.
	#[arg(long, default_value_t = 1, value_name = "u64", hide_default_value = true, required_if_eq_any = [("search_strategy", "transition"), ("search_strategy", "interleaved")])]
	search_interval: u64,
	/// Whether to print verbose output.
	#[arg(short, long)]
	verbose: bool,
	/// The chosen objective.
	#[arg(long, value_enum, value_name = "objective", default_value_t = ObjectiveType::Makespan)]
	objective_type: ObjectiveType,
	/// The branching strategy to use by the solver.
	#[arg(long, value_enum, value_name = "strategy", default_value_t = BranchingStrategy::Static(StaticBranching::JobInputOrder))]
	branching_strategy: BranchingStrategy,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
/// Search strategy options exposed through the job-shop CLI.
enum SearchMode {
	/// Use the user-provided branchers for all search decisions until they are
	/// exhausted, and only then defer to the SAT solver.
	#[default]
	Branchers,
	/// Always defer to the SAT solver to make search decisions, ignoring any
	/// user-provided branchers.
	Sat,
	/// Transition from “branchers” to “sat” when the given trigger condition is
	/// met.
	Transition,
	/// Interleave “branchers” and “sat” search strategies, switching between
	/// them each time the trigger condition is met.
	Interleaved,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
/// Trigger counters that can drive search-strategy transitions.
enum SearchTrigger {
	/// Switch after the given number of conflicts have been encountered.
	#[default]
	Conflicts,
	/// Switch after the given number of restarts have been encountered.
	Restarts,
}

impl Cli {
	/// Formats an option value as a string, using "N/A" as the default if the
	/// value is `None`.
	fn display_option<'a, T: Display>(&self, opt: &'a Option<T>) -> &'a dyn Display {
		const N_A: &str = "N/A";
		if let Some(v) = opt {
			let v: &dyn Display = v;
			v
		} else {
			&N_A
		}
	}

	/// Build the solver search strategy from the CLI flags.
	fn search_strategy(&self) -> SearchStrategy {
		let trigger = match self.search_trigger {
			SearchTrigger::Conflicts => SwitchTrigger::Conflicts,
			SearchTrigger::Restarts => SwitchTrigger::Restarts,
		};
		let trigger = trigger(self.search_interval);
		match self.search_strategy {
			SearchMode::Branchers => SearchStrategy::Branchers,
			SearchMode::Sat => SearchStrategy::Sat,
			SearchMode::Transition => SearchStrategy::Transition(trigger),
			SearchMode::Interleaved => SearchStrategy::Interleaved(trigger),
		}
	}
}

impl Display for Cli {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		writeln!(f, "  Objective type: {:?}", self.objective_type)?;
		writeln!(f, "  Branching strategy: {:?}", self.branching_strategy)?;
		writeln!(f, "  Reason eager: {}", self.reason_eager)?;
		writeln!(f, "  Integer eager limit: {}", self.int_eager_limit)?;
		writeln!(
			f,
			"  Time limit: {}",
			self.display_option(&self.time_limit.map(|tl| tl.as_secs_f32()))
		)?;
		writeln!(f, "  Restart: {}", self.restart)?;
		writeln!(f, "  Search strategy: {:?}", self.search_strategy)?;
		if matches!(
			self.search_strategy,
			SearchMode::Transition | SearchMode::Interleaved
		) {
			writeln!(f, "  Search trigger: {:?}", self.search_trigger)?;
			writeln!(f, "  Search interval: {}", self.search_interval)?;
		}
		Ok(())
	}
}

fn main() {
	let options = match Cli::try_parse_from(std::env::args_os()) {
		Ok(options) => options,
		Err(err) => {
			err.print().expect("unable to write clap error output");
			std::process::exit(2);
		}
	};
	let instance = match Instance::from_jsp_file(options.path.to_string_lossy().as_ref()) {
		Ok(instance) => instance,
		Err(err) => {
			eprintln!(
				"failed to parse JSP file “{}”: {err}",
				options.path.display()
			);
			std::process::exit(2);
		}
	};
	let JobShopModel {
		mut model,
		start_time,
		objective: objective_variable,
	} = JobShopModel::new(&instance, options.objective_type);

	println!(
		"Parsed JSP instance: {} jobs, {} machines, {} operations, max time {}",
		instance.n,
		instance.m,
		instance.operation_count(),
		instance.max_time
	);

	println!("Solver configurations:");
	println!("{0}", options);

	// Configure solver initialization options.
	let init_config = InitConfig::default()
		.with_restart(options.restart)
		.with_int_eager_limit(options.int_eager_limit)
		.with_reason_eager(options.reason_eager);
	let (mut slv, map): (Solver, _) = model.to_solver(&init_config).unwrap();

	options
		.branching_strategy
		.to_solver(&mut slv, &map, &start_time, &instance);
	slv.set_search_strategy(options.search_strategy());

	// Solve the problem using branch-and-bound for the selected objective.
	let obj = map.get(&mut slv, objective_variable);
	let mut last_obj = None;
	let mut solution = Solution::init(&instance, &start_time, &map, &mut slv);

	// Set up the termination callback for the time limit and Ctrl-C.
	let start = Instant::now();
	let interrupted = Arc::new(AtomicBool::new(false));
	let interrupted_clone = Arc::clone(&interrupted);
	let time_limit = options.time_limit;
	slv.set_terminate_callback(Some(move || {
		if interrupted.load(Ordering::SeqCst)
			|| time_limit.is_some_and(|deadline| Instant::now().duration_since(start) >= deadline)
		{
			TerminationSignal::Terminate
		} else {
			TerminationSignal::Continue
		}
	}));
	if let Err(err) = ctrlc::set_handler({
		let interrupted = interrupted_clone;
		move || {
			interrupted.store(true, Ordering::SeqCst);
		}
	}) {
		println!("unable to set Ctrl-C handler: {err}");
		std::process::exit(-1);
	}

	let (status, stats, _) = slv.branch_and_bound(Goal::Minimize(obj), |sol| {
		solution.save_assignment(sol);
		last_obj = Some(IntValuation::val(&obj, sol));
		if options.verbose {
			println!("Found new solution with objective: {}", last_obj.unwrap());
			println!("{solution}");
			println!("-------------------------");
		}
	});

	if !options.verbose {
		println!(
			"Best solution found with objective: {}",
			last_obj.unwrap_or(i64::MAX)
		);
		println!("{solution}");
	}

	// Print statistics if requested.
	if options.statistics {
		println!("Solving statistics:");
		println!("  Status: {status:?}");
		if let Some(obj) = last_obj {
			println!("  Objective value: {obj}");
		}
		println!("  User decisions: {}", stats.user_decisions());
		println!("  Oracle decisions: {}", stats.sat_decisions());
		println!("  Propagations: {}", stats.cp_propagations());
		println!("  Conflicts: {}", stats.conflicts());
		println!("  Restarts: {}", stats.restarts());
		println!("  Peak depth: {}", stats.peak_depth());
		println!(
			"  Time: {:.3} seconds",
			(Instant::now() - start).as_secs_f32()
		);
	}
}
