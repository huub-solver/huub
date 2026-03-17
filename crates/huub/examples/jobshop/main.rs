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
	fmt, i64,
	process::exit,
	sync::{
		Arc,
		atomic::{AtomicBool, Ordering},
	},
	time::{Duration, Instant},
};

use huub::{
	Goal, TerminationSignal,
	lower::InitConfig,
	solver::{IntValuation, Solver},
};
use pico_args::Arguments;

use crate::{
	brancher::{BranchingStrategy, DynamicBranching, StaticBranching},
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

#[derive(Debug, Default)]
struct Options {
	statistics: bool,
	reason_eager: bool,
	time_limit: Option<Duration>,
	int_eager_limit: usize,
	restart: bool,
	vsids_after_conflict: Option<u32>,
	vsids_after_restart: bool,
	toggle_vsids: bool,
	vsids_only: bool,
	verbose: bool,
	objective_type: ObjectiveType,
	strategy: BranchingStrategy,
}

impl Options {
	fn format_option<T: ToString>(&self, opt: &Option<T>) -> String {
		opt.as_ref()
			.map(ToString::to_string)
			.unwrap_or_else(|| "N/A".to_string())
	}
}

impl fmt::Display for Options {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		writeln!(f, "  Objective type: {:?}", self.objective_type)?;
		writeln!(f, "  Reason eager: {}", self.reason_eager)?;
		writeln!(f, "  Integer eager limit: {}", self.int_eager_limit)?;
		writeln!(
			f,
			"  Time limit: {}",
			self.format_option(&self.time_limit.map(|tl| tl.as_secs_f32()))
		)?;
		writeln!(f, "  Restart: {}", self.restart)?;
		writeln!(
			f,
			"  VSIDS after conflict: {}",
			self.format_option(&self.vsids_after_conflict)
		)?;
		writeln!(f, "  VSIDS after restart: {}", self.vsids_after_restart)?;
		writeln!(f, "  Toggle VSIDS: {}", self.toggle_vsids)?;
		writeln!(f, "  VSIDS only: {}", self.vsids_only)?;
		Ok(())
	}
}

/// Parses command-line arguments and builds a job-shop scheduling instance.
///
/// # command-line options
/// - `-v`, `--verbose`: Print details for every solution found.
/// - `-s`, `--statistics`: Print solver statistics after solving.
/// - `--reason-eager`: Enable eager reason requests for propagated literals.
/// - `-t`, `--time-limit <DURATION>`: Set a time limit (e.g., `60`, `1m`,
///   `2h`). Accepts milliseconds (default), seconds (`s`), minutes (`m`), or
///   hours (`h`).
/// - `--int-eager-limit <INT>`: Set the integer eager limit (default: 256).
/// - `--restart`: Enable solver restarts.
/// - `--vsids-after-conflict <INT>`: Enable VSIDS after a given number of
///   conflicts.
/// - `--vsids-after-restart`: Enable VSIDS after each restart.
/// - `--toggle-vsids`: Toggle VSIDS during solving.
/// - `--vsids-only`: Use only VSIDS for variable selection.
/// - `--objective-type <TYPE>`: Objective type: `makespan` (minimize max
///   completion time) or `total_completion_time` (minimize sum of completion
///   times).
/// - `--branching-strategy <STRATEGY>`: Branching strategy: `job-fifo`,
///   `job-lwf`, `job-mwf`, `job-sjf`, `job-ljf`, `op-fifo`, `op-lpt`, `op-spt`,
///   `op-lwr`, `op-mwr`, `op-lor`, or `op-mor`.
/// - `<data_file>`: Path to the JSP instance file (required).
///
/// # errors
/// Returns an error if required arguments are missing, unexpected arguments
/// are present, or the JSP file cannot be parsed.
fn parse_args() -> Result<(Instance, Options), String> {
	let mut pargs = Arguments::from_env();

	let parse_objective_type = |s: &str| match s {
		"makespan" => Ok(ObjectiveType::Makespan),
		"total_completion_time" => Ok(ObjectiveType::TotalCompletionTime),
		_ => Err(format!("Invalid objective type: {s}")),
	};

	let parse_branching_strategy = |s: &str| match s {
		"job-fifo" => Ok(BranchingStrategy::Static(StaticBranching::JobFifo)),
		"job-lwf" => Ok(BranchingStrategy::Static(StaticBranching::JobLwf)),
		"job-mwf" => Ok(BranchingStrategy::Static(StaticBranching::JobMwf)),
		"job-sjf" => Ok(BranchingStrategy::Static(StaticBranching::JobSjf)),
		"job-ljf" => Ok(BranchingStrategy::Static(StaticBranching::JobLjf)),
		"op-fifo" => Ok(BranchingStrategy::Static(StaticBranching::OpFifo)),
		"op-lpt" => Ok(BranchingStrategy::Static(StaticBranching::OpLpt)),
		"op-spt" => Ok(BranchingStrategy::Static(StaticBranching::OpSpt)),
		"op-lwr" => Ok(BranchingStrategy::Dynamic(DynamicBranching::OpLwr)),
		"op-mwr" => Ok(BranchingStrategy::Dynamic(DynamicBranching::OpMwr)),
		"op-lor" => Ok(BranchingStrategy::Dynamic(DynamicBranching::OpLor)),
		"op-mor" => Ok(BranchingStrategy::Dynamic(DynamicBranching::OpMor)),
		_ => Err(format!("Invalid branching strategy: {s}")),
	};

	let options = Options {
		verbose: pargs.contains(["-v", "--verbose"]),
		statistics: pargs.contains(["-s", "--statistics"]),
		reason_eager: pargs.contains("--reason-eager"),
		time_limit: pargs
			.opt_value_from_fn(["-t", "--time-limit"], parse_time_limit)
			.map_err(|e| e.to_string())?,
		int_eager_limit: pargs.value_from_str("--int-eager-limit").unwrap_or(256),
		restart: pargs.contains("--restart"),
		vsids_after_conflict: pargs
			.opt_value_from_str("--vsids-after-conflict")
			.unwrap_or(None),
		vsids_after_restart: pargs.contains("--vsids-after-restart"),
		toggle_vsids: pargs.contains("--toggle-vsids"),
		vsids_only: pargs.contains("--vsids-only"),
		objective_type: pargs
			.value_from_fn("--objective-type", parse_objective_type)
			.unwrap_or_default(),
		strategy: pargs
			.value_from_fn("--branching-strategy", parse_branching_strategy)
			.unwrap_or(BranchingStrategy::Static(StaticBranching::JobFifo)),
	};

	let data_file: String = pargs.free_from_str().expect("Missing data file argument");

	let remaining_args = pargs.finish();
	if !remaining_args.is_empty() {
		return Err(format!("Unexpected arguments: {remaining_args:?}"));
	}

	let instance = Instance::from_jsp_file(data_file.as_str()).expect("Failed to parse JSP file");

	Ok((instance, options))
}

fn main() {
	let (instance, options) = parse_args().expect("Failed to parse arguments");
	let JobShopModel {
		mut model,
		start_time,
		objective_variable,
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
		.strategy
		.install(&mut slv, &map, &start_time, &instance);

	// Set solver options from command-line flags.
	slv.set_toggle_vsids(options.toggle_vsids);
	slv.set_vsids_after_conflict(options.vsids_after_conflict);
	slv.set_vsids_after_restart(options.vsids_after_restart);
	slv.set_vsids_only(options.vsids_only);

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
			|| time_limit.map_or(false, |deadline| {
				Instant::now().duration_since(start) >= deadline
			}) {
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
		exit(-1);
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
		println!("  Objective value: {}", last_obj.unwrap_or(i64::MAX));
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
