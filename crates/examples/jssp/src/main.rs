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

use std::{
	fmt,
	fs::File,
	io::{self, BufRead, BufReader},
	process::exit,
	sync::{
		Arc,
		atomic::{AtomicBool, Ordering},
	},
	time::{Duration, Instant},
};

use huub::{
	Branching, IntDecision, IntLinExpr, Model, TermSignal, ValueSelection, VariableSelection,
	disjunctive_strict,
	reformulate::{InitConfig, ReformulationMap},
	solver::{Goal, IntView, Solver, Valuation, Value, View},
};
use pico_args::Arguments;
use rangelist::RangeList;

/// Parses a time duration for the time limit flag.
/// If no unit is provided, assumes milliseconds.
fn parse_time_limit(s: &str) -> Result<Duration, humantime::DurationError> {
	if let Ok(ms) = s.parse() {
		Ok(Duration::from_millis(ms))
	} else {
		humantime::parse_duration(s)
	}
}

#[derive(Debug)]
pub struct Operation {
	pub machine: usize,
	pub processing_time: usize,
}

#[derive(Debug)]
pub struct Job {
	pub operations: Vec<Operation>,
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

#[derive(Debug, Default)]
struct Instance {
	options: Options,
	n: usize,
	m: usize,
	max_time: usize,
	jobs: Vec<Job>,
	operations_on_machine: Vec<Vec<(usize, usize)>>, // (job_index, operation_index)
}

#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub enum ObjectiveType {
	#[default]
	Makespan,
	TotalCompletionTime,
}

impl Instance {
	/// Parses a job-shop scheduling (JSP) instance from a text file.
	///
	/// Expected file format:
	/// - First line: two integers "N M"
	///     - N = number of jobs
	///     - M = number of machines
	/// - Next N lines: one line per job. Each job line contains an even number
	///   of whitespace-separated integers interpreted as consecutive (machine,
	///   processing_time) pairs. A job line with k pairs represents k
	///   operations for that job: machine_0 time_0 machine_1 time_1 ...
	///   machine_{k-1} time_{k-1}
	/// - Machine indices are zero-based and expected to be in the range 0..M-1.
	/// - Processing times are non-negative integers.
	/// - If a job line contains an odd number of integers, the trailing number
	///   is ignored.
	///
	/// Example (3 jobs, 4 machines):
	/// 3 4
	/// 0 3 1 2 2 4
	/// 1 5 3 2
	/// 2 2 0 4 1 1
	///
	/// Parsing errors (missing header, invalid integers, wrong number of job
	/// lines, ...) are propagated as io::Error.
	fn parse_jsp_file(&mut self, path: &str) -> Result<(), io::Error> {
		let file = File::open(path)?;
		let mut lines = BufReader::new(file).lines();

		// Parse header: number of jobs and machines
		let header = lines
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "Missing header"))??;
		let mut header_parts = header.split_whitespace();
		self.n = header_parts
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "Missing N"))?
			.parse()
			.map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "Invalid N"))?;
		self.m = header_parts
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "Missing M"))?
			.parse()
			.map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "Invalid M"))?;

		// Parse jobs and their operations
		self.jobs = Vec::with_capacity(self.n);
		for line in lines.take(self.n) {
			let line = line?;
			let nums: Vec<usize> = line
				.split_whitespace()
				.map(|s| s.parse().unwrap())
				.collect();
			let mut operations = Vec::with_capacity(nums.len() / 2);
			for pair in nums.chunks(2) {
				if pair.len() == 2 {
					operations.push(Operation {
						machine: pair[0],
						processing_time: pair[1],
					});
				}
			}
			self.jobs.push(Job { operations });
		}

		Ok(())
	}

	/// Parses command-line arguments and builds a job-shop scheduling instance.
	///
	/// # Command-line options
	/// - `-v`, `--verbose`: Print details for every solution found.
	/// - `-s`, `--statistics`: Print solver statistics after solving.
	/// - `--reason-eager`: Enable eager reason requests for propagated
	///   literals.
	/// - `-t`, `--time-limit <DURATION>`: Set a time limit (e.g., `60`, `1m`,
	///   `2h`). Accepts milliseconds (default), seconds (`s`), minutes (`m`),
	///   or hours (`h`).
	/// - `--int-eager-limit <INT>`: Set the integer eager limit (default: 256).
	/// - `--restart`: Enable solver restarts.
	/// - `--vsids-after-conflict <INT>`: Enable VSIDS after a given number of
	///   conflicts.
	/// - `--vsids-after-restart`: Enable VSIDS after each restart.
	/// - `--toggle-vsids`: Toggle VSIDS during solving.
	/// - `--vsids-only`: Use only VSIDS for variable selection.
	/// - `--objective-type <TYPE>`: Objective type: `makespan` (minimize max
	///   completion time) or `total_completion_time` (minimize sum of
	///   completion times).
	/// - `<data_file>`: Path to the JSP instance file (required).
	///
	/// # Errors
	/// Returns an error if required arguments are missing, unexpected arguments
	/// are present, or the JSP file cannot be parsed.
	fn from_args() -> Result<Self, String> {
		let mut instance = Instance::default();
		let mut pargs = Arguments::from_env();

		let parse_objective_type = |s: &str| match s {
			"makespan" => Ok(ObjectiveType::Makespan),
			"total_completion_time" => Ok(ObjectiveType::TotalCompletionTime),
			_ => Err(format!("Invalid objective type: {s}")),
		};

		instance.options = Options {
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
		};

		let data_file: String = pargs.free_from_str().expect("Missing data file argument");

		let remaining_args = pargs.finish();
		if !remaining_args.is_empty() {
			return Err(format!("Unexpected arguments: {remaining_args:?}"));
		}

		instance
			.parse_jsp_file(data_file.as_str())
			.expect("Failed to parse JSP file");

		// Compute the maximum possible makespan
		let mut max_time = 0;
		for job in &instance.jobs {
			for op in &job.operations {
				max_time += op.processing_time;
			}
		}
		instance.max_time = max_time;

		// Build a list of operations for each machine
		instance.operations_on_machine = vec![Vec::new(); instance.m];
		for (job_idx, job) in instance.jobs.iter().enumerate() {
			for (op_idx, op) in job.operations.iter().enumerate() {
				instance.operations_on_machine[op.machine].push((job_idx, op_idx));
			}
		}

		Ok(instance)
	}
}

/// Stores the solution for a JSP instance.
#[derive(Debug)]
pub struct Solution {
	/// For each machine, a list of (job_index, operation_index,
	/// start_time_view)
	pub machine_schedule: Vec<Vec<(usize, usize, IntView)>>,
	/// Start times for each operation on each machine
	pub start_time: Option<Vec<Vec<(usize, usize, i64)>>>,
}

impl Solution {
	pub(crate) fn init(
		instance: &Instance,
		start_time: &[Vec<IntDecision>],
		map: &ReformulationMap,
		slv: &mut Solver,
	) -> Self {
		let mut machine_schedule = vec![Vec::new(); instance.m];
		for (machine_id, schedule) in machine_schedule.iter_mut().enumerate() {
			for &(job_idx, op_idx) in &instance.operations_on_machine[machine_id] {
				let var = start_time[job_idx][op_idx];
				let start = map.get_int(slv, var);
				schedule.push((job_idx, op_idx, start));
			}
		}
		Solution {
			machine_schedule,
			start_time: None,
		}
	}

	/// Constructs a Solution from the start times and instance.
	pub(crate) fn save_assignment<T: Valuation>(&mut self, value: T) {
		let mut start_time = Vec::with_capacity(self.machine_schedule.len());
		for ops in self.machine_schedule.iter() {
			let mut machine_profile = Vec::new();
			for (job_idx, op_idx, start_view) in ops {
				if let Value::Int(start_val) = value(View::Int(*start_view)) {
					machine_profile.push((*job_idx, *op_idx, start_val));
				}
			}
			machine_profile.sort_by_key(|&(_, _, st)| st);
			start_time.push(machine_profile);
		}
		self.start_time = Some(start_time);
	}
}

impl fmt::Display for Solution {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(start_times) = &self.start_time {
			for (machine_id, ops) in start_times.iter().enumerate() {
				write!(f, "Machine {machine_id}:")?;
				for (job_idx, op_idx, start_time) in ops {
					write!(f, " ({job_idx},{op_idx},{start_time})")?;
				}
				writeln!(f)?;
			}
		}
		Ok(())
	}
}

fn main() {
	let instance = Instance::from_args().expect("Failed to parse arguments");

	println!(
		"Parsed JSP instance: {} jobs, {} machines, {} operations, max time {}",
		instance.n,
		instance.m,
		instance
			.operations_on_machine
			.iter()
			.map(|ops| ops.len())
			.sum::<usize>(),
		instance.max_time
	);

	let mut model = Model::default();
	let mut start_time = Vec::with_capacity(instance.n);
	for job in &instance.jobs {
		let op_start_times = model.new_int_vars(
			job.operations.len(),
			RangeList::from(0..=(instance.max_time as i64)),
		);
		start_time.push(op_start_times);
	}

	// Add precedence constraints: operations in each job must be sequential
	for (i, job_start_time) in start_time.iter().enumerate() {
		let job = &instance.jobs[i];
		for j in 0..(job.operations.len() - 1) {
			let op1_end = job_start_time[j] + job.operations[j].processing_time as i64;
			model += (job_start_time[j + 1] - op1_end).geq(0);
		}
	}

	// Add disjunctive constraints: operations on the same machine cannot overlap
	for machine_id in 0..instance.m {
		let mut machine_ops = Vec::new();
		for (job_idx, job) in instance.jobs.iter().enumerate() {
			for (op_idx, op) in job.operations.iter().enumerate() {
				if op.machine == machine_id {
					machine_ops.push((job_idx, op_idx, op.processing_time as i64));
				}
			}
		}
		let op_start_times = machine_ops
			.iter()
			.map(|(job_idx, op_idx, _)| start_time[*job_idx][*op_idx])
			.collect::<Vec<_>>();
		let op_durations = machine_ops
			.iter()
			.map(|(_, _, duration)| *duration)
			.collect::<Vec<_>>();
		model += disjunctive_strict(op_start_times, op_durations);
	}

	// Add objective variable: minimize the total completion time
	let objective_variable = match instance.options.objective_type {
		ObjectiveType::Makespan => {
			// Makespan objective
			let makespan = model.new_int_var(RangeList::from(0..=(instance.max_time as i64)));
			for (job_idx, job) in instance.jobs.iter().enumerate() {
				let last_op_idx = job.operations.len() - 1;
				let end_time = start_time[job_idx][last_op_idx]
					+ job.operations[last_op_idx].processing_time as i64;
				model += (makespan - end_time).geq(0);
			}
			makespan
		}
		ObjectiveType::TotalCompletionTime => {
			// Total completion time objective
			let total_completion_time = model.new_int_var(RangeList::from(
				0..=(instance.max_time as i64 * instance.n as i64),
			));
			let mut completion_times = Vec::new();
			for (job_idx, job) in instance.jobs.iter().enumerate() {
				let last_op_idx = job.operations.len() - 1;
				let end_time = start_time[job_idx][last_op_idx]
					+ job.operations[last_op_idx].processing_time as i64;
				completion_times.push(end_time);
			}
			model +=
				(completion_times.into_iter().sum::<IntLinExpr>() - total_completion_time).leq(0);
			total_completion_time
		}
	};

	// Add branching strategy for start times
	model += Branching::Int(
		start_time
			.iter()
			.flat_map(|ops| ops.iter().cloned())
			.collect(),
		VariableSelection::Smallest,
		ValueSelection::IndomainMin,
	);

	println!("Solver configurations:");
	println!("{0}", instance.options);

	// Configure solver initialization options
	let init_config = InitConfig::default();
	init_config
		.with_restart(instance.options.restart)
		.with_int_eager_limit(instance.options.int_eager_limit)
		.with_reason_eager(instance.options.reason_eager);
	let (mut slv, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();

	// Set solver options from command-line flags
	slv.set_toggle_vsids(instance.options.toggle_vsids);
	slv.set_vsids_after_conflict(instance.options.vsids_after_conflict);
	slv.set_vsids_after_restart(instance.options.vsids_after_restart);
	slv.set_vsids_only(instance.options.vsids_only);

	// Set up termination callback for time limit and Ctrl-C
	let start = Instant::now();
	let interrupted = Arc::new(AtomicBool::new(false));
	if let Some(deadline) = instance.options.time_limit.map(|t| start + t) {
		let interrupted = Arc::clone(&interrupted);
		slv.set_terminate_callback(Some(move || {
			if interrupted.load(Ordering::SeqCst) || Instant::now() >= deadline {
				TermSignal::Terminate
			} else {
				TermSignal::Continue
			}
		}));
	}
	if let Err(err) = ctrlc::set_handler(move || {
		interrupted.store(true, Ordering::SeqCst);
	}) {
		println!("unable to set Ctrl-C handler: {err}");
		exit(-1);
	}

	// Solve the problem using branch-and-bound for the makespan objective
	let obj = map.get_int(&mut slv, objective_variable);
	let goal = Goal::Minimize;
	let mut last_obj = match goal {
		Goal::Minimize => i64::MAX,
		Goal::Maximize => i64::MIN,
	};
	let mut solution = Solution::init(&instance, &start_time, &map, &mut slv);
	let (status, stats, obj_val) = slv.branch_and_bound(obj, goal, |value| {
		solution.save_assignment(value);
		if let Value::Int(obj_val) = value(View::Int(obj)) {
			last_obj = obj_val;
		}
		if instance.options.verbose {
			println!("Found new solution with objective: {last_obj}");
			println!("{solution}");
			println!("-------------------------");
		}
	});

	if !instance.options.verbose {
		println!(
			"Best solution found with objective: {}",
			obj_val.unwrap_or(last_obj)
		);
		println!("{solution}");
	}

	// Print statistics if requested
	if instance.options.statistics {
		println!("Solving statistics:");
		println!("  Status: {status:?}");
		println!("  Objective value: {}", obj_val.unwrap_or(last_obj));
		println!("  User decisions: {}", stats.user_decisions());
		println!("  Oracle decisions: {}", stats.oracle_decisions());
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
