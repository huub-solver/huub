use huub::reformulate::{InitConfig, ReformulationMap};
use huub::solver::{Goal, IntView, Solver, Valuation, Value, View};
use huub::{
    Branching, IntDecision, Model, TermSignal, ValueSelection, VariableSelection,
    disjunctive_strict,
};
use pico_args::Arguments;
use rangelist::RangeList;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

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
    int_eager_limit: Option<usize>,
    restart: bool,
    vsids_after_conflict: Option<u32>,
    vsids_after_restart: bool,
    toggle_vsids: bool,
    vsids_only: bool,
    verbose: bool,
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

impl Instance {
    /// Parses a JSP instance from a file.
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

    /// Parses command-line arguments and builds an instance.
    fn from_args() -> Result<Self, String> {
        let mut instance = Instance::default();
        let mut pargs = Arguments::from_env();

        instance.options = Options {
            verbose: pargs.contains(["-v", "--verbose"]),
            statistics: pargs.contains(["-s", "--statistics"]),
            reason_eager: pargs.contains("--reason-eager"),
            time_limit: pargs
                .opt_value_from_fn(["-t", "--time-limit"], parse_time_limit)
                .map_err(|e| e.to_string())?,
            int_eager_limit: pargs
                .opt_value_from_str("--int-eager-limit")
                .unwrap_or(Some(256)),
            restart: pargs.contains("--restart"),
            vsids_after_conflict: pargs
                .opt_value_from_str("--vsids-after-conflict")
                .unwrap_or(None),
            vsids_after_restart: pargs.contains("--vsids-after-restart"),
            toggle_vsids: pargs.contains("--toggle-vsids"),
            vsids_only: pargs.contains("--vsids-only"),
        };

        let data_file: String = pargs.free_from_str().expect("Missing data file argument");

        let remaining_args = pargs.finish();
        if !remaining_args.is_empty() {
            return Err(format!("Unexpected arguments: {:?}", remaining_args));
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
    /// For each machine, a list of (job_index, operation_index, start_time_view)
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
        for machine_id in 0..instance.m {
            for &(job_idx, op_idx) in &instance.operations_on_machine[machine_id] {
                let var = start_time[job_idx][op_idx];
                let start = map.get_int(slv, var);
                machine_schedule[machine_id].push((job_idx, op_idx, start));
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
                write!(f, "Machine {}:", machine_id)?;
                for (job_idx, op_idx, start_time) in ops {
                    write!(f, " ({},{},{})", job_idx, op_idx, start_time)?;
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
    for i in 0..instance.n {
        let job = &instance.jobs[i];
        for j in 0..(job.operations.len() - 1) {
            let op1_end = start_time[i][j].clone() + job.operations[j].processing_time as i64;
            model += (start_time[i][j + 1].clone() - op1_end).geq(0);
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
            .map(|(job_idx, op_idx, _)| start_time[*job_idx][*op_idx].clone())
            .collect::<Vec<_>>();
        let op_durations = machine_ops
            .iter()
            .map(|(_, _, duration)| *duration)
            .collect::<Vec<_>>();
        model += disjunctive_strict(op_start_times, op_durations);
    }

    // Add objective: minimize makespan
    let makespan = model.new_int_var(RangeList::from(0..=(instance.max_time as i64)));
    for (job_idx, job) in instance.jobs.iter().enumerate() {
        let last_op_idx = job.operations.len() - 1;
        let end_time = start_time[job_idx][last_op_idx].clone()
            + job.operations[last_op_idx].processing_time as i64;
        model += (makespan - end_time).geq(0);
    }

    // Add branching strategy for start times
    model += Branching::Int(
        start_time
            .iter()
            .flat_map(|ops| ops.iter().cloned())
            .collect(),
        VariableSelection::Smallest,
        ValueSelection::IndomainMin,
    );

    // Configure solver initialization options
    let init_config = InitConfig::default();
    init_config
        .with_restart(instance.options.restart)
        .with_int_eager_limit(instance.options.int_eager_limit.unwrap_or(256))
        .with_reason_eager(instance.options.reason_eager);
    let (mut slv, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();

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
        println!("unable to set Ctrl-C handler: {}", err);
        exit(-1);
    }

    // Set solver options from command-line flags
    slv.set_toggle_vsids(instance.options.toggle_vsids);
    slv.set_vsids_after_conflict(instance.options.vsids_after_conflict);
    slv.set_vsids_after_restart(instance.options.vsids_after_restart);
    slv.set_vsids_only(instance.options.vsids_only);

    // Solve the problem using branch-and-bound for the makespan objective
    let obj = map.get_int(&mut slv, makespan);
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
            println!("Found new best makespan: {}", last_obj);
            println!("{}", solution);
            println!("-------------------------");
        }
    });

    // Print statistics if requested
    if instance.options.statistics {
        println!("Solving statistics:");
        println!("  Status: {:?}", status);
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
