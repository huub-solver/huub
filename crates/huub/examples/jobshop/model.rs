//! Domain types and model construction for the job shop example.

use std::{
	fmt,
	fs::File,
	io::{self, BufRead, BufReader},
};

use clap::ValueEnum;
use huub::{
	lower::LoweringMap,
	model::{self, Model, expressions::IntLinearExp},
	solver::{self, Solver, Valuation},
};

#[derive(Debug, Default)]
/// The representation of the data for a jobshop scheduling instance.
pub(crate) struct Instance {
	/// The number of jobs in the instance.
	pub(crate) n: usize,
	/// The number of machines in the instance.
	pub(crate) m: usize,
	/// The latest completion time of any operation in the instance.
	pub(crate) max_time: usize,
	/// The jobs in the instance, represented as a vector of operations.
	pub(crate) jobs: Vec<Job>,
	/// The `(job_idx, op_idx)` pairs grouped by machine.
	pub(crate) operations_on_machine: Vec<Vec<(usize, usize)>>,
}

/// A job is represented as a vector of operations.
pub(crate) type Job = Vec<Operation>;

/// A job shop constraint model for the given instance and objective type.
pub(crate) struct JobShopModel {
	/// The underlying Huub [`Model`] representation.
	pub(crate) model: Model,
	/// The start time of each operation on each machine.
	pub(crate) start_time: Vec<Vec<model::View<i64>>>,
	/// The decision variable representing the objective value.
	pub(crate) objective: model::View<i64>,
}

/// Choice of objective function to use to access the quality of a jobshop
/// assignment.
#[derive(Debug, Clone, Copy, Default, PartialEq, ValueEnum)]
pub(crate) enum ObjectiveType {
	/// The makespan objective function, which minimizes the completion time of
	/// the last operation on the last machine.
	#[default]
	Makespan,
	/// The total completion time objective function, which minimizes the sum of
	/// completion times of all operations.
	TotalCompletionTime,
}

#[derive(Copy, Debug, Clone, PartialEq, Eq)]
/// The representation of an operation to be scheduled on a machine.
pub(crate) struct Operation {
	/// The index of the job this operation belongs to.
	pub(crate) job_idx: usize,
	/// The index of the machine this operation is assigned to.
	pub(crate) machine: usize,
	/// The index of the operation within the job.
	pub(crate) op_idx: usize,
	/// The time required to process this operation.
	pub(crate) processing_time: usize,
}

/// Stores the solution for a job-shop instance.
#[derive(Debug)]
pub(crate) struct Solution {
	/// For each machine, a list of `(job_idx, op_idx, start_time_view)`.
	pub(crate) machine_schedule: Vec<Vec<(usize, usize, solver::View<i64>)>>,
	/// Start times for each operation on each machine.
	pub(crate) start_time: Option<Vec<Vec<(usize, usize, i64)>>>,
}

/// Create
fn job_completion_times(
	instance: &Instance,
	start_time: &[Vec<model::View<i64>>],
) -> Vec<model::View<i64>> {
	let mut completion_times = Vec::with_capacity(instance.jobs.len());
	for (job_idx, job) in instance.jobs.iter().enumerate() {
		let Some((last_op_idx, last_op)) = job.iter().enumerate().next_back() else {
			continue;
		};
		completion_times.push(start_time[job_idx][last_op_idx] + last_op.processing_time as i64);
	}
	completion_times
}

impl Instance {
	/// Parses a job-shop scheduling instance from a text file.
	pub(crate) fn from_jsp_file(path: &str) -> Result<Self, io::Error> {
		let mut instance = Instance::default();
		let file = File::open(path)?;
		let mut lines = BufReader::new(file).lines();

		let header = lines
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing header"))??;
		let mut header_parts = header.split_whitespace();
		instance.n = header_parts
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing N"))?
			.parse()
			.map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid N"))?;
		instance.m = header_parts
			.next()
			.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing M"))?
			.parse()
			.map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid M"))?;

		instance.jobs = Vec::with_capacity(instance.n);
		for job_idx in 0..instance.n {
			let line = lines.next().ok_or_else(|| {
				io::Error::new(
					io::ErrorKind::InvalidData,
					format!("missing job description for job {job_idx}"),
				)
			})??;
			let nums = line
				.split_whitespace()
				.map(|token| {
					token.parse::<usize>().map_err(|_| {
						io::Error::new(
							io::ErrorKind::InvalidData,
							format!("invalid integer in job {job_idx}: {token}"),
						)
					})
				})
				.collect::<Result<Vec<_>, _>>()?;

			let mut operations = Vec::with_capacity(nums.len() / 2);
			for pair in nums.chunks(2) {
				if pair.len() != 2 {
					continue;
				}
				let machine = pair[0];
				if machine >= instance.m {
					return Err(io::Error::new(
						io::ErrorKind::InvalidData,
						format!("machine index {machine} is out of range for job {job_idx}"),
					));
				}
				operations.push(Operation {
					job_idx,
					machine,
					op_idx: operations.len(),
					processing_time: pair[1],
				});
			}
			instance.jobs.push(operations);
		}

		instance.max_time = instance
			.jobs
			.iter()
			.flatten()
			.map(|op| op.processing_time)
			.sum();

		instance.operations_on_machine = vec![Vec::new(); instance.m];
		for (job_idx, job) in instance.jobs.iter().enumerate() {
			for (op_idx, op) in job.iter().enumerate() {
				instance.operations_on_machine[op.machine].push((job_idx, op_idx));
			}
		}

		Ok(instance)
	}

	/// Returns the number of operations in the instance.
	pub(crate) fn operation_count(&self) -> usize {
		self.jobs.iter().map(Vec::len).sum()
	}
}

impl JobShopModel {
	/// Create a new job shop model for the given instance and objective type.
	pub(crate) fn new(instance: &Instance, objective_type: ObjectiveType) -> Self {
		let mut model = Model::default();
		// ANCHOR: create_decision_variables
		let mut start_time = Vec::with_capacity(instance.n);
		for job in &instance.jobs {
			start_time.push(model.new_int_decisions(job.len(), 0..=(instance.max_time as i64)));
		}
		// ANCHOR_END: create_decision_variables

		// ANCHOR: precedence_constraints
		for (job, job_start_time) in instance.jobs.iter().zip(&start_time) {
			for (op_idx, op) in job.iter().enumerate().take(job.len().saturating_sub(1)) {
				let op_end = job_start_time[op_idx] + op.processing_time as i64;
				model.linear(job_start_time[op_idx + 1]).ge(op_end).post();
			}
		}
		// ANCHOR_END: precedence_constraints

		// ANCHOR: disjunctive_constraints
		for operations_on_machine in &instance.operations_on_machine {
			let mut op_start_times = Vec::with_capacity(operations_on_machine.len());
			let mut op_durations = Vec::with_capacity(operations_on_machine.len());
			for &(job_idx, op_idx) in operations_on_machine {
				let op = instance.jobs[job_idx][op_idx];
				op_start_times.push(start_time[job_idx][op_idx]);
				op_durations.push(op.processing_time as i64);
			}
			model
				.disjunctive()
				.start_times(op_start_times)
				.durations(op_durations)
				.post();
		}
		// ANCHOR_END: disjunctive_constraints

		let completion_times = job_completion_times(instance, &start_time);
		// ANCHOR: define_objective
		let objective_variable = match objective_type {
			ObjectiveType::Makespan => {
				let makespan = model.new_int_decision(0..=(instance.max_time as i64));
				for completion_time in completion_times {
					model.linear(makespan).ge(completion_time).post();
				}
				makespan
			}
			ObjectiveType::TotalCompletionTime => {
				let exp: IntLinearExp = completion_times.into_iter().sum();
				model.linear(exp).define()
			}
		};
		// ANCHOR_END: define_objective

		JobShopModel {
			model,
			start_time,
			objective: objective_variable,
		}
	}
}

impl Solution {
	/// Initialize an empty solution for the given instance.
	pub(crate) fn init(
		instance: &Instance,
		start_time: &[Vec<model::View<i64>>],
		map: &LoweringMap,
		slv: &mut Solver,
	) -> Self {
		let mut machine_schedule = vec![Vec::new(); instance.m];
		for (machine_id, schedule) in machine_schedule.iter_mut().enumerate() {
			for &(job_idx, op_idx) in &instance.operations_on_machine[machine_id] {
				let var = start_time[job_idx][op_idx];
				let start = map.get(slv, var);
				schedule.push((job_idx, op_idx, start));
			}
		}
		Solution {
			machine_schedule,
			start_time: None,
		}
	}

	/// Constructs a solution from the current solver assignment.
	pub(crate) fn save_assignment(&mut self, value: solver::Solution<'_>) {
		let mut start_time = Vec::with_capacity(self.machine_schedule.len());
		for ops in &self.machine_schedule {
			let mut machine_profile = Vec::new();
			for (job_idx, op_idx, start_view) in ops {
				machine_profile.push((*job_idx, *op_idx, Valuation::val(start_view, value)));
			}
			machine_profile.sort_by_key(|&(_, _, start)| start);
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

#[cfg(test)]
mod tests {
	use huub::{
		lower::InitConfig,
		solver::{Solver, Valuation},
	};

	use crate::model::{Instance, JobShopModel, ObjectiveType};

	#[test]
	fn optimal_completion_time_2x2() {
		let path = concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/jobshop/instances/2x2.jsp"
		);
		assert_eq!(solve_jobshop(path, ObjectiveType::TotalCompletionTime), 11);
	}

	#[test]
	fn optimal_completion_time_6x6() {
		let path = concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/jobshop/instances/6x6.jsp"
		);
		assert_eq!(solve_jobshop(path, ObjectiveType::TotalCompletionTime), 107);
	}

	#[test]
	fn optimal_makespan_2x2() {
		let path = concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/jobshop/instances/2x2.jsp"
		);
		assert_eq!(solve_jobshop(path, ObjectiveType::Makespan), 6);
	}

	#[test]
	fn optimal_makespan_6x6() {
		let path = concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/jobshop/instances/6x6.jsp"
		);
		assert_eq!(solve_jobshop(path, ObjectiveType::Makespan), 23);
	}

	/// Solves a job-shop scheduling instance using the given objective type and
	/// returns the optimal objective value.
	fn solve_jobshop(path: &str, objective_type: ObjectiveType) -> i64 {
		let instance = Instance::from_jsp_file(path).expect("failed to parse instance");
		let JobShopModel {
			mut model,
			objective,
			..
		} = JobShopModel::new(&instance, objective_type);
		let (mut slv, map): (Solver, _) = model.to_solver(&InitConfig::default()).unwrap();
		let obj = map.get(&mut slv, objective);
		let mut best = None;
		slv.solve()
			.on_solution(|sol| {
				best = Some(Valuation::val(&obj, sol));
			})
			.minimize(obj);
		best.expect("failed to find a solution")
	}
}
