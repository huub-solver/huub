//! Branching strategies for the job shop example.

use clap::{ValueEnum, builder::PossibleValue};
use huub::{
	DeepClone,
	actions::{
		BoolInspectionActions, BrancherInitActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, ReasoningContext, Trailed,
	},
	lower::LoweringMap,
	model::{self as huub_model, deserialize::Branching},
	solver::{
		self, IntLitMeaning, Solver,
		branchers::{Brancher, DecisionSelection, Directive, DomainSelection},
	},
};

use crate::model::{Instance, Job, Operation};

/// Branching strategies for variable selection in the job shop scheduling
/// problem.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum BranchingStrategy {
	/// A static branching strategy using the brancher implementations provided
	/// in Huub.
	Static(StaticBranching),
	/// A (custom) dynamic branching strategy specifically for the jobshop
	/// scheduling problem.
	Dynamic(DynamicBranching),
}

#[derive(Clone, Debug, DeepClone, Eq, PartialEq)]
/// A dynamic branching strategy that selects variables to branch on based on
/// the given [`DynamicBranching`] strategy.
struct DynamicBrancher {
	/// The dynamic branching strategy to use.
	strategy: DynamicBranching,
	/// The operations along with their start time variables.
	operations: Vec<(Operation, solver::View<i64>)>,
	/// The scores for each job computed during branching.
	scores: Vec<Trailed<usize>>,
	/// The start of the unfixed variables in `operations`.
	next: Trailed<usize>,
}

#[derive(DeepClone, Debug, Clone, Copy, PartialEq, Eq, Default)]
/// Branching strategies for [`DynamicBranching`], a specialized [`Brancher`]
/// implementation for the job shop scheduling problem.
pub(crate) enum DynamicBranching {
	#[default]
	/// Select the first available operation of the job with the least total
	/// processing time remaining across all jobs.
	LeastWork,
	/// Select the first available operation of the job with the most total
	/// processing time remaining across all jobs.
	MostWork,
	/// Select the first available operation of the job with the least number of
	/// operations remaining across all jobs.
	FewestOperations,
	/// Select the first available operation of the job with the most number of
	/// operations remaining across all jobs.
	MostOperations,
}

/// Branching strategy descriptions of branching strategies for jobshop that can
/// be implemented using the Huub standard [`Brancher`] implementations.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub(crate) enum StaticBranching {
	/// Select jobs in their input order and schedule all operations of a job
	/// before moving to the next job.
	#[default]
	JobInputOrder,
	/// Select jobs with the least total processing time first and schedule all
	/// operations of a job before moving to the next job.
	JobLeastTotalWork,
	/// Select jobs with the most total processing time first and schedule all
	/// operations of a job before moving to the next job.
	JobMostTotalWork,
	/// Select jobs with the fewest operations first and schedule all
	/// operations of a job before moving to the next job.
	JobFewestOperations,
	/// Select jobs with the most operations first and schedule all
	/// operations of a job before moving to the next job.
	JobMostOperations,
	/// Select operations in their input order.
	OperationInputOrder,
	/// Select operations with the longest processing time first.
	OperationLongestProcessingTime,
	/// Select operations with the shortest processing time first.
	OperationShortestProcessingTime,
}

impl BranchingStrategy {
	/// Adds a brancher for the [`BranchingStrategy`] to the solver.
	pub(crate) fn to_solver(
		self,
		solver: &mut Solver,
		map: &LoweringMap,
		start_time: &[Vec<huub_model::View<i64>>],
		instance: &Instance,
	) {
		match self {
			BranchingStrategy::Static(strategy) => {
				let branching = strategy.huub_branching(start_time, instance);
				branching.to_solver(solver, map);
			}
			BranchingStrategy::Dynamic(strategy) => {
				let mut lowered_start_time = Vec::with_capacity(start_time.len());
				for job_start_times in start_time {
					let mut lowered_job_start_times = Vec::with_capacity(job_start_times.len());
					for &op_start_time in job_start_times {
						lowered_job_start_times.push(map.get(solver, op_start_time));
					}
					lowered_start_time.push(lowered_job_start_times);
				}
				DynamicBrancher::new_in(solver, strategy, &lowered_start_time, &instance.jobs);
			}
		}
	}
}

impl Default for BranchingStrategy {
	fn default() -> Self {
		BranchingStrategy::Static(StaticBranching::JobInputOrder)
	}
}

impl ValueEnum for BranchingStrategy {
	fn to_possible_value(&self) -> Option<PossibleValue> {
		let name = match self {
			Self::Static(StaticBranching::JobInputOrder) => "job-input-order",
			Self::Static(StaticBranching::JobLeastTotalWork) => "job-least-total-work",
			Self::Static(StaticBranching::JobMostTotalWork) => "job-most-total-work",
			Self::Static(StaticBranching::JobFewestOperations) => "job-fewest-operations",
			Self::Static(StaticBranching::JobMostOperations) => "job-most-operations",
			Self::Static(StaticBranching::OperationInputOrder) => "operation-input-order",
			Self::Static(StaticBranching::OperationLongestProcessingTime) => {
				"operation-longest-processing-time"
			}
			Self::Static(StaticBranching::OperationShortestProcessingTime) => {
				"operation-shortest-processing-time"
			}
			Self::Dynamic(DynamicBranching::LeastWork) => "least-work",
			Self::Dynamic(DynamicBranching::MostWork) => "most-work",
			Self::Dynamic(DynamicBranching::FewestOperations) => "fewest-operations",
			Self::Dynamic(DynamicBranching::MostOperations) => "most-operations",
		};
		Some(PossibleValue::new(name))
	}

	fn value_variants<'a>() -> &'a [Self] {
		&[
			Self::Static(StaticBranching::JobInputOrder),
			Self::Static(StaticBranching::JobLeastTotalWork),
			Self::Static(StaticBranching::JobMostTotalWork),
			Self::Static(StaticBranching::JobFewestOperations),
			Self::Static(StaticBranching::JobMostOperations),
			Self::Static(StaticBranching::OperationInputOrder),
			Self::Static(StaticBranching::OperationLongestProcessingTime),
			Self::Static(StaticBranching::OperationShortestProcessingTime),
			Self::Dynamic(DynamicBranching::LeastWork),
			Self::Dynamic(DynamicBranching::MostWork),
			Self::Dynamic(DynamicBranching::FewestOperations),
			Self::Dynamic(DynamicBranching::MostOperations),
		]
	}
}

impl DynamicBrancher {
	/// Adds a new [`DynamicBrancher`] with the given strategy and start time
	/// variables within the solver.
	// ANCHOR: initialize_brancher
	fn new_in(
		solver: &mut impl BrancherInitActions,
		strategy: DynamicBranching,
		start_time: &[Vec<solver::View<i64>>],
		jobs: &[Job],
	) {
		for job_start_times in start_time {
			for &op_start_time in job_start_times {
				solver.ensure_decidable(op_start_time);
			}
		}

		let scores = vec![solver.new_trailed(0); jobs.len()];
		let mut operations = Vec::new();
		for (job_idx, job) in jobs.iter().enumerate() {
			for (op_idx, op) in job.iter().enumerate() {
				operations.push((*op, start_time[job_idx][op_idx]));
			}
		}

		let next = solver.new_trailed(0);
		solver.push_brancher(Box::new(DynamicBrancher {
			strategy,
			operations,
			scores,
			next,
		}));
	}
	// ANCHOR_END: initialize_brancher
}

impl<D> Brancher<D> for DynamicBrancher
where
	D: DecisionActions + ReasoningContext<Atom = solver::View<bool>>,
	solver::Decision<i64>: IntDecisionActions<D>,
	solver::Decision<bool>: BoolInspectionActions<D>,
{
	// ANCHOR: decide_method
	fn decide(&mut self, ctx: &mut D) -> Directive {
		let begin = ctx.trailed(self.next);
		if begin == self.operations.len() {
			return Directive::Exhausted;
		}

		let mut first_unfixed = begin;
		let mut first_unfixed_op = vec![None; self.scores.len()];
		let mut job_scores: Vec<_> = self
			.scores
			.iter()
			.map(|&score| ctx.trailed(score))
			.collect();

		for i in begin..self.operations.len() {
			let (operation, var) = &self.operations[i];
			let (lb, ub) = var.bounds(ctx);
			if lb == ub {
				match self.strategy {
					DynamicBranching::FewestOperations | DynamicBranching::MostOperations => {
						job_scores[operation.job_idx] += 1;
					}
					DynamicBranching::LeastWork | DynamicBranching::MostWork => {
						job_scores[operation.job_idx] += operation.processing_time;
					}
				}

				let unfixed_var = self.operations[first_unfixed];
				let fixed_var = self.operations[i];
				self.operations[first_unfixed] = fixed_var;
				self.operations[i] = unfixed_var;
				first_unfixed += 1;
			} else if first_unfixed_op[operation.job_idx]
				.is_none_or(|(incumbent_idx, _)| operation.op_idx < incumbent_idx)
			{
				first_unfixed_op[operation.job_idx] =
					Some((operation.op_idx, self.operations[i].1));
			}
		}

		let selected_job = job_scores
			.iter()
			.enumerate()
			.filter(|(job_idx, _)| first_unfixed_op[*job_idx].is_some())
			.max_by(|(_, score_a), (_, score_b)| match self.strategy {
				DynamicBranching::LeastWork | DynamicBranching::FewestOperations => {
					score_b.cmp(score_a)
				}
				DynamicBranching::MostWork | DynamicBranching::MostOperations => {
					score_a.cmp(score_b)
				}
			});
		let Some((selected_job_idx, _)) = selected_job else {
			return Directive::Exhausted;
		};

		for (job_idx, &score) in job_scores.iter().enumerate() {
			let _ = ctx.set_trailed(self.scores[job_idx], score);
		}
		let _ = ctx.set_trailed(self.next, first_unfixed);

		let op_view = first_unfixed_op[selected_job_idx]
			.expect("the selected job must have an unfixed operation")
			.1;
		let lb = op_view.min(ctx);
		Directive::Select(op_view.lit(ctx, IntLitMeaning::Less(lb + 1)))
	}
	// ANCHOR_END: decide_method
}

impl StaticBranching {
	/// Creates a static branching strategy for the job shop scheduling problem.
	fn huub_branching(
		self,
		start_time: &[Vec<huub_model::View<i64>>],
		instance: &Instance,
	) -> Branching {
		let mut vars = Vec::new();
		match self {
			StaticBranching::JobInputOrder | StaticBranching::OperationInputOrder => {
				// Order jobs or operations by their original order in the input.
				for &op in start_time.iter().flatten() {
					vars.push(op);
				}
			}
			StaticBranching::JobLeastTotalWork | StaticBranching::JobMostTotalWork => {
				// Order jobs by total processing time.
				let mut job_work: Vec<(usize, i64)> = (0..instance.n)
					.map(|job_idx| {
						let work = instance.jobs[job_idx]
							.iter()
							.map(|op| op.processing_time as i64)
							.sum();
						(job_idx, work)
					})
					.collect();
				job_work.sort_by(|a, b| {
					if self == StaticBranching::JobMostTotalWork {
						b.1.cmp(&a.1)
					} else {
						a.1.cmp(&b.1)
					}
				});
				for (job_idx, _) in job_work {
					for &op in &start_time[job_idx] {
						vars.push(op);
					}
				}
			}
			StaticBranching::JobMostOperations | StaticBranching::JobFewestOperations => {
				// Order jobs by the number of remaining operations.
				let mut job_lengths: Vec<(usize, i64)> = (0..instance.n)
					.map(|job_idx| (job_idx, instance.jobs[job_idx].len() as i64))
					.collect();
				job_lengths.sort_by(|a, b| {
					if self == StaticBranching::JobMostOperations {
						b.1.cmp(&a.1)
					} else {
						a.1.cmp(&b.1)
					}
				});
				for (job_idx, _) in job_lengths {
					for &op in &start_time[job_idx] {
						vars.push(op);
					}
				}
			}
			StaticBranching::OperationLongestProcessingTime
			| StaticBranching::OperationShortestProcessingTime => {
				// Order all operations by processing time.
				let mut operations = Vec::new();
				for (job_idx, job) in instance.jobs.iter().enumerate() {
					for (op_idx, op) in job.iter().enumerate() {
						operations.push((job_idx, op_idx, op.processing_time as i64));
					}
				}
				operations.sort_by(|a, b| {
					if self == StaticBranching::OperationLongestProcessingTime {
						b.2.cmp(&a.2)
					} else {
						a.2.cmp(&b.2)
					}
				});

				for (job_idx, op_idx, _) in operations {
					vars.push(start_time[job_idx][op_idx]);
				}
			}
		}

		Branching::Int(
			vars,
			DecisionSelection::InputOrder,
			DomainSelection::IndomainMin,
		)
	}
}
