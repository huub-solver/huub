//! Module containing the central solving infrastructure.

pub(crate) mod activation_list;
pub(crate) mod bool_to_int;
pub mod branchers;
pub(crate) mod decision;
pub(crate) mod engine;
pub(crate) mod initialization_context;
pub(crate) mod queue;
pub(crate) mod solution;
pub(crate) mod solving_context;
pub(crate) mod trail;
pub(crate) mod view;

use std::{
	any::Any,
	cell::{RefCell, RefMut},
	fmt::Debug,
	hash::Hash,
	mem,
	num::NonZero,
	ops::{Add, AddAssign, Not},
	rc::Rc,
};

use bon::{Builder, bon};
use itertools::Itertools;
pub use pindakaas::solver::cadical::Cadical;
use pindakaas::{
	ClauseDatabase, ClauseDatabaseTools, Lit as RawLit, Unsatisfiable, VarRange,
	solver::{
		Assumptions, FailedAssumptions, LearnCallback, SolveResult as SatSolveResult,
		TerminateCallback,
		propagation::{ExternalPropagation, SolvingActions},
	},
};
use rangelist::IntervalIterator;
use rustc_hash::FxHashMap;
use tracing::{debug, warn};

pub use crate::solver::{
	decision::{Decision, DecisionReference},
	solution::{AnyView, Solution, Valuation, Value},
	view::{DefaultView, View, boolean::BoolView, integer::IntView},
};
use crate::{
	Clause, IntSet, IntVal,
	actions::{
		BrancherInitActions, ConstructionActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, PostingActions, ReasoningContext, ReasoningEngine, Trailed,
		TrailingActions,
	},
	constraints::{BoxedPropagator, Conflict},
	helpers::bytes::Bytes,
	solver::{
		branchers::BoxedBrancher,
		decision::integer::{DirectStorage, IntDecision, LazyOrderStorage, OrderStorage},
		engine::{Engine, PropRef},
		initialization_context::InitializationContext,
		queue::PropagatorInfo,
	},
	views::LinearBoolView,
};

/// Trait implemented by the object given to the callback when assumption
/// solving detects unsatisfiability.
pub trait AssumptionChecker {
	/// Check if the given assumption literal was used to prove the
	/// unsatisfiability of the formula under the assumptions used for the last
	/// SAT search.
	///
	/// Note that for Boolean views that are not assumption literals, the
	/// behavior is unspecified.
	fn fail(&self, bv: View<bool>) -> bool;
}

/// Helper method for collecting solution values.
#[derive(Debug, Eq, PartialEq)]
pub struct CollectSolutionsIn<'a, View: Valuation> {
	/// Decision variables to track.
	vars: Vec<View>,
	/// Mutable reference to storage for collected solutions.
	store: &'a mut Vec<Vec<View::Val>>,
}

/// Statistics related to the initialization of the solver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InitStatistics {
	/// Number of (non-view) Boolean decision variables present in the solver.
	pub bool_decisions: usize,
	/// Number of (non-view) integer decision variables present in the solver.
	pub int_decisions: usize,
	/// Number of propagators in the solver.
	pub propagators: usize,
}

/// The meaning of a literal in the context of an integer decision variable `x`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntLitMeaning {
	/// Literal representing the condition `x = i`.
	Eq(IntVal),
	/// Literal representing the condition `x ≠ i`.
	NotEq(IntVal),
	/// Literal representing the condition `x ≥ i`.
	GreaterEq(IntVal),
	/// Literal representing the condition `x < i`.
	Less(IntVal),
}

/// Strategy used to create SAT literals for complex decision variables.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum LiteralStrategy {
	/// All literals are created before solving starts.
	Eager,
	/// Literals are created the first time they are requested.
	#[default]
	Lazy,
}

/// An assumption checker that can be used when no assumptions are used.
///
/// Note that this checker will always return false.
pub(crate) struct NoAssumptions;

/// Preferred search direction for an integer decision variable.
///
/// The polarity is used to set the phase of the underlying Boolean literals so
/// that the SAT solver tries the preferred direction first, and to decide to
/// which bound an unfixed integer variable is fixed during solution checking.
///
/// The absence of a preferred direction is represented by `Option<Polarity>`'s
/// `None`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum Polarity {
	/// Prefer larger values (push the variable toward its upper bound).
	Positive,
	/// Prefer smaller values (push the variable toward its lower bound).
	Negative,
}

/// The overarching search strategy used by the solver.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub enum SearchStrategy {
	/// Use the user provided [`Brancher`](crate::solver::branchers::Brancher)s
	/// until they are all exhausted, and only then defer to the SAT solver to
	/// make search decisions.
	#[default]
	Branchers,
	/// Always defer to the SAT solver to make search decisions, ignoring any
	/// user provided [`Brancher`](crate::solver::branchers::Brancher)s.
	Sat,
	/// Transition from [`SearchStrategy::Branchers`] to [`SearchStrategy::Sat`]
	/// when the given trigger condition is met.
	Transition(SwitchTrigger),
	/// Interleave [`SearchStrategy::Branchers`] and [`SearchStrategy::Sat`]
	/// search strategies, switching between them each time the trigger
	/// condition is met.
	Interleaved(SwitchTrigger),
}

/// Callback invoked each time a solution is found.
///
/// Implement this trait or use a closure to react to discovered solutions.
/// The callback receives a [`Solution`] reference for querying decision
/// variable values.
pub trait SolutionCallback {
	/// Handle a newly found solution.
	///
	/// This method receives a reference to the current solution. Use the
	/// [`Valuation`] trait to extract decision variable values.
	fn on_solution(&mut self, sol: Solution<'_>);
}

/// Internal struct representing complete solve arguments.
///
/// Users interact with this through the public [`SolveArgs`] builder type
/// returned by [`Solver::solve`].
#[derive(Builder)]
#[builder(
	builder_type(
		name = SolveArgs,
		vis = "pub",
		doc {
			/// Builder to configure and execute a solve operation.
			///
			/// Obtained by calling [`Solver::solve()`]. The builder uses type-state
			/// parameters to enforce that each option is set at most once and that
			/// terminal methods are only callable on a fully configured instance.
			///
			/// # Terminal methods
			///
			/// Call one of the following to execute the solve and consume the builder:
			///
			/// - **[`.satisfy()`][SolveArgs::satisfy]**: search for any satisfying
			///   assignment.
			/// - **[`.minimize(obj)`][SolveArgs::minimize]**: find the assignment
			///   minimizing `obj` via branch-and-bound.
			/// - **[`.maximize(obj)`][SolveArgs::maximize]**: find the assignment
			///   maximizing `obj` via branch-and-bound.
		}
	),
  generics(setters(name = "with_{}", vis = "")),
  start_fn(vis = "", name = builder_internal),
  finish_fn(vis = "", name = finalize_internal),
)]
struct SolveArgsComplete<'a, Sat, S, F>
where
	S: SolutionCallback,
	F: FnOnce(&dyn AssumptionChecker),
{
	/// Reference to the solver being used for the search.
	/// This field is set directly by [`Solver::solve`].
	#[builder(setters(name = solver_internal, vis = ""))]
	solver: &'a mut Solver<Sat>,
	/// Boolean assumptions to pass to the underlying SAT solver.
	///
	/// Assumptions are used to restrict the SAT solver to consider the search
	/// space where all assumptions are satisfied. Assumptions are temporary:
	/// they are only used for the current solve call.
	#[builder(default = Vec::new(), with = FromIterator::from_iter)]
	assuming: Vec<View<bool>>,
	/// Optional callback invoked each time a solution is found.
	///
	/// The callback receives a reference to the current solution context,
	/// allowing inspection of decision variable values via the [`Valuation`]
	/// trait.
	///
	/// Behavior:
	/// - For satisfiability checks (`.satisfy()`): called at most once.
	/// - For optimization (`.minimize()`, `.maximize()`): called for each
	///   improving solution.
	/// - For all-solutions enumeration: called for each distinct solution
	///   found.
	/// - If not set, solutions are accepted silently.
	#[builder(setters(name = on_solution_internal, vis = ""))]
	on_solution: Option<S>,
	/// Optional callback invoked when the SAT solver reports unsatisfiability.
	///
	/// The callback receives an [`AssumptionChecker`], which allows analyzing
	/// which assumptions (if any) contributed to the conflict. This is useful
	/// for debugging infeasible problems or implementing iterative relaxation
	/// strategies.
	#[builder(setters(name = on_failure_internal, vis = ""))]
	on_failure: Option<F>,
	/// Optional list of decision variable views for exhaustive solution
	/// enumeration.
	///
	/// When set in combination with `.minimize()` or `.maximize()`, the solver
	/// will continue to search for all other solutions with the same optimal
	/// objective value after the first optimum is found.
	///
	/// Behavior:
	/// - If unset, then standard search is performed, stopping at the first
	///   solution or once optimality is proven.
	/// - If set with `.satisfy()`: enumerate all feasible solutions
	/// - If set with `.minimize()`/`.maximize()`: find all optimal solutions
	///
	///
	/// # Warning
	///
	/// No-good clauses are added internally to prevent re-visiting
	/// solutions. This tightens the search space permanently and cannot be
	/// undone.
	#[builder(setters(name = all_solutions_internal, vis = ""))]
	all_solutions: Option<Vec<AnyView>>,
	/// Controls whether to use clauses to communicate objective bounds to the
	/// SAT solver during optimization.
	///
	/// Two strategies are supported:
	///
	/// - **False (default)**: Objective bounds are passed as assumptions to the
	///   SAT solver. Assumptions are released after each solve attempt. This is
	///   useful when exploring multiple scenarios or performing incremental
	///   solving.
	///
	/// - **True**: Objective bounds are added as permanent clauses to the
	///   solver. **warning**: this tightens the search space permanently and
	///   cannot be undone. Use this when performing standalone optimization
	///   where the solver instance is not needed later.
	///
	/// Note: This setting is ignored if `all_solutions` is set, in which case
	/// assumptions are always used to ensure no-good clauses work correctly.
	bind_using_clauses: Option<bool>,
}

/// The main solver object that is used to interact with the LCG solver.
#[derive(Debug)]
pub struct Solver<Sat = Cadical> {
	/// The SAT solver that has been connected to [`Self::engine`] to perform
	/// external propagation.
	pub(crate) sat: Sat,
	/// A reference to the [`Engine`] instance that is connected to
	/// [`Self::sat`].
	pub(crate) engine: Rc<RefCell<Engine>>,
}

/// Structure capturing statistical information about the solver instance and
/// the search it has performed.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub struct SolverStatistics {
	/// Number of conflicts encountered during the search.
	pub conflicts: u64,
	/// Number of search directives made by the SAT solver.
	pub sat_search_directives: u64,
	/// Peak depth of the search tree.
	pub peak_depth: u32,
	/// Number of times a [`Propagator`](crate::constraints::Propagator)
	/// instance was called.
	pub cp_propagator_calls: u64,
	/// Number of times the search was restarted from the root (as signalled by
	/// the SAT solver).
	pub restarts: u32,
	/// Number of search directives made by the user-specified search
	/// heuristics
	pub user_search_directives: u64,
	/// Number of eagerly created SAT literals to represent decisions variables
	pub eager_literals: u64,
	/// Number of lazily created SAT literals to represent decision variables
	pub lazy_literals: u64,
}

/// Result of a solving attempt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Status {
	/// The solver has found a solution.
	Satisfied,
	/// The solver has proven that the problem is unsatisfiable.
	Unsatisfiable,
	/// The solver has proven that no more or better solutions can be found.
	Complete,
	/// The solver was interrupted before a result could be reached.
	Unknown,
}

/// Trigger for switching between search strategies.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SwitchTrigger {
	/// Switch after the given number of conflicts have been encountered.
	Conflicts(u64),
	/// Switch after the given number of restarts have been encountered.
	Restarts(u64),
}

/// Type alias for a signal given by callbacks to the [`Solver`] to indicate
/// whether it should terminate.
pub type TerminationSignal = pindakaas::solver::TermSignal;

/// Helper function that calls [`tracing::debug!`] on learned clauses.
///
/// This function is used as part of the callback given to the SAT solver.
fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(
		target: "solver",
		clause = ?clause.map(i32::from).collect::<Vec<i32>>(),
		"learn clause"
	);
}

impl<A: FailedAssumptions> AssumptionChecker for A {
	fn fail(&self, bv: View<bool>) -> bool {
		match bv.0 {
			BoolView::Lit(lit) => self.fail(lit.0),
			BoolView::Const(false) => true,
			BoolView::Const(true) => false,
		}
	}
}

/// Implementation of solution collection callback.
impl<'a, View: Valuation> SolutionCallback for CollectSolutionsIn<'a, View> {
	fn on_solution(&mut self, sol: Solution<'_>) {
		self.store
			.push(self.vars.iter().map(|v| Valuation::val(v, sol)).collect());
	}
}

/// Blanket implementation for closures and function pointers.
impl<F> SolutionCallback for F
where
	F: for<'a> FnMut(Solution<'a>),
{
	fn on_solution(&mut self, sol: Solution<'_>) {
		self(sol);
	}
}

impl IntLitMeaning {
	/// Returns the clauses that can be used to define the given literal
	/// according to the meaning `self`.
	///
	/// Note this method is only intended to be used to define positive
	/// literals, and it is thus assumed to be unreachable to be called on
	/// [`LitMeaning::NotEq`] or [`LitMeaning::GreaterEq`].
	pub(crate) fn defining_clauses(
		&self,
		lit: RawLit,
		prev: Option<RawLit>,
		next: Option<RawLit>,
	) -> Vec<Clause<RawLit>> {
		let mut ret = Vec::<Clause<RawLit>>::new();
		match self {
			IntLitMeaning::Eq(_) => {
				let prev = prev.expect("prev should contain the GreaterEq literal for the value"); // x≥i
				let next =
					next.expect("next should contain the GreaterEq literal for the next value"); // x≥i+n

				ret.push(vec![!lit, !prev]); // x=i -> x≥i
				ret.push(vec![!lit, next]); // x=i -> x<i+n
				ret.push(vec![lit, prev, !next]); // x!=i -> x<i \/ x>i+n
			}
			IntLitMeaning::Less(_) => {
				if let Some(prev) = prev {
					ret.push(vec![!prev, lit]); // x<(i-n) -> x<i
				}
				if let Some(next) = next {
					ret.push(vec![!lit, next]); // x<i -> x<(i+n)
				}
			}
			_ => unreachable!(),
		}
		ret
	}
}

impl Not for IntLitMeaning {
	type Output = IntLitMeaning;

	fn not(self) -> Self::Output {
		match self {
			IntLitMeaning::Eq(i) => IntLitMeaning::NotEq(i),
			IntLitMeaning::NotEq(i) => IntLitMeaning::Eq(i),
			IntLitMeaning::GreaterEq(i) => IntLitMeaning::Less(i),
			IntLitMeaning::Less(i) => IntLitMeaning::GreaterEq(i),
		}
	}
}

impl AssumptionChecker for NoAssumptions {
	fn fail(&self, bv: View<bool>) -> bool {
		matches!(bv.0, BoolView::Const(false))
	}
}

impl Not for Polarity {
	type Output = Self;

	fn not(self) -> Self {
		match self {
			Polarity::Positive => Polarity::Negative,
			Polarity::Negative => Polarity::Positive,
		}
	}
}

impl<'a, Sat, S, F, State: solve_args::State> SolveArgs<'a, Sat, S, F, State>
where
	S: SolutionCallback,
	F: FnOnce(&dyn AssumptionChecker),
{
	/// Enable exhaustive solution enumeration for selected decision variable
	/// views.
	///
	/// When set, the solver will continue searching after finding the requested
	/// solution, collecting all distinct solutions for the given views. In case
	/// of:
	/// - **Satisfiability checks**: It finds all feasible solutions
	/// - **Optimization**: If finds all solutions with the same optimal
	///   objective value
	pub fn all_solutions<T: Into<AnyView>>(
		self,
		views: impl IntoIterator<Item = T>,
	) -> SolveArgs<'a, Sat, S, F, solve_args::SetAllSolutions<State>>
	where
		State::AllSolutions: solve_args::IsUnset,
	{
		self.maybe_all_solutions(Some(views))
	}

	/// Collect solution values into a vector for later inspection.
	///
	/// Convenience method that creates a [`SolutionCallback`] implementation
	/// to automatically gather variable values from each solution found.
	/// Solutions are stored in row-major order (one solution per row).
	///
	/// # Arguments
	///
	/// - `vars`: List of decision variable views to track
	/// - `store`: Mutable vector where solutions will be appended
	///
	/// # Important
	///
	/// This method only sets up the callback to collect solutions. To actually
	/// enumerate all solutions, you must also call `.all_solutions(vars)` with
	/// the same (or related) variables, or the search will terminate after
	/// finding the first solution.
	///
	/// # Examples
	///
	/// Collect all satisfying assignments:
	/// ```
	/// # use huub::solver::{Solver, Status};
	/// # let mut solver: Solver = Solver::default();
	/// # let x = solver.new_int_decision(1..=3).view();
	/// # let y = solver.new_int_decision(1..=3).view();
	/// let mut solutions = Vec::new();
	/// let status = solver
	/// 	.solve()
	/// 	.all_solutions([x, y])
	/// 	.collect_solutions_in(vec![x, y], &mut solutions)
	/// 	.satisfy();
	/// assert_eq!(status, Status::Complete);
	/// // solutions now contains all feasible (x, y) pairs
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn collect_solutions_in<'b, View: Valuation>(
		self,
		vars: Vec<View>,
		store: &'b mut Vec<Vec<View::Val>>,
	) -> SolveArgs<'a, Sat, CollectSolutionsIn<'b, View>, F, solve_args::SetOnSolution<State>>
	where
		State::OnSolution: solve_args::IsUnset,
	{
		// Note: Unfortunately due to Rust's type system limitations, we cannot
		// automatically convert the View variables to AnyView here for the
		// all_solutions field. The caller must explicitly use
		// .all_solutions() if they need it.
		self.with_s::<CollectSolutionsIn<'b, View>>()
			.on_solution_internal(CollectSolutionsIn { vars, store })
	}

	/// Find a solution that maximizes the given objective expression.
	pub fn maximize(self, objective: impl Into<View<IntVal>>) -> (Status, Option<IntVal>)
	where
		Sat: ExternalPropagation + Assumptions,
		State::Solver: solve_args::IsSet,
	{
		let objective = objective.into();
		let (status, opt) = self.minimize(-objective);
		(status, opt.map(|v| -v))
	}

	/// Enable exhaustive solution enumeration for selected decision variable
	/// views.
	///
	/// When set, the solver will continue searching after finding the requested
	/// solution, collecting all distinct solutions for the given views. In case
	/// of:
	/// - **Satisfiability checks**: It finds all feasible solutions
	/// - **Optimization**: If finds all solutions with the same optimal
	///   objective value
	pub fn maybe_all_solutions<T: Into<AnyView>>(
		self,
		views: Option<impl IntoIterator<Item = T>>,
	) -> SolveArgs<'a, Sat, S, F, solve_args::SetAllSolutions<State>>
	where
		State::AllSolutions: solve_args::IsUnset,
	{
		self.maybe_all_solutions_internal(views.map(|v| v.into_iter().map(|v| v.into()).collect()))
	}

	/// Conditionally register a failure callback.
	///
	/// Behaves like [`on_failure`](Self::on_failure) when given `Some`, and
	/// leaves the callback unset when given `None`.
	pub fn maybe_on_failure<NewF>(
		self,
		on_failure: Option<NewF>,
	) -> SolveArgs<'a, Sat, S, NewF, solve_args::SetOnFailure<State>>
	where
		State::OnFailure: solve_args::IsUnset,
		NewF: FnOnce(&dyn AssumptionChecker),
	{
		self.with_f::<NewF>().maybe_on_failure_internal(on_failure)
	}

	/// Conditionally register a solution callback.
	///
	/// Behaves like [`on_solution`](Self::on_solution) when given `Some`, and
	/// leaves the callback unset when given `None`.
	pub fn maybe_on_solution<NewS>(
		self,
		on_solution: Option<NewS>,
	) -> SolveArgs<'a, Sat, NewS, F, solve_args::SetOnSolution<State>>
	where
		State::OnSolution: solve_args::IsUnset,
		NewS: for<'b> FnMut(Solution<'b>),
	{
		self.with_s::<NewS>()
			.maybe_on_solution_internal(on_solution)
	}

	/// Find a solution that minimizes the given objective expression.
	/// Implements branch-and-bound search, iteratively improving the solution
	/// until proven optimal.
	pub fn minimize(self, objective: impl Into<View<IntVal>>) -> (Status, Option<IntVal>)
	where
		Sat: ExternalPropagation + Assumptions,
		State::Solver: solve_args::IsSet,
	{
		use Status::*;

		// Process arguments
		let SolveArgsComplete {
			solver,
			assuming,
			mut on_solution,
			on_failure,
			all_solutions,
			bind_using_clauses,
		} = self.finalize_internal();
		let mut bind_using_clauses = bind_using_clauses.unwrap_or(false);
		if bind_using_clauses && all_solutions.is_some() {
			warn!("bind_using_clauses option ignored because all_solutions is enabled");
			bind_using_clauses = false;
		}

		// Process assumptions
		let Ok(mut assumptions): Result<Vec<RawLit>, _> = assuming
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => None,
				BoolView::Const(false) => Some(Err(())),
			})
			.collect()
		else {
			if let Some(on_failure) = on_failure {
				on_failure(&NoAssumptions);
			}
			return (Unsatisfiable, None);
		};

		// Start branch and bound loop
		let objective = objective.into();
		let mut obj_curr = None;
		let obj_bound = objective.min(solver);
		let mut obj_assump = None;
		let mut vals: Vec<Value> = vec![
			Value::Int(0);
			if let Some(all_solutions) = &all_solutions {
				all_solutions.len()
			} else {
				0
			}
		];

		debug!(target: "solver", obj_bound, "start branch and bound");
		let (status, obj) = loop {
			let result = solver
				.sat
				.solve_assuming(assumptions.iter().cloned().chain(obj_assump));
			match result {
				SatSolveResult::Satisfied(ref sol) => {
					let sol = Solution {
						sat: sol,
						state: &solver.engine.borrow().state,
					};
					obj_curr = Some(Valuation::val(&objective, sol));
					if let Some(callback) = &mut on_solution {
						callback.on_solution(sol);
					}
					if let Some(vars) = &all_solutions {
						for (i, v) in vars.iter().enumerate() {
							vals[i] = Valuation::val(v, sol);
						}
					}
					debug!(
						target: "solver",
						?obj_curr,
						obj_bound,
						"sat solve result"
					);
				}
				// Latest SAT solve was unsatisfiable:
				// - If no previous solution was found, then the problem doesn't have any feasible
				//   solutions.
				// - If a previous solution was found, then the current bound is the best solution
				//   under the current constraints and assumptions.
				SatSolveResult::Unsatisfiable(fail) => {
					if let Some(on_failure) = on_failure {
						on_failure(&fail);
					}
					break if obj_curr.is_none() {
						(Unsatisfiable, None)
					} else {
						(Complete, obj_curr)
					};
				}
				// Latest SAT solve returned unknown: this indicates that the
				// solver reached a search limit.
				// We return `Satisfied` if we found at least one solution,
				// and `Unknown` if we didn't find any solutions yet.
				SatSolveResult::Unknown => {
					break if obj_curr.is_none() {
						(Unknown, None)
					} else {
						(Satisfied, obj_curr)
					};
				}
			}
			drop(result);

			if obj_curr == Some(obj_bound) {
				if let Some(on_failure) = on_failure {
					on_failure(&NoAssumptions);
				}
				break (Complete, obj_curr);
			} else {
				let bound_lit = objective.lit(solver, IntLitMeaning::Less(obj_curr.unwrap()));
				debug!(
					target: "solver",
					clause = bind_using_clauses,
					lit = i32::from({
						let BoolView::Lit(l) = bound_lit.0 else {
							unreachable!()
						};
						l.0
					}),
					"add objective bound"
				);
				if bind_using_clauses {
					solver.add_clause([bound_lit]).unwrap();
				} else {
					let BoolView::Lit(l) = bound_lit.0 else {
						unreachable!()
					};
					obj_assump = Some(l.0);
				}
			}
		};
		if all_solutions.is_none() || status != Complete {
			return (status, obj);
		}

		// Continue to look for all other solutions with the same objective value.
		// Solutions already visited are added as (permanent) no-good clauses.
		let vars = all_solutions.unwrap();
		let BoolView::Lit(opt_lit) = objective
			.lit(solver, IntLitMeaning::Eq(obj_curr.unwrap()))
			.0
		else {
			unreachable!()
		};
		assumptions.push(opt_lit.0);
		loop {
			solver.add_no_good(&vars, &vals).unwrap();

			let result = solver.sat.solve_assuming(assumptions.clone());
			match result {
				SatSolveResult::Satisfied(ref sol) => {
					let sol = Solution {
						sat: sol,
						state: &solver.engine.borrow().state,
					};
					obj_curr = Some(Valuation::val(&objective, sol));
					if let Some(callback) = &mut on_solution {
						callback.on_solution(sol);
					}
					for (i, v) in vars.iter().enumerate() {
						vals[i] = Valuation::val(v, sol);
					}
					debug!(
						target: "solver",
						?obj_curr,
						obj_bound,
						"sat solve result"
					);
				}
				SatSolveResult::Unsatisfiable(_) => break (Complete, obj_curr),
				SatSolveResult::Unknown => break (Satisfied, obj_curr),
			}
		}
	}

	/// Register a failure callback for assumption analysis.
	///
	/// The callback is invoked when the SAT solver reports unsatisfiability.
	/// It receives an [`AssumptionChecker`] object that can determine which
	/// assumptions contributed to the conflict.
	pub fn on_failure<NewF>(
		self,
		on_failure: NewF,
	) -> SolveArgs<'a, Sat, S, NewF, solve_args::SetOnFailure<State>>
	where
		State::OnFailure: solve_args::IsUnset,
		NewF: FnOnce(&dyn AssumptionChecker),
	{
		self.with_f::<NewF>().on_failure_internal(on_failure)
	}

	/// Register a solution callback.
	///
	/// The callback is invoked each time a solution is found:
	/// - For satisfiability checks: called at most once
	/// - For optimization: called each time a better solution is found
	/// - For all-solutions: called for each distinct solution
	pub fn on_solution<NewS>(
		self,
		on_solution: NewS,
	) -> SolveArgs<'a, Sat, NewS, F, solve_args::SetOnSolution<State>>
	where
		State::OnSolution: solve_args::IsUnset,
		NewS: for<'b> FnMut(Solution<'b>),
	{
		self.with_s::<NewS>().on_solution_internal(on_solution)
	}

	/// Execute a satisfiability check.
	///
	/// Searches for any assignment satisfying all constraints and assumptions.
	/// The search generally terminates as soon as a solution is found (or when
	/// we determine no solution is possible). However, if `all_solutions` is
	/// set, the search will continue to enumerate all feasible solutions.
	pub fn satisfy(self) -> Status
	where
		Sat: ExternalPropagation + Assumptions,
		State: solve_args::IsComplete,
	{
		let SolveArgsComplete {
			solver,
			assuming,
			mut on_solution,
			on_failure,
			all_solutions,
			..
		} = self.finalize_internal();

		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assuming
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => None,
				BoolView::Const(false) => Some(Err(())),
			})
			.collect()
		else {
			if let Some(on_failure) = on_failure {
				on_failure(&NoAssumptions);
			}
			return Status::Unsatisfiable;
		};

		let mut has_solution = false;
		loop {
			let result = solver.sat.solve_assuming(assumptions.clone());
			let vals: Vec<_> = match result {
				SatSolveResult::Satisfied(ref sol) => {
					let sol = Solution {
						sat: sol,
						state: &solver.engine.borrow().state,
					};
					has_solution = true;
					if let Some(callback) = &mut on_solution {
						callback.on_solution(sol);
					}
					if let Some(vars) = &all_solutions {
						vars.iter().map(|v| v.val(sol)).collect()
					} else {
						break Status::Satisfied;
					}
				}
				SatSolveResult::Unsatisfiable(fail) => {
					if let Some(on_failure) = on_failure {
						on_failure(&fail);
					}
					break if has_solution {
						Status::Complete
					} else {
						Status::Unsatisfiable
					};
				}
				SatSolveResult::Unknown => {
					break if has_solution {
						Status::Satisfied
					} else {
						Status::Unknown
					};
				}
			};
			drop(result);

			debug_assert!(all_solutions.is_some());
			let vars = all_solutions.as_ref().unwrap();
			if solver.add_no_good(vars, &vals).is_err() {
				break Status::Complete;
			}
		}
	}
}

impl<Sat: ClauseDatabase> Solver<Sat> {
	/// Add a clause to the solver
	pub fn add_clause<Iter>(
		&mut self,
		clause: Iter,
	) -> Result<(), <Self as ReasoningContext>::Conflict>
	where
		Iter: IntoIterator,
		Iter::Item: Into<View<bool>>,
	{
		let clause = clause.into_iter().map(Into::into).collect_vec();
		match ClauseDatabaseTools::add_clause(&mut self.sat, clause.clone()) {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => Err(Conflict::new(
				self,
				None,
				clause.into_iter().map(|l| !l).collect_vec(),
			)),
		}
	}
}

impl<Sat: ExternalPropagation + Assumptions> Solver<Sat> {
	/// Solve the problem given the current state.
	///
	/// This is the main entry point for all solving operations. It returns a
	/// fluent builder API that allows configuring solve options and callbacks
	/// before execution.
	///
	/// # Examples
	///
	/// Simple satisfiability solving:
	/// ```
	/// # use huub::solver::{Solver, Status};
	/// # let mut solver: Solver = Solver::default();
	/// let status = solver.solve().satisfy();
	/// assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	///
	/// Satisfiability with callback to inspect solution:
	/// ```
	/// # use huub::solver::{Solver, Status, Valuation};
	/// # let mut solver: Solver = Solver::default();
	/// # let x = solver.new_int_decision(1..=4).view();
	/// let mut value = None;
	/// let status = solver
	/// 	.solve()
	/// 	.on_solution(|solution| {
	/// 		value = Some(x.val(solution));
	/// 	})
	/// 	.satisfy();
	/// assert_eq!(status, Status::Satisfied);
	/// assert!(value.is_some());
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	///
	/// Optimization with callbacks:
	/// ```
	/// # use huub::solver::{Solver, Status};
	/// # let mut solver: Solver = Solver::default();
	/// # let x = solver.new_int_decision(1..=4).view();
	/// let (status, optimum) = solver.solve().on_solution(|_| {}).minimize(x);
	/// assert_eq!(status, Status::Complete);
	/// assert_eq!(optimum, Some(1));
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	///
	/// With assumptions for incremental solving:
	/// ```
	/// # use huub::solver::{Solver, Status};
	/// # let mut solver: Solver = Solver::default();
	/// # let b = solver.new_bool_decision();
	/// let status = solver
	/// 	.solve()
	/// 	.assuming([b.into()])
	/// 	.on_failure(|_| {})
	/// 	.satisfy();
	/// assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	///
	/// Enumerating all solutions:
	/// ```
	/// # use huub::solver::{Solver, Status};
	/// # let mut solver: Solver = Solver::default();
	/// # let x = solver.new_int_decision(1..=3).view();
	/// let mut count = 0;
	/// let status = solver
	/// 	.solve()
	/// 	.all_solutions([x])
	/// 	.on_solution(|_| count += 1)
	/// 	.satisfy();
	/// assert_eq!(status, Status::Complete);
	/// assert_eq!(count, 3);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn solve<'a>(
		&'a mut self,
	) -> SolveArgs<
		'a,
		Sat,
		for<'b> fn(Solution<'b>),
		for<'b> fn(&'b dyn AssumptionChecker),
		solve_args::SetSolver,
	> {
		SolveArgsComplete::builder_internal().solver_internal(self)
	}

	/// Try to find a solution to the problem for which the [`Solver`] was
	/// initialized, using the given Boolean assumptions.
	pub fn solve_assuming(
		&mut self,
		assumptions: impl IntoIterator<Item = View<bool>>,
		mut on_sol: impl FnMut(Solution<'_>),
		on_fail: impl FnOnce(&dyn AssumptionChecker),
	) -> Status {
		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assumptions
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => None,
				BoolView::Const(false) => Some(Err(())),
			})
			.collect()
		else {
			on_fail(&NoAssumptions);
			return Status::Unsatisfiable;
		};

		let result = self.sat.solve_assuming(assumptions);
		match result {
			SatSolveResult::Satisfied(value) => {
				let sol = Solution {
					sat: &value,
					state: &self.engine.borrow().state,
				};
				on_sol(sol);
				Status::Satisfied
			}
			SatSolveResult::Unsatisfiable(fail) => {
				on_fail(&fail);
				Status::Unsatisfiable
			}
			SatSolveResult::Unknown => Status::Unknown,
		}
	}
}

#[bon]
impl<Sat: ExternalPropagation> Solver<Sat> {
	/// Method used to add a no-good clause from a solution. This clause can be
	/// used to ensure that the same solution is not found again.
	///
	/// ## Warning
	/// This method will panic if the number of variables and values do not
	/// match.
	#[doc(hidden)]
	pub fn add_no_good(
		&mut self,
		vars: &[AnyView],
		vals: &[Value],
	) -> Result<(), <Self as ReasoningContext>::Conflict> {
		let clause = vars
			.iter()
			.zip_eq(vals)
			.map(|(var, val)| match *var {
				AnyView::Bool(bv) => match val {
					Value::Bool(true) => !bv,
					Value::Bool(false) => bv,
					_ => unreachable!(),
				},
				AnyView::Int(iv) => {
					let Value::Int(val) = val.clone() else {
						unreachable!()
					};
					iv.lit(self, IntLitMeaning::NotEq(val))
				}
			})
			.collect_vec();
		debug!(
			target: "solver",
			clause = ?clause
				.iter()
				.filter_map(|&x| if let BoolView::Lit(x) = x.0 {
					Some(i32::from(x.0))
				} else {
					None
				})
				.collect::<Vec<i32>>(),
			"add solution nogood"
		);
		self.add_clause(clause)
	}

	/// Add a constraint propagator to the solver to enforce a constraint.
	pub(crate) fn add_propagator(&mut self, propagator: BoxedPropagator, from_model: bool) {
		let mut handle = self.engine.borrow_mut();
		let engine = &mut *handle;
		engine.propagators.push(propagator);
		let prop_ref = PropRef::new(engine.propagators.len() - 1);
		let mut ctx = InitializationContext::new(&mut engine.state, prop_ref);
		engine.propagators[prop_ref.index()].initialize(&mut ctx);
		let priority = ctx.priority();
		let enqueue = ctx.enqueue(from_model);
		let new_observed = mem::take(&mut ctx.observed_variables);
		engine.state.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(
			prop_ref.index(),
			engine.state.propagator_queue.info.len() - 1
		);
		if enqueue {
			engine
				.state
				.propagator_queue
				.enqueue_propagator(prop_ref.raw());
		}
		drop(handle);
		for v in new_observed {
			// Ensure that the trail has a space to track the literal
			{
				self.engine.borrow_mut().state.trail.grow_to_boolvar(v);
			}
			// Ensure the SAT solver knows the literal is observed.
			self.sat.add_observed_var(v);
		}
	}

	/// Split the solver into a solving actions object that limits interaction
	/// with the SAT solver, and the dynamic engine reference.
	pub(crate) fn as_parts_mut(&mut self) -> (impl SolvingActions + '_, RefMut<'_, Engine>) {
		struct SA<'a, O>(&'a mut O);
		impl<O: ExternalPropagation> SolvingActions for SA<'_, O> {
			fn is_decision(&mut self, _: RawLit) -> bool {
				false
			}
			fn new_observed_var(&mut self) -> pindakaas::Var {
				self.0.new_observed_var()
			}
			fn phase(&mut self, lit: RawLit) {
				self.0.phase(lit);
			}
			fn unphase(&mut self, lit: RawLit) {
				self.0.unphase(lit);
			}
		}

		(SA(&mut self.sat), self.engine.borrow_mut())
	}

	/// Access the initialization statistics of the [`Solver`] object.
	pub fn init_statistics(&self) -> InitStatistics {
		InitStatistics {
			bool_decisions: self.engine.borrow().state.statistics.eager_literals as usize
				+ self.engine.borrow().state.statistics.lazy_literals as usize,
			int_decisions: self.engine.borrow().state.int_vars.len(),
			propagators: self.engine.borrow().propagators.len(),
		}
	}

	/// Create a new Boolean decision variable in the solver.
	pub fn new_bool_decision(&mut self) -> Decision<bool> {
		let lit = self.sat.new_lit();
		self.engine.borrow_mut().state.statistics.eager_literals += 1;
		Decision(lit)
	}

	/// Create a new integer decision variable with the given `domain`.
	///
	/// Use the optional `order_literals` and `direct_literals` setters to
	/// choose whether order and direct literals are created eagerly or lazily.
	/// Direct literal can only be eager when the order literals are also
	/// eager. Both default to lazy.
	///
	/// Finalize the builder with `.view()` to always get a [`View<IntVal>`], or
	/// with `.decision()` to get a [`Decision<IntVal>`] when the domain has at
	/// least three values.
	#[builder(finish_fn(name = view, doc {
		/// Finalize the builder and return a [`View`] of the new integer decision.
		///
		/// This always succeeds, even for domains with one or two values, which
		/// are represented more compactly than a full integer decision.
	}))]
	pub fn new_int_decision(
		&mut self,
		#[builder(start_fn, into)] domain: IntSet,
		#[builder(default)] mut order_literals: LiteralStrategy,
		#[builder(default)] direct_literals: LiteralStrategy,
		polarity: Option<Polarity>,
	) -> View<IntVal> {
		let orig_domain_len = domain.card();
		assert_ne!(
			orig_domain_len,
			Some(0),
			"Unable to create integer variable empty domain"
		);
		if orig_domain_len == Some(1) {
			return (*domain.min().unwrap()).into();
		}
		let lb = *domain.min().unwrap();
		let ub = *domain.max().unwrap();
		if orig_domain_len == Some(2) {
			let lit = self.new_bool_decision();
			return LinearBoolView::new(NonZero::new(ub - lb).unwrap(), lb, lit).into();
		}
		if (direct_literals, order_literals) == (LiteralStrategy::Eager, LiteralStrategy::Lazy) {
			warn!(
				target: "solver",
				"coercing order_literals to eager because direct_literals is eager"
			);
			order_literals = LiteralStrategy::Eager;
		};

		let mut engine = self.engine.borrow_mut();
		let upper_bound = engine.state.trail.track(ub);
		let order_encoding = match order_literals {
			LiteralStrategy::Eager => {
				let card = orig_domain_len
					.expect("unable to create literals eagerly for domains that exceed usize::MAX");
				engine.state.statistics.eager_literals += (card - 1) as u64;
				OrderStorage::Eager {
					lower_bound: engine.state.trail.track(lb),
					storage: self.sat.new_var_range(card - 1),
				}
			}
			LiteralStrategy::Lazy => {
				OrderStorage::Lazy(LazyOrderStorage::new_in(&mut engine.state.trail))
			}
		};
		let direct_encoding = match direct_literals {
			LiteralStrategy::Eager => {
				let card = orig_domain_len
					.expect("unable to create literals eagerly for domains that exceed usize::MAX");
				engine.state.statistics.eager_literals += (card - 2) as u64;
				DirectStorage::Eager(self.sat.new_var_range(card - 2))
			}
			LiteralStrategy::Lazy => DirectStorage::Lazy(FxHashMap::default()),
		};
		// Drop engine to allow SAT interaction
		drop(engine);

		// Enforce consistency constraints for eager literals
		if let OrderStorage::Eager { storage, .. } = &order_encoding {
			let mut direct_enc_iter = if let DirectStorage::Eager(vars) = &direct_encoding {
				Some(*vars)
			} else {
				None
			}
			.into_iter()
			.flatten();
			for (ord_i, ord_j) in (*storage).tuple_windows() {
				let ord_i: RawLit = ord_i.into(); // x<i
				let ord_j: RawLit = ord_j.into(); // x<j, where j = i + n and n≥1
				self.sat.add_clause([!ord_i, ord_j]).unwrap(); // x<i -> x<(i+n)
				if matches!(direct_encoding, DirectStorage::Eager(_)) {
					let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
					self.sat.add_clause([!eq_i, !ord_i]).unwrap(); // x=i -> x≥i
					self.sat.add_clause([!eq_i, ord_j]).unwrap(); // x=i -> x<(i+n)
					self.sat.add_clause([eq_i, ord_i, !ord_j]).unwrap(); // x≠i -> (x<i \/
					// x≥(i+n))
				}
			}
			debug_assert!(direct_enc_iter.next().is_none());
		}

		// Create the resulting integer variable
		let mut engine = self.engine.borrow_mut();
		engine.state.int_vars.push(IntDecision {
			direct_encoding,
			domain,
			order_encoding,
			upper_bound,
			polarity,
		});
		let iv = Decision((engine.state.int_vars.len() - 1) as u32);
		// Create propagator activation list
		engine.state.int_activation.push(Default::default());
		debug_assert_eq!(
			engine.state.int_vars.len(),
			engine.state.int_activation.len()
		);

		// Setup the boolean to integer mapping
		if let OrderStorage::Eager { storage, .. } = engine.state.int_vars[iv.idx()].order_encoding
		{
			// Apply phase hints to the (eager) order literals according to the
			// polarity. Note that the positive literal represents `x < val`, so a
			// positive polarity (prefer large values) phases the negation.
			match polarity {
				Some(Polarity::Positive) => {
					for l in storage {
						self.sat.phase(!Into::<RawLit>::into(l));
					}
				}
				Some(Polarity::Negative) => {
					for l in storage {
						self.sat.phase(Into::<RawLit>::into(l));
					}
				}
				None => {}
			}
			let mut vars = storage;
			if let DirectStorage::Eager(vars2) = &engine.state.int_vars[iv.idx()].direct_encoding {
				debug_assert_eq!(Into::<i32>::into(vars.end()) + 1, vars2.start().into());
				vars = VarRange::new(vars.start(), vars2.end());
			}
			engine.state.bool_to_int.insert_eager(vars, iv);
			engine
				.state
				.trail
				.grow_to_boolvar(vars.clone().next_back().unwrap());
			for l in vars {
				self.sat.add_observed_var(l);
			}
		}

		iv.into()
	}

	/// Set the overarching search strategy to use during solving.
	pub fn set_search_strategy(&mut self, strategy: SearchStrategy) {
		self.engine.borrow_mut().state.set_search_strategy(strategy);
	}

	/// Access the solver statistics for the search process up to this point.
	pub fn solver_statistics(&self) -> SolverStatistics {
		let cp_stats = &self.engine.borrow().state.statistics;
		SolverStatistics {
			conflicts: cp_stats.conflicts,
			sat_search_directives: cp_stats.sat_search_directives,
			peak_depth: cp_stats.peak_depth,
			cp_propagator_calls: cp_stats.propagations,
			restarts: cp_stats.restarts,
			user_search_directives: cp_stats.user_search_directives,
			eager_literals: cp_stats.eager_literals,
			lazy_literals: cp_stats.lazy_literals,
		}
	}
}

impl<Sat: TerminateCallback> Solver<Sat> {
	/// Set a callback function used to indicate a termination requirement to
	/// the solver.
	///
	/// The solver will periodically call this function and check its return
	/// value during the search. Subsequent calls to this method override the
	/// previously set callback function.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	pub fn set_terminate_callback<F: FnMut() -> TerminationSignal + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		self.sat.set_terminate_callback(cb);
	}
}

impl<Sat: LearnCallback> Solver<Sat> {
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	pub fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Decision<bool>>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		if let Some(mut f) = cb {
			self.sat
				.set_learn_callback(Some(move |clause: &mut dyn Iterator<Item = RawLit>| {
					trace_learned_clause(clause);
					let mut clause = clause.map(Decision);
					f(&mut clause);
				}));
		} else {
			self.sat.set_learn_callback(Some(trace_learned_clause));
		}
	}
}

impl<Sat: ExternalPropagation> BrancherInitActions for Solver<Sat> {
	fn ensure_decidable<T: DefaultView>(&mut self, view: impl Into<View<T>>) {
		let view: View<T> = view.into();
		let any: &dyn Any = &view;
		if let Some(view) = any.downcast_ref::<View<bool>>() {
			match view.0 {
				BoolView::Lit(var) => {
					let var = var.0.var();
					self.engine.borrow_mut().state.trail.grow_to_boolvar(var);
					self.sat.add_observed_var(var);
				}
				BoolView::Const(_) => {}
			}
		} else if let Some(view) = any.downcast_ref::<View<IntVal>>() {
			match view.0 {
				IntView::Bool(LinearBoolView { var, .. }) => {
					let var = var.0.var();
					self.engine.borrow_mut().state.trail.grow_to_boolvar(var);
					self.sat.add_observed_var(var);
				}
				_ => {
					// Nothing has to happened for constants and all literals
					// for integer variables are already marked as
					// observed.
				}
			}
		} else {
			unreachable!()
		}
	}

	fn push_brancher(&mut self, brancher: BoxedBrancher) {
		self.engine.borrow_mut().branchers.push(brancher);
	}
}

impl Clone for Solver<Cadical> {
	fn clone(&self) -> Self {
		let engine: Engine = self.engine.borrow().clone();
		let engine = Rc::new(RefCell::new(engine));
		let sat = self.sat.shallow_clone_with_propagator(Rc::clone(&engine));
		Solver { sat, engine }
	}
}

impl<Sat: ExternalPropagation> ConstructionActions for Solver<Sat> {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		self.engine.borrow_mut().state.trail.track(init)
	}
}

impl<Sat: ExternalPropagation> DecisionActions for Solver<Sat> {
	fn num_conflicts(&self) -> u64 {
		self.engine.borrow().state.statistics.conflicts
	}
}

impl<Sat: Default + ExternalPropagation + LearnCallback> Default for Solver<Sat> {
	fn default() -> Self {
		let mut sat = Sat::default();
		let engine = Rc::default();
		sat.set_learn_callback(Some(trace_learned_clause));
		sat.connect_propagator(Rc::clone(&engine));
		Self { sat, engine }
	}
}

impl<Sat: ExternalPropagation> PostingActions for Solver<Sat> {
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict> {
		Solver::add_clause(self, clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.add_propagator(propagator, false);
	}
}

impl<Sat> ReasoningContext for Solver<Sat> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl<Sat> TrailingActions for Solver<Sat> {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		self.engine.borrow_mut().state.set_trailed(i, v)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		self.engine.borrow().state.trailed(i)
	}
}

impl<'a, Sat, State> SolverNewIntDecisionBuilder<'a, Sat, State>
where
	Sat: ExternalPropagation,
	State: solver_new_int_decision_builder::State,
{
	/// Finalize the builder and return the [`Decision<IntVal>`] for the new
	/// integer variable.
	///
	/// # Panics
	///
	/// Panics if the domain has fewer than three values, because those domains
	/// are represented as constants or linear Boolean views instead of a full
	/// integer decision.
	pub fn decision(self) -> Decision<IntVal>
	where
		State: solver_new_int_decision_builder::IsComplete,
	{
		let IntView::Linear(lin_view) = self.view().0 else {
			panic!("domain did not contain at least three values");
		};
		debug_assert_eq!(lin_view.offset, 0);
		debug_assert_eq!(lin_view.scale.get(), 1);
		lin_view.var
	}
}

impl Add for SolverStatistics {
	type Output = SolverStatistics;

	fn add(mut self, other: SolverStatistics) -> SolverStatistics {
		self += other;
		self
	}
}

impl AddAssign for SolverStatistics {
	fn add_assign(&mut self, other: SolverStatistics) {
		self.conflicts += other.conflicts;
		self.sat_search_directives += other.sat_search_directives;
		self.peak_depth = self.peak_depth.max(other.peak_depth);
		self.cp_propagator_calls += other.cp_propagator_calls;
		self.restarts += other.restarts;
		self.user_search_directives += other.user_search_directives;
		self.eager_literals = self.eager_literals.max(other.eager_literals);
		self.lazy_literals = self.lazy_literals.max(other.lazy_literals);
	}
}
