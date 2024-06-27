pub(crate) mod engine;
pub(crate) mod initialization_context;
pub(crate) mod poster;
pub(crate) mod value;
pub(crate) mod view;

use std::fmt;

use delegate::delegate;
use itertools::Itertools;
use pindakaas::{
	solver::{
		cadical::Cadical, LearnCallback, NextVarRange, PropagatingSolver, PropagatorAccess,
		SlvTermSignal, SolveAssuming, SolveResult as SatSolveResult, Solver as SolverTrait,
		TermCallback,
	},
	Cnf, Lit as RawLit, Valuation as SatValuation,
};
use tracing::debug;

use crate::{
	actions::{explanation::ExplanationActions, inspection::InspectionActions},
	solver::{
		engine::{Engine, PropRef},
		initialization_context::InitializationContext,
		poster::Poster,
		value::{AssumptionChecker, ConstantFailure, Valuation, Value},
		view::{BoolViewInner, IntView, IntViewInner, SolverView},
	},
	BoolView, IntVal, LitMeaning, ReformulationError,
};

pub struct Solver<Sat = Cadical>
where
	Sat: SatSolver,
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) oracle: Sat,
}

impl<Sol, Sat> Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	pub(crate) fn engine(&self) -> &Engine {
		self.oracle.propagator().unwrap()
	}

	pub(crate) fn engine_mut(&mut self) -> &mut Engine {
		self.oracle.propagator_mut().unwrap()
	}

	/// Try and find a solution to the problem for which the Solver was initialized, given a list of
	/// Boolean assumptions.
	pub fn solve_assuming(
		&mut self,
		assumptions: impl IntoIterator<Item = BoolView>,
		mut on_sol: impl FnMut(&dyn Valuation),
		on_fail: impl FnOnce(&dyn AssumptionChecker),
	) -> SolveResult {
		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assumptions
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolViewInner::Lit(lit) => Some(Ok(lit)),
				BoolViewInner::Const(true) => None,
				BoolViewInner::Const(false) => Some(Err(ReformulationError::TrivialUnsatisfiable)),
			})
			.collect()
		else {
			on_fail(&ConstantFailure);
			return SolveResult::Unsatisfiable;
		};

		let status = self.oracle.solve_assuming(
			assumptions,
			|model| {
				let engine: &Engine = model.propagator().unwrap();
				let wrapper: &dyn Valuation = &|x| match x {
					SolverView::Bool(lit) => match lit.0 {
						BoolViewInner::Lit(lit) => model.value(lit).map(Value::Bool),
						BoolViewInner::Const(b) => Some(Value::Bool(b)),
					},
					SolverView::Int(var) => match var.0 {
						IntViewInner::VarRef(iv) => {
							Some(Value::Int(engine.state.int_vars[iv].get_value(model)))
						}
						IntViewInner::Const(i) => Some(Value::Int(i)),
						IntViewInner::Linear {
							transformer: transform,
							var,
						} => {
							let val = engine.state.int_vars[var].get_value(model);
							Some(Value::Int(transform.transform(val)))
						}
						IntViewInner::Bool { transformer, lit } => model
							.value(lit)
							.map(|v| Value::Int(transformer.transform(v as IntVal))),
					},
				};
				on_sol(wrapper);
			},
			|fail_fn| on_fail(fail_fn),
		);
		match status {
			SatSolveResult::Sat => SolveResult::Satisfied,
			SatSolveResult::Unsat => SolveResult::Unsatisfiable,
			SatSolveResult::Unknown => SolveResult::Unknown,
		}
	}

	/// Try and find a solution to the problem for which the Solver was initialized.
	pub fn solve(&mut self, on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		self.solve_assuming([], on_sol, |_| {})
	}

	/// Find all solutions with regard to a list of given variables.
	/// The given closure will be called for each solution found.
	///
	/// WARNING: This method will add additional clauses into the solver to prevent the same solution
	/// from being generated twice. This will make repeated use of the Solver object impossible. Note
	/// that you can clone the Solver object before calling this method to work around this
	/// limitation.
	pub fn all_solutions(
		&mut self,
		vars: &[SolverView],
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> SolveResult {
		let mut num_sol = 0;
		loop {
			let mut vals = Vec::with_capacity(vars.len());
			let status = self.solve(|value| {
				num_sol += 1;
				for v in vars {
					vals.push(value(*v));
				}
				on_sol(value);
			});
			match status {
				SolveResult::Satisfied => {
					let nogood: Vec<RawLit> = vars
						.iter()
						.zip_eq(vals)
						.filter_map(|(var, val)| match var {
							SolverView::Bool(BoolView(BoolViewInner::Lit(l))) => {
								let Value::Bool(val) = val? else {
									unreachable!()
								};
								Some(if val { !l } else { *l })
							}
							SolverView::Int(iv) => {
								let Value::Int(val) = val? else {
									unreachable!()
								};
								match self.engine().state.get_int_lit(*iv, LitMeaning::Eq(val)).0 {
									BoolViewInner::Lit(l) => Some(!l),
									BoolViewInner::Const(true) => None,
									BoolViewInner::Const(false) => unreachable!(),
								}
							}
							_ => None,
						})
						.collect();
					if nogood.is_empty() || self.oracle.add_clause(nogood).is_err() {
						return SolveResult::Complete;
					}
				}
				SolveResult::Unsatisfiable => {
					if num_sol == 0 {
						return SolveResult::Unsatisfiable;
					} else {
						return SolveResult::Complete;
					}
				}
				SolveResult::Unknown => {
					if num_sol == 0 {
						return SolveResult::Unknown;
					} else {
						return SolveResult::Satisfied;
					}
				}
				_ => unreachable!(),
			}
		}
	}

	/// Wrapper function for `all_solutions` that collects all solutions and returns them in a vector
	/// of solution values.
	///
	/// WARNING: This method will add additional clauses into the solver to prevent the same solution
	/// from being generated twice. This will make repeated use of the Solver object impossible. Note
	/// that you can clone the Solver object before calling this method to work around this
	/// limitation.
	pub fn get_all_solutions(&mut self, vars: &[SolverView]) -> (SolveResult, Vec<Vec<Value>>) {
		let mut solutions = Vec::new();
		let status = self.all_solutions(vars, |sol| {
			let mut sol_vec = Vec::with_capacity(vars.len());
			for v in vars {
				sol_vec.push(sol(*v).unwrap());
			}
			solutions.push(sol_vec);
		});
		(status, solutions)
	}

	/// Find an optimal solution with regards to the given objective and goal.
	///
	/// Note that this method uses assumptions iteratively increase the lower bound of the objective.
	/// This does not impact the state of the solver for continued use.œ
	pub fn branch_and_bound(
		&mut self,
		objective: IntView,
		goal: Goal,
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> SolveResult {
		let mut obj_curr = None;
		let obj_best = match goal {
			Goal::Minimize => self.engine().state.get_int_lower_bound(objective),
			Goal::Maximize => self.engine().state.get_int_upper_bound(objective),
		};
		let mut assump = None;
		loop {
			let status = self.solve_assuming(
				assump,
				|value| {
					obj_curr = value(SolverView::Int(objective)).map(|val| {
						if let Value::Int(i) = val {
							i
						} else {
							unreachable!()
						}
					});
					on_sol(value);
				},
				|_| {},
			);
			match status {
				SolveResult::Satisfied => {
					if obj_curr == Some(obj_best) {
						return SolveResult::Complete;
					} else {
						assump = match goal {
							Goal::Minimize => Some(
								self.engine()
									.state
									.get_int_lit(objective, LitMeaning::Less(obj_curr.unwrap())),
							),
							Goal::Maximize => Some(self.engine().state.get_int_lit(
								objective,
								LitMeaning::GreaterEq(obj_curr.unwrap() + 1),
							)),
						};
					}
				}
				SolveResult::Unsatisfiable => {
					return if obj_curr.is_none() {
						SolveResult::Unsatisfiable
					} else {
						SolveResult::Complete
					}
				}
				SolveResult::Unknown => {
					return if obj_curr.is_none() {
						SolveResult::Unknown
					} else {
						SolveResult::Satisfied
					}
				}
				SolveResult::Complete => unreachable!(),
			}
		}
	}

	pub fn num_int_vars(&self) -> usize {
		self.engine().state.int_vars.len()
	}

	pub(crate) fn add_propagator<P: Poster>(&mut self, poster: P) {
		let prop_ref = PropRef::from(self.engine().propagators.len());
		let mut actions = InitializationContext {
			slv: self,
			prop: prop_ref,
		};
		let (prop, enqueue) = poster.post(&mut actions);
		if enqueue {
			let level = prop.queue_priority_level();
			self.engine_mut().state.prop_queue.insert(level, prop_ref);
		}
		let p = self.engine_mut().propagators.push(prop);
		debug_assert_eq!(prop_ref, p);
		let p = self.engine_mut().state.enqueued.push(enqueue);
		debug_assert_eq!(prop_ref, p);
	}

	pub(crate) fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		iter: I,
	) -> Result<(), ReformulationError> {
		let mut clause = Vec::new();
		for lit in iter {
			match lit.0 {
				BoolViewInner::Lit(l) => clause.push(l),
				BoolViewInner::Const(true) => return Ok(()),
				BoolViewInner::Const(false) => (),
			}
		}
		if clause.is_empty() {
			return Err(ReformulationError::TrivialUnsatisfiable);
		}
		self.oracle
			.add_clause(clause)
			.map_err(|_| ReformulationError::TrivialUnsatisfiable)
	}

	pub fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = RawLit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		if let Some(mut f) = cb {
			self.oracle.set_learn_callback(Some(
				move |clause: &mut dyn Iterator<Item = RawLit>| {
					trace_learned_clause(clause);
					f(clause)
				},
			));
		} else {
			self.oracle.set_learn_callback(Some(trace_learned_clause));
		}
	}

	delegate! {
		to self.oracle {
			pub fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>);
		}
	}
}

impl<Sol, Sat> fmt::Debug for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol> + fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Solver")
			.field("oracle", &self.oracle)
			.field("engine", self.engine())
			.finish()
	}
}

impl<Sol, Sat> From<Cnf> for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	fn from(value: Cnf) -> Self {
		let mut core: Sat = value.into();
		core.set_external_propagator(Some(Engine::default()));
		core.set_learn_callback(Some(trace_learned_clause));
		Self { oracle: core }
	}
}

impl<Sol, Sat> Clone for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol> + Clone,
{
	fn clone(&self) -> Self {
		let mut core = self.oracle.clone();
		let engine = self.engine().clone();
		core.set_external_propagator(Some(engine));
		core.set_learn_callback(Some(trace_learned_clause));
		Self { oracle: core }
	}
}

fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

pub trait SatSolver:
	PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>
where
	<Self as SolverTrait>::ValueFn: PropagatorAccess,
{
}
impl<X> SatSolver for X
where
	X: PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>,
	<X as SolverTrait>::ValueFn: PropagatorAccess,
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
	Satisfied,
	Unsatisfiable,
	Complete,
	Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Goal {
	Maximize,
	Minimize,
}
