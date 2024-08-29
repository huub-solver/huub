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
use poster::BrancherPoster;
use tracing::{debug, trace};

use crate::{
	actions::{
		decision::DecisionActions, explanation::ExplanationActions, inspection::InspectionActions,
		trailing::TrailingActions,
	},
	solver::{
		engine::{
			int_var::{IntVarRef, LazyLitDef},
			trace_new_lit,
			trail::TrailedInt,
			Engine, PropRef, SearchStatistics,
		},
		initialization_context::{InitRef, InitializationContext},
		poster::Poster,
		value::{AssumptionChecker, ConstantFailure, Valuation, Value},
		view::{BoolViewInner, IntView, IntViewInner, SolverView},
	},
	BoolView, IntVal, LitMeaning, ReformulationError,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SolverConfiguration {
	/// Switch between the activity-based search heuristic and the user-specific search heuristic after each restart.
	///
	/// This option is ignored if [`vsids_only`] is set to `true`.
	toggle_vsids: bool,
	/// Switch to the activity-based search heuristic after the given number of conflicts.
	///
	/// This option is ignored if [`toggle_vsids`] or [`vsids_only`] is set to `true`.
	vsids_after: Option<u32>,
	/// Only use the activity-based search heuristic provided by the SAT solver. Ignore the user-specific search heuristic.
	vsids_only: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Goal {
	Maximize,
	Minimize,
}

/// Statistics related to the initialization of the solver
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InitStatistics {
	// TODO
	// /// Number of (non-view) boolean variables present in the solver
	// bool_vars: usize,
	/// Number of (non-view) integer variables represented in the solver
	int_vars: usize,
	/// Number of propagators in the solver
	propagators: usize,
}

pub trait SatSolver:
	PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>
where
	<Self as SolverTrait>::ValueFn: PropagatorAccess,
{
}

pub struct Solver<Sat = Cadical>
where
	Sat: SatSolver,
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) oracle: Sat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
	Satisfied,
	Unsatisfiable,
	Complete,
	Unknown,
}

fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

impl InitStatistics {
	pub fn int_vars(&self) -> usize {
		self.int_vars
	}
	pub fn propagators(&self) -> usize {
		self.propagators
	}
}

impl<Sol, Sat> Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	pub(crate) fn add_brancher<P: BrancherPoster>(&mut self, poster: P) {
		let mut actions = InitializationContext {
			slv: self,
			init_ref: InitRef::Brancher,
		};
		let brancher = poster.post(&mut actions);
		self.engine_mut().branchers.push(brancher);
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

	pub(crate) fn add_propagator<P: Poster>(&mut self, poster: P) {
		let prop_ref = PropRef::from(self.engine().propagators.len());
		let mut actions = InitializationContext {
			slv: self,
			init_ref: InitRef::Propagator(prop_ref),
		};
		let (prop, queue_pref) = poster.post(&mut actions);
		let p = self.engine_mut().propagators.push(prop);
		debug_assert_eq!(prop_ref, p);
		let engine = self.engine_mut();
		let p = engine.state.propagator_priority.push(queue_pref.priority);
		debug_assert_eq!(prop_ref, p);
		let p = self.engine_mut().state.enqueued.push(false);
		debug_assert_eq!(prop_ref, p);
		if queue_pref.enqueue_on_post {
			self.engine_mut().state.enqueue_propagator(prop_ref);
		}
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
								match self.get_int_lit(*iv, LitMeaning::Eq(val)).0 {
									BoolViewInner::Lit(l) => Some(!l),
									BoolViewInner::Const(true) => None,
									BoolViewInner::Const(false) => unreachable!(),
								}
							}
							_ => None,
						})
						.collect();
					debug!(clause = ?nogood.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add solution nogood");
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

	/// Find an optimal solution with regards to the given objective and goal.
	///
	/// Note that this method uses assumptions iteratively increase the lower bound of the objective.
	/// This does not impact the state of the solver for continued use.
	pub fn branch_and_bound(
		&mut self,
		objective: IntView,
		goal: Goal,
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> SolveResult {
		let mut obj_curr = None;
		let obj_bound = match goal {
			Goal::Minimize => self.get_int_lower_bound(objective),
			Goal::Maximize => self.get_int_upper_bound(objective),
		};
		let mut assump = None;
		debug!(obj_bound, "start branch and bound");
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
			debug!(?status, ?obj_curr, obj_bound, ?goal, "oracle solve result");
			match status {
				SolveResult::Satisfied => {
					if obj_curr == Some(obj_bound) {
						return SolveResult::Complete;
					} else {
						assump = match goal {
							Goal::Minimize => Some(
								self.get_int_lit(objective, LitMeaning::Less(obj_curr.unwrap())),
							),
							Goal::Maximize => Some(self.get_int_lit(
								objective,
								LitMeaning::GreaterEq(obj_curr.unwrap() + 1),
							)),
						};
						debug!(
							lit = i32::from({
								let BoolViewInner::Lit(l) = assump.unwrap().0 else {
									unreachable!()
								};
								l
							}),
							"add objective bound"
						)
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

	pub(crate) fn engine(&self) -> &Engine {
		self.oracle.propagator().unwrap()
	}

	pub(crate) fn engine_mut(&mut self) -> &mut Engine {
		self.oracle.propagator_mut().unwrap()
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

	pub fn init_statistics(&self) -> InitStatistics {
		InitStatistics {
			int_vars: self.engine().state.int_vars.len(),
			propagators: self.engine().propagators.len(),
		}
	}

	pub fn search_statistics(&self) -> &SearchStatistics {
		&self.engine().state.statistics
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
		to self.engine_mut().state {
			pub fn set_vsids_after(&mut self, conflicts: Option<u32>);
			pub fn set_vsids_only(&mut self, enable: bool);
			pub fn set_toggle_vsids(&mut self, enable: bool);
		}
	}

	/// Try and find a solution to the problem for which the Solver was initialized.
	pub fn solve(&mut self, on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		self.solve_assuming([], on_sol, |_| {})
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
}

impl<Slv> SatSolver for Slv
where
	Slv:
		PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>,
	<Slv as SolverTrait>::ValueFn: PropagatorAccess,
{
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

impl<Sol, Sat> DecisionActions for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: LitMeaning) -> BoolView {
		// TODO: We currently copy the integer variable struct here to avoid
		// borrowing issues. Hopefully the compiler sees that this is unnecessary,
		// but we should check and see if we can avoid this.
		let mut var = self.engine_mut().state.int_vars[iv].clone();
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = self.oracle.new_var();
			trace_new_lit!(iv, def, v);
			self.oracle.add_observed_var(v);
			self.engine_mut()
				.state
				.bool_to_int
				.insert_lazy(v, iv, def.meaning.clone());
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				trace!(clause = ?cl.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add clause");
				self.oracle.add_clause(cl).unwrap();
			}
			v
		};
		let bv = var.bool_lit(meaning, new_var);
		self.engine_mut().state.int_vars[iv] = var;
		bv
	}
}

impl<Sol, Sat> ExplanationActions for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.engine().state {
			fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
		}
		to self.engine_mut().state {
			fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
			fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
			fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning);
		}
	}

	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		let val = self.get_int_val(var)?;
		Some(self.get_int_lit(var, LitMeaning::Eq(val)))
	}
}

impl<Sol, Sat> InspectionActions for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl<Sol, Sat> TrailingActions for Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	delegate! {
		to self.engine().state {
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
		}
		to self.engine_mut().state {
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}
