pub(crate) mod engine;
pub(crate) mod initialization_context;
pub(crate) mod value;
pub(crate) mod view;

use delegate::delegate;
use pindakaas::{
	solver::{
		cadical::Cadical, LearnCallback, NextVarRange, PropagatingSolver, PropagatorAccess,
		SlvTermSignal, SolveAssuming, SolveResult, Solver as SolverTrait, TermCallback,
	},
	Cnf, Lit as RawLit, Valuation as SatValuation,
};
use tracing::debug;

use self::{
	value::{Valuation, Value},
	view::{BoolViewInner, IntView, SolverView},
};
use crate::{
	propagator::Propagator,
	solver::{
		engine::{Engine, PropRef},
		initialization_context::InitializationContext,
		view::IntViewInner,
	},
};

#[derive(Debug)]
pub struct Solver<Sat: SatSolver = Cadical>
where
	<Sat as SolverTrait>::ValueFn: PropagatorAccess,
{
	pub(crate) oracle: Sat,
}

impl<Sol: PropagatorAccess + SatValuation, Sat: SatSolver + SolverTrait<ValueFn = Sol>>
	Solver<Sat>
{
	pub(crate) fn engine(&self) -> &Engine {
		self.oracle.propagator().unwrap()
	}

	pub(crate) fn engine_mut(&mut self) -> &mut Engine {
		self.oracle.propagator_mut().unwrap()
	}

	pub fn solve(&mut self, mut on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		self.oracle.solve(|model| {
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
					IntViewInner::Linear { var, scale, offset } => {
						Some(Value::Int(IntView::linear_transform(
							engine.state.int_vars[var].get_value(model),
							scale,
							offset,
						)))
					}
				},
			};
			on_sol(wrapper);
		})
	}

	pub fn num_int_vars(&self) -> usize {
		self.engine().state.int_vars.len()
	}

	pub(crate) fn add_propagator(&mut self, mut prop: impl Propagator + 'static) {
		let prop_ref = PropRef::from(self.engine().propagators.len());
		let enqueue = prop.initialize(&mut InitializationContext {
			slv: self,
			prop: prop_ref,
		});
		if enqueue {
			let level = prop.queue_priority_level();
			self.engine_mut().state.prop_queue.insert(level, prop_ref);
		}
		let p = self.engine_mut().propagators.push(Box::new(prop));
		debug_assert_eq!(prop_ref, p);
		let p = self.engine_mut().state.enqueued.push(enqueue);
		debug_assert_eq!(prop_ref, p);
	}

	pub fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = RawLit>)>(
		&mut self,
		cb: Option<F>,
	) {
		if let Some(mut f) = cb {
			let g = move |clause: &mut dyn Iterator<Item = RawLit>| {
				trace_learned_clause(clause);
				f(clause)
			};
			self.oracle.set_learn_callback(Some(Box::new(g)));
		} else {
			self.oracle.set_learn_callback(Some(trace_learned_clause));
		}
	}

	delegate! {
		to self.oracle {
			pub fn set_terminate_callback<F: FnMut() -> SlvTermSignal>(&mut self, cb: Option<F>);
		}
	}
}

impl<Sol: PropagatorAccess + SatValuation, Sat: SatSolver + SolverTrait<ValueFn = Sol>> From<Cnf>
	for Solver<Sat>
{
	fn from(value: Cnf) -> Self {
		let mut core: Sat = value.into();
		let None = core.set_external_propagator(Some(Box::<Engine>::default())) else {
			unreachable!()
		};
		core.set_learn_callback(Some(trace_learned_clause));
		Self { oracle: core }
	}
}

impl<Sol: PropagatorAccess + SatValuation, Sat: SatSolver + SolverTrait<ValueFn = Sol> + Clone>
	Clone for Solver<Sat>
{
	fn clone(&self) -> Self {
		let mut core = self.oracle.clone();
		let engine = self.engine().clone();
		let None = core.set_external_propagator(Some(Box::new(engine))) else {
			unreachable!()
		};
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
