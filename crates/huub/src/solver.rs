pub(crate) mod engine;
pub(crate) mod value;
pub(crate) mod view;

use pindakaas::{
	solver::{
		cadical::Cadical, LearnCallback, NextVarRange, PropagatingSolver, SolveAssuming,
		SolveResult, TermCallback,
	},
	Cnf, Lit as RawLit,
};
use tracing::debug;

use self::view::BoolViewInner;
pub use crate::solver::{
	engine::int_var::LitMeaning,
	value::{IntVal, Valuation, Value},
	view::{BoolView, IntView, SolverView},
};
use crate::{
	propagator::{init_action::InitializationActions, Initialize, Propagator},
	solver::{
		engine::{Engine, PropRef},
		view::IntViewInner,
	},
};

#[derive(Debug)]
pub struct Solver<Sat: SatSolver = Cadical> {
	pub(crate) core: Sat,
}

impl<Sat: SatSolver> Solver<Sat> {
	pub(crate) fn engine(&self) -> &Engine {
		self.core.propagator().unwrap()
	}

	pub(crate) fn engine_mut(&mut self) -> &mut Engine {
		self.core.propagator_mut().unwrap()
	}

	pub fn solve(&mut self, mut on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		// TODO: This is bad, but we cannot access propagator in the value function.
		// If we could, then we could (hopefully) just access the current domain
		let int_vars = self.engine().int_vars.clone();

		self.core.solve(|sat_value| {
			let wrapper: &dyn Valuation = &|x| match x {
				SolverView::Bool(lit) => match lit.0 {
					BoolViewInner::Lit(lit) => sat_value(lit).map(Value::Bool),
					BoolViewInner::Const(b) => Some(Value::Bool(b)),
				},
				SolverView::Int(var) => match var.0 {
					IntViewInner::VarRef(iv) => Some(Value::Int(int_vars[iv].get_value(sat_value))),
					IntViewInner::Const(i) => Some(Value::Int(i)),
				},
			};
			on_sol(wrapper);
		})
	}

	pub fn num_int_vars(&self) -> usize {
		self.engine().int_vars.len()
	}
}

impl<Sat: SatSolver + From<Cnf>> From<Cnf> for Solver<Sat> {
	fn from(value: Cnf) -> Self {
		let mut core: Sat = value.into();
		let None = core.set_external_propagator(Some(Box::<Engine>::default())) else {
			unreachable!()
		};
		core.set_learn_callback(Some(learn_clause_cb));
		Self { core }
	}
}

fn learn_clause_cb(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

impl<Sat: SatSolver> Solver<Sat> {
	pub(crate) fn add_propagator(&mut self, mut prop: impl Propagator + Initialize + 'static) {
		let prop_ref = PropRef::from(self.engine().propagators.len());
		let mut actions = InitializationActions {
			prop_ref,
			slv: self,
		};
		let enqueue = prop.initialize(&mut actions);
		if enqueue {
			let level = prop.queue_priority_level();
			self.engine_mut().prop_queue.insert(level, prop_ref);
		}
		let p = self.engine_mut().propagators.push(Box::new(prop));
		debug_assert_eq!(prop_ref, p);
		let p = self.engine_mut().enqueued.push(enqueue);
		debug_assert_eq!(prop_ref, p);
	}
}

pub trait SatSolver:
	PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>
{
}
impl<
		X: PropagatingSolver + TermCallback + LearnCallback + SolveAssuming + NextVarRange + From<Cnf>,
	> SatSolver for X
{
}
