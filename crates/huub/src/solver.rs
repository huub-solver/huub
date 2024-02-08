mod propagation_layer;

use pindakaas::solver::{
	cadical::Cadical, LearnCallback, PropagatingSolver, SolveAssuming, TermCallback,
};

pub use self::propagation_layer::PropagationLayer;
use crate::{BoolVar, Literal};

pub struct Solver<Sat = Cadical> {
	pub(crate) engine: Sat,
}

impl<S: SatSolver> Solver<S> {
	pub(crate) fn propagation_layer(&self) -> &PropagationLayer {
		self.engine.propagator().unwrap()
	}

	pub(crate) fn propagation_layer_mut(&mut self) -> &mut PropagationLayer {
		self.engine.propagator_mut().unwrap()
	}

	pub fn solve(&mut self, mut on_sol: impl FnMut(&dyn Valuation)) {
		self.engine.solve(|sat_value| {
			let wrapper: &dyn Valuation = &|x| match x {
				Variable::Bool(x) => {
					let lit: Literal = x.into();
					sat_value(lit.0).map(Value::Bool)
				}
			};
			on_sol(wrapper);
		});
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Variable {
	Bool(BoolVar),
}
impl From<BoolVar> for Variable {
	fn from(value: BoolVar) -> Self {
		Self::Bool(value)
	}
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Value {
	Bool(bool),
}

pub trait Valuation: Fn(Variable) -> Option<Value> {}
impl<F: Fn(Variable) -> Option<Value>> Valuation for F {}
pub trait SatSolver: PropagatingSolver + TermCallback + LearnCallback + SolveAssuming {}
impl<X: PropagatingSolver + TermCallback + LearnCallback + SolveAssuming> SatSolver for X {}
