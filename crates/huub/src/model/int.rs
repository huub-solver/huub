use std::ops::{Add, Mul, Neg};

use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	ClauseDatabase, Valuation as SatValuation,
};
use rangelist::{IntervalIterator, RangeList};

use crate::{
	helpers::linear_transform::LinearTransform,
	model::{bool::BoolView, reformulate::VariableMap},
	solver::{view, SatSolver},
	IntVal, Model, NonZeroIntVal, ReformulationError, Solver,
};

impl IntView {
	pub(crate) fn to_arg<Sol, Sat>(
		&self,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> view::IntView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		map.get_int(slv, self)
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntVar(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct IntVarDef {
	pub(crate) domain: RangeList<IntVal>,
	pub(crate) constraints: Vec<usize>,
}

impl IntVarDef {
	pub(crate) fn with_domain(dom: RangeList<IntVal>) -> Self {
		Self {
			domain: dom,
			constraints: Vec::new(),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntView {
	Var(IntVar),
	Const(i64),
	Linear(LinearTransform, IntVar),
	Bool(LinearTransform, BoolView),
}

impl Add<IntVal> for IntView {
	type Output = Self;
	fn add(self, rhs: IntVal) -> Self::Output {
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::offset(rhs), x),
			Self::Const(v) => Self::Const(v + rhs),
			Self::Linear(t, x) => Self::Linear(t + rhs, x),
			Self::Bool(t, x) => Self::Bool(t + rhs, x),
		}
	}
}

impl Mul<NonZeroIntVal> for IntView {
	type Output = Self;
	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::scaled(rhs), x),
			Self::Const(v) => Self::Const(v * rhs.get()),
			Self::Linear(t, x) => Self::Linear(t * rhs, x),
			Self::Bool(t, x) => Self::Bool(t * rhs, x),
		}
	}
}

impl Mul<IntVal> for IntView {
	type Output = Self;
	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			Self::Const(0)
		} else {
			self.mul(NonZeroIntVal::new(rhs).unwrap())
		}
	}
}

impl Neg for IntView {
	type Output = Self;
	fn neg(self) -> Self::Output {
		match self {
			Self::Var(x) => {
				Self::Linear(LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()), x)
			}
			Self::Const(v) => Self::Const(-v),
			Self::Linear(t, x) => Self::Linear(-t, x),
			Self::Bool(t, x) => Self::Bool(-t, x),
		}
	}
}

impl From<BoolView> for IntView {
	fn from(value: BoolView) -> Self {
		match value {
			BoolView::Const(b) => Self::Const(b as IntVal),
			x => Self::Bool(LinearTransform::offset(0), x),
		}
	}
}

impl Model {
	pub(crate) fn get_int_lower_bound(&self, iv: &IntView) -> IntVal {
		match *iv {
			IntView::Var(v) => {
				let def = &self.int_vars[v.0 as usize];
				*def.domain.lower_bound().unwrap()
			}
			IntView::Const(v) => v,
			IntView::Linear(t, v) => {
				let def = &self.int_vars[v.0 as usize];
				if t.positive_scale() {
					t.transform(*def.domain.lower_bound().unwrap())
				} else {
					t.transform(*def.domain.upper_bound().unwrap())
				}
			}
			IntView::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(0)
				} else {
					t.transform(1)
				}
			}
		}
	}

	pub(crate) fn get_int_upper_bound(&self, iv: &IntView) -> IntVal {
		match *iv {
			IntView::Var(v) => {
				let def = &self.int_vars[v.0 as usize];
				*def.domain.upper_bound().unwrap()
			}
			IntView::Const(v) => v,
			IntView::Linear(t, v) => {
				let def = &self.int_vars[v.0 as usize];
				if t.positive_scale() {
					t.transform(*def.domain.upper_bound().unwrap())
				} else {
					t.transform(*def.domain.lower_bound().unwrap())
				}
			}
			IntView::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(1)
				} else {
					t.transform(0)
				}
			}
		}
	}

	pub(crate) fn set_int_lower_bound(
		&mut self,
		iv: &IntView,
		lb: IntVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let def = &mut self.int_vars[v.0 as usize];
				if lb <= *def.domain.lower_bound().unwrap() {
					return Ok(());
				} else if lb > *def.domain.upper_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if *r.end() < lb {
						None
					} else if *r.start() < lb {
						Some(lb..=*r.end())
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if *v < lb {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(t, x) => {
				let def = &mut self.int_vars[x.0 as usize];
				if t.positive_scale() {
					let new_lb = t.rev_transform(lb);
					if new_lb > *def.domain.upper_bound().unwrap() {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_lb <= *def.domain.lower_bound().unwrap() {
						return Ok(());
					}
					def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
						if *r.end() < new_lb {
							None
						} else if *r.start() < new_lb {
							Some(new_lb..=*r.end())
						} else {
							Some(r)
						}
					}));
					let constraints = def.constraints.clone();
					for c in constraints {
						if c != con {
							self.enqueue(c);
						}
					}
					Ok(())
				} else {
					let new_ub = t.rev_transform(lb);
					if new_ub < *def.domain.lower_bound().unwrap() {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_ub >= *def.domain.upper_bound().unwrap() {
						return Ok(());
					}
					def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
						if *r.end() < new_ub {
							None
						} else if *r.start() < new_ub {
							Some(*r.start()..=new_ub)
						} else {
							Some(r)
						}
					}));
					let constraints = def.constraints.clone();
					for c in constraints {
						if c != con {
							self.enqueue(c);
						}
					}
					Ok(())
				}
			}
			IntView::Bool(t, b) => {
				if t.positive_scale() {
					let new_lb = t.rev_transform(lb);
					if new_lb > 1 {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_lb > 0 {
						if let BoolView::Lit(l) = b.clone() {
							let _ = self.add_clause(vec![l]);
						} else {
							todo!()
						}
					}
					Ok(())
				} else {
					let new_ub = t.rev_transform(lb);
					if new_ub < 0 {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_ub < 1 {
						if let BoolView::Lit(l) = b {
							let _ = self.add_clause(vec![!l]);
						} else {
							todo!()
						}
					}
					Ok(())
				}
			}
		}
	}

	pub(crate) fn set_int_upper_bound(
		&mut self,
		iv: &IntView,
		ub: IntVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let def = &mut self.int_vars[v.0 as usize];
				if ub >= *def.domain.upper_bound().unwrap() {
					return Ok(());
				} else if ub < *def.domain.lower_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if ub < *r.start() {
						None
					} else if ub < *r.end() {
						Some(*r.start()..=ub)
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if *v > ub {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(t, x) => {
				let def = &mut self.int_vars[x.0 as usize];
				if t.positive_scale() {
					let new_ub = t.rev_transform(ub);
					if new_ub < *def.domain.lower_bound().unwrap() {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_ub >= *def.domain.upper_bound().unwrap() {
						return Ok(());
					}
					def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
						if new_ub < *r.start() {
							None
						} else if new_ub < *r.end() {
							Some(*r.start()..=new_ub)
						} else {
							Some(r)
						}
					}));
					let constraints = def.constraints.clone();
					for c in constraints {
						if c != con {
							self.enqueue(c);
						}
					}
					Ok(())
				} else {
					let new_lb = t.rev_transform(ub);
					if new_lb > *def.domain.upper_bound().unwrap() {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_lb <= *def.domain.lower_bound().unwrap() {
						return Ok(());
					}
					def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
						if new_lb > *r.end() {
							None
						} else if new_lb > *r.start() {
							Some(new_lb..=*r.end())
						} else {
							Some(r)
						}
					}));
					let constraints = def.constraints.clone();
					for c in constraints {
						if c != con {
							self.enqueue(c);
						}
					}
					Ok(())
				}
			}
			IntView::Bool(t, b) => {
				if t.positive_scale() {
					let new_ub = t.rev_transform(ub);
					if new_ub < 0 {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_ub < 1 {
						if let BoolView::Lit(l) = b.clone() {
							let _ = self.add_clause(vec![!l]);
						} else {
							todo!()
						}
					}
					Ok(())
				} else {
					let new_lb = t.rev_transform(ub);
					if new_lb > 1 {
						return Err(ReformulationError::TrivialUnsatisfiable);
					} else if new_lb > 0 {
						if let BoolView::Lit(l) = b.clone() {
							let _ = self.add_clause(vec![l]);
						} else {
							todo!()
						}
					}
					Ok(())
				}
			}
		}
	}

	pub(crate) fn diff_int_domain(
		&mut self,
		iv: &IntView,
		mask: &RangeList<IntVal>,
		con: usize,
	) -> Result<(), ReformulationError> {
		match *iv {
			IntView::Var(v) => {
				let diff: RangeList<_> = self.int_vars[v.0 as usize].domain.diff(mask);
				if diff.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v.0 as usize].domain == diff {
					return Ok(());
				}
				self.int_vars[v.0 as usize].domain = diff;
				let constraints = self.int_vars[v.0 as usize].constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if mask.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(_, _) => todo!(),
			IntView::Bool(_, _) => todo!(),
		}
	}

	pub(crate) fn intersect_int_domain(
		&mut self,
		iv: &IntView,
		mask: &RangeList<IntVal>,
		con: usize,
	) -> Result<(), ReformulationError> {
		match *iv {
			IntView::Var(v) => {
				let intersect: RangeList<_> = self.int_vars[v.0 as usize].domain.intersect(mask);
				if intersect.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v.0 as usize].domain == intersect {
					return Ok(());
				}
				self.int_vars[v.0 as usize].domain = intersect;
				let constraints = self.int_vars[v.0 as usize].constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if !mask.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(_, _) => todo!(),
			IntView::Bool(_, _) => todo!(),
		}
	}
}
