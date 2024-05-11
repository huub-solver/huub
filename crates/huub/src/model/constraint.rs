use flatzinc_serde::RangeList;
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};

use super::{
	int::IntView,
	reformulate::{ReifContext, VariableMap},
};
use crate::{
	propagator::{
		all_different::AllDifferentValue, element::IntElementBounds, int_lin_le::LinearLE,
		minimum::Minimum,
	},
	solver::SatSolver,
	BoolExpr, IntVal, Model, ReformulationError, Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
	AllDifferent(Vec<IntView>),
	IntLinEq(Vec<IntVal>, Vec<IntView>, IntVal),
	IntLinLessEq(Vec<IntVal>, Vec<IntView>, IntVal),
	Maximum(Vec<IntView>, IntView),
	Minimum(Vec<IntView>, IntView),
	Element(Vec<IntView>, IntView, IntView),
	SimpleBool(BoolExpr),
}

impl Constraint {
	pub(crate) fn to_solver<Sol, Sat>(
		&self,
		slv: &mut Solver<Sat>,
		map: &mut VariableMap,
	) -> Result<(), ReformulationError>
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		match self {
			Constraint::SimpleBool(exp) => exp.constrain(slv, map),
			Constraint::AllDifferent(v) => {
				let vars: Vec<_> = v
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				slv.add_propagator(AllDifferentValue::new(vars));
				Ok(())
			}
			Constraint::IntLinLessEq(coeffs, vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.zip_eq(coeffs.iter())
					.map(|(v, &c)| {
						v.to_arg(
							if c >= 0 {
								ReifContext::Pos
							} else {
								ReifContext::Neg
							},
							slv,
							map,
						)
					})
					.collect();
				slv.add_propagator(LinearLE::new(coeffs, vars, *c));
				Ok(())
			}
			Constraint::IntLinEq(coeffs, vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				// coeffs * vars <= c
				slv.add_propagator(LinearLE::new(coeffs, vars.clone(), *c));
				// coeffs * vars >= c <=>  -coeffs * vars <= -c
				slv.add_propagator(LinearLE::new(
					&coeffs.iter().map(|c| -c).collect_vec(),
					vars,
					-c,
				));
				Ok(())
			}
			Constraint::Minimum(vars, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = y.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(Minimum::new(vars, y));
				Ok(())
			}
			Constraint::Maximum(vars, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| -v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = -y.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(Minimum::new(vars, y));
				Ok(())
			}
			Constraint::Element(vars, idx, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = y.to_arg(ReifContext::Mixed, slv, map);
				let idx = idx.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(IntElementBounds::new(vars, y, idx));
				Ok(())
			}
		}
	}
}

impl Model {
	pub(crate) fn propagate(&mut self, con: usize) -> Result<(), ReformulationError> {
		match self.constraints[con].clone() {
			Constraint::AllDifferent(vars) => {
				let (vals, vars): (Vec<_>, Vec<_>) =
					vars.iter().partition(|v| matches!(v, IntView::Const(_)));
				if vals.is_empty() {
					return Ok(());
				}
				let neg_dom = RangeList::from_iter(vals.iter().map(|i| {
					let IntView::Const(i) = i else { unreachable!() };
					*i..=*i
				}));
				for v in vars {
					self.diff_int_domain(v, &neg_dom, con)?
				}
				Ok(())
			}
			Constraint::Maximum(args, m) => {
				let max_lb = args
					.iter()
					.map(|a| self.get_int_lower_bound(a))
					.max()
					.unwrap();
				let max_ub = args
					.iter()
					.map(|a| self.get_int_upper_bound(a))
					.max()
					.unwrap();
				self.set_int_lower_bound(&m, max_lb, con)?;
				self.set_int_upper_bound(&m, max_ub, con)?;

				let ub = self.get_int_upper_bound(&m);
				for a in args {
					self.set_int_upper_bound(&a, ub, con)?;
				}
				Ok(())
			}
			Constraint::Minimum(args, m) => {
				let min_lb = args
					.iter()
					.map(|a| self.get_int_lower_bound(a))
					.min()
					.unwrap();
				let min_ub = args
					.iter()
					.map(|a| self.get_int_upper_bound(a))
					.min()
					.unwrap();
				self.set_int_lower_bound(&m, min_lb, con)?;
				self.set_int_upper_bound(&m, min_ub, con)?;

				let lb = self.get_int_lower_bound(&m);
				for a in args {
					self.set_int_lower_bound(&a, lb, con)?;
				}
				Ok(())
			}
			Constraint::Element(args, y, idx) => {
				// make sure idx is within the range of args
				self.set_int_lower_bound(&idx, 0, con)?;
				self.set_int_upper_bound(&idx, args.len() as IntVal, con)?;
				let (min_lb, max_ub) =
					args.iter()
						.fold((IntVal::MAX, IntVal::MIN), |(min_lb, max_ub), v| {
							(
								min_lb.min(self.get_int_lower_bound(v)),
								max_ub.max(self.get_int_upper_bound(v)),
							)
						});
				if min_lb > self.get_int_lower_bound(&y) {
					self.set_int_lower_bound(&y, min_lb, con)?;
				}
				if max_ub < self.get_int_upper_bound(&y) {
					self.set_int_upper_bound(&y, max_ub, con)?;
				}
				Ok(())
			}
			_ => Ok(()),
		}
	}

	pub(crate) fn subscribe(&mut self, con: usize) {
		match &self.constraints[con] {
			Constraint::Maximum(args, m) | Constraint::Minimum(args, m) => {
				for a in args {
					if let IntView::Var(a) = a {
						self.int_vars[a.0 as usize].constraints.push(con);
					}
				}
				if let IntView::Var(m) = m {
					self.int_vars[m.0 as usize].constraints.push(con);
				}
			}
			Constraint::Element(args, y, idx) => {
				for a in args {
					if let IntExpr::Var(a) = a {
						self.int_vars[a.0 as usize].constraints.push(con);
					}
				}
				if let IntExpr::Var(y) = y {
					self.int_vars[y.0 as usize].constraints.push(con);
				}
				if let IntExpr::Var(idx) = idx {
					self.int_vars[idx.0 as usize].constraints.push(con);
				}
			}
			_ => {}
		}
	}
}
