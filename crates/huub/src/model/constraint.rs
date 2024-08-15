use std::iter::once;

use itertools::Itertools;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};
use rangelist::RangeList;

use crate::{
	actions::{explanation::ExplanationActions, inspection::InspectionActions},
	helpers::{div_ceil, div_floor},
	model::{
		bool::BoolView,
		int::IntView,
		reformulate::{ReifContext, VariableMap},
	},
	propagator::{
		all_different_int::AllDifferentIntValue,
		array_int_minimum::ArrayIntMinimumBounds,
		array_var_int_element::ArrayVarIntElementBounds,
		disjunctive::DisjunctiveEdgeFinding,
		int_lin_le::{IntLinearLessEqBounds, IntLinearLessEqImpBounds},
		int_lin_ne::{IntLinearNotEqImpValue, IntLinearNotEqValue},
		int_pow::IntPowBounds,
		int_times::IntTimesBounds,
	},
	solver::{
		view::{BoolViewInner, IntViewInner},
		SatSolver,
	},
	BoolExpr, IntSetVal, IntVal, LitMeaning, Model, NonZeroIntVal, ReformulationError, Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
	AllDifferentInt(Vec<IntView>),
	Disjunctive(Vec<IntView>, Vec<IntVal>),
	ArrayIntElement(Vec<IntVal>, IntView, IntView),
	ArrayIntMaximum(Vec<IntView>, IntView),
	ArrayIntMinimum(Vec<IntView>, IntView),
	ArrayVarBoolElement(Vec<BoolExpr>, IntView, BoolExpr),
	ArrayVarIntElement(Vec<IntView>, IntView, IntView),
	IntLinEq(Vec<IntView>, IntVal),
	IntLinEqImp(Vec<IntView>, IntVal, BoolExpr),
	IntLinEqReif(Vec<IntView>, IntVal, BoolExpr),
	IntLinLessEq(Vec<IntView>, IntVal),
	IntLinLessEqImp(Vec<IntView>, IntVal, BoolExpr),
	IntLinLessEqReif(Vec<IntView>, IntVal, BoolExpr),
	IntLinNotEq(Vec<IntView>, IntVal),
	IntLinNotEqImp(Vec<IntView>, IntVal, BoolExpr),
	IntLinNotEqReif(Vec<IntView>, IntVal, BoolExpr),
	IntPow(IntView, IntView, IntView),
	IntTimes(IntView, IntView, IntView),
	PropLogic(BoolExpr),
	SetInReif(IntView, IntSetVal, BoolExpr),
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
			Constraint::AllDifferentInt(v) => {
				let vars: Vec<_> = v
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				slv.add_propagator(AllDifferentIntValue::prepare(vars));
				Ok(())
			}
			Constraint::Disjunctive(v, d) => {
				let vars: Vec<_> = v
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let durs = d
					.iter()
					.map(|d| {
						assert!(
							*d >= 0,
							"duration of tasks in disjunctive constraint must be non-negative"
						);
						*d
					})
					.collect_vec();
				// Add propagator for lower bound propagation
				slv.add_propagator(DisjunctiveEdgeFinding::prepare(vars.clone(), durs.clone()));

				// Add symmetric propagator for upper bound propagation
				let horizon = vars
					.iter()
					.zip(durs.iter())
					.map(|(v, d)| slv.engine().state.get_int_upper_bound(*v) + d)
					.max()
					.unwrap();
				let symmetric_vars = vars
					.iter()
					.zip(durs.iter())
					.map(|(v, d)| -*v + (horizon - d));
				slv.add_propagator(DisjunctiveEdgeFinding::prepare(
					symmetric_vars,
					durs.clone(),
				));
				Ok(())
			}
			Constraint::ArrayIntElement(arr, idx, y) => {
				let idx = idx.to_arg(ReifContext::Mixed, slv, map);
				let y = y.to_arg(ReifContext::Mixed, slv, map);

				let idx_map = arr
					.iter()
					.enumerate()
					.map(|(i, v)| (*v, (i + 1) as IntVal))
					.into_group_map();

				for (val, idxs) in idx_map {
					let val_eq = slv.get_int_lit(y, LitMeaning::Eq(val));
					let idxs: Vec<_> = idxs
						.into_iter()
						.map(|i| slv.get_int_lit(idx, LitMeaning::Eq(i)))
						.collect();

					for i in idxs.iter() {
						// (idx = i) -> (val = arr[i])
						slv.add_clause([!i, val_eq])?;
					}
					// (idx not in idxs) -> (val != arr[i])
					slv.add_clause(idxs.into_iter().chain(once(!val_eq)))?
				}
				Ok(())
			}
			Constraint::ArrayIntMinimum(vars, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = y.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(ArrayIntMinimumBounds::prepare(vars, y));
				Ok(())
			}
			Constraint::ArrayIntMaximum(vars, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| -v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = -y.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(ArrayIntMinimumBounds::prepare(vars, y));
				Ok(())
			}
			Constraint::ArrayVarIntElement(vars, idx, y) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let y = y.to_arg(ReifContext::Mixed, slv, map);
				let idx = idx.to_arg(ReifContext::Mixed, slv, map);
				// tranform 1-based index into 0-based index array
				slv.add_propagator(ArrayVarIntElementBounds::prepare(vars, y, idx + (-1)));
				Ok(())
			}
			Constraint::ArrayVarBoolElement(vars, idx, y) => {
				let idx = idx.to_arg(ReifContext::Mixed, slv, map);
				// If the index is already fixed, implement simple equivalence
				if let IntViewInner::Const(idx) = idx.0 {
					let idx = idx as usize;
					return BoolExpr::Equiv(vec![vars[idx - 1].clone(), y.clone()])
						.constrain(slv, map);
				}

				// Evaluate result literal
				let y = y.to_arg(ReifContext::Mixed, slv, map, None)?;
				let arr: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map, None))
					.try_collect()?;

				for (i, l) in arr.iter().enumerate() {
					// Evaluate array literal
					let idx_eq = slv.get_int_lit(idx, LitMeaning::Eq((i + 1) as IntVal));
					// add clause (idx = i + 1 /\ arr[i]) => val
					slv.add_clause([!idx_eq, !l, y])?;
					// add clause (idx = i + 1 /\ !arr[i]) => !val
					slv.add_clause([!idx_eq, *l, !y])?
				}

				// add clause (arr[1] /\ arr[2] /\ ... /\ arr[n]) => val
				slv.add_clause(arr.iter().map(|l| !l).chain(once(y)))?;
				// add clause (!arr[1] /\ !arr[2] /\ ... /\ !arr[n]) => !val
				slv.add_clause(arr.into_iter().chain(once(!y)))?;
				Ok(())
			}
			Constraint::IntLinEq(vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				// coeffs * vars <= c
				slv.add_propagator(IntLinearLessEqBounds::prepare(vars.clone(), *c));
				// coeffs * vars >= c <=> -coeffs * vars <= -c
				slv.add_propagator(IntLinearLessEqBounds::prepare(
					vars.into_iter().map(|v| -v),
					-c,
				));
				Ok(())
			}
			Constraint::IntLinEqImp(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Neg, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(vars.clone(), *c));
						slv.add_propagator(IntLinearLessEqBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c,
						));
					}
					BoolViewInner::Const(false) => {}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(vars.clone(), *c, r));
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c,
							r,
						));
					}
				}
				Ok(())
			}
			Constraint::IntLinEqReif(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Mixed, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(vars.clone(), *c));
						slv.add_propagator(IntLinearLessEqBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c,
						));
					}
					BoolViewInner::Const(false) => {
						slv.add_propagator(IntLinearNotEqValue::prepare(vars, *c));
					}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(vars.clone(), *c, r));
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(
							vars.iter().map(|v| -(*v)),
							-c,
							r,
						));
						slv.add_propagator(IntLinearNotEqImpValue::prepare(vars, *c, !r));
					}
				}
				Ok(())
			}
			Constraint::IntLinLessEq(vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Pos, slv, map))
					.collect();
				slv.add_propagator(IntLinearLessEqBounds::prepare(vars, *c));
				Ok(())
			}
			Constraint::IntLinLessEqImp(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Neg, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(vars, *c));
					}
					BoolViewInner::Const(false) => {}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(vars, *c, r));
					}
				}
				Ok(())
			}
			Constraint::IntLinLessEqReif(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Mixed, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(vars, *c));
					}
					BoolViewInner::Const(false) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c + 1,
						));
					}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(vars.clone(), *c, r));
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c + 1,
							!r,
						));
					}
				}
				Ok(())
			}
			Constraint::IntLinNotEq(vars, c) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Pos, slv, map))
					.collect();
				slv.add_propagator(IntLinearNotEqValue::prepare(vars, *c));
				Ok(())
			}
			Constraint::IntLinNotEqImp(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Neg, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearNotEqValue::prepare(vars, *c));
					}
					BoolViewInner::Const(false) => {}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearNotEqImpValue::prepare(vars, *c, r));
					}
				}
				Ok(())
			}
			Constraint::IntLinNotEqReif(vars, c, r) => {
				let vars: Vec<_> = vars
					.iter()
					.map(|v| v.to_arg(ReifContext::Mixed, slv, map))
					.collect();
				let r = r.to_arg(ReifContext::Mixed, slv, map, None)?;
				match r.0 {
					BoolViewInner::Const(true) => {
						slv.add_propagator(IntLinearNotEqValue::prepare(vars, *c));
					}
					BoolViewInner::Const(false) => {
						slv.add_propagator(IntLinearLessEqBounds::prepare(vars.clone(), *c));
						slv.add_propagator(IntLinearLessEqBounds::prepare(
							vars.into_iter().map(|v| -v),
							-c,
						));
					}
					BoolViewInner::Lit(r) => {
						slv.add_propagator(IntLinearNotEqImpValue::prepare(vars.clone(), *c, r));
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(vars.clone(), *c, !r));
						slv.add_propagator(IntLinearLessEqImpBounds::prepare(
							vars.iter().map(|v| -(*v)),
							-c,
							!r,
						));
					}
				}
				Ok(())
			}
			Constraint::IntPow(base, exponent, res) => {
				let base = base.to_arg(ReifContext::Mixed, slv, map);
				let exponent = exponent.to_arg(ReifContext::Mixed, slv, map);
				let result = res.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(IntPowBounds::prepare(base, exponent, result));
				Ok(())
			}
			Constraint::IntTimes(x, y, z) => {
				let x = x.to_arg(ReifContext::Mixed, slv, map);
				let y = y.to_arg(ReifContext::Mixed, slv, map);
				let z = z.to_arg(ReifContext::Mixed, slv, map);
				slv.add_propagator(IntTimesBounds::prepare(x, y, z));
				Ok(())
			}
			Constraint::PropLogic(exp) => exp.constrain(slv, map),
			Constraint::SetInReif(x, s, r) => {
				if s.iter().len() == 1 {
					let lb = *s.lower_bound().unwrap();
					let ub = *s.upper_bound().unwrap();
					BoolExpr::Equiv(vec![
						BoolExpr::And(vec![
							BoolView::IntGreaterEq(Box::from(x.clone()), lb).into(),
							BoolView::IntLessEq(Box::from(x.clone()), ub).into(),
						]),
						r.clone(),
					])
					.constrain(slv, map)
				} else {
					let eq_lits = s
						.iter()
						.flatten()
						.map(|v| BoolView::IntEq(Box::new(x.clone()), v).into())
						.collect();
					BoolExpr::Equiv(vec![r.clone(), BoolExpr::Or(eq_lits)]).constrain(slv, map)
				}
			}
		}
	}
}

impl Model {
	pub(crate) fn propagate(&mut self, con: usize) -> Result<(), ReformulationError> {
		let simplified = match self.constraints[con].clone() {
			Constraint::AllDifferentInt(vars) => {
				let (vals, vars): (Vec<_>, Vec<_>) = vars
					.into_iter()
					.partition(|v| matches!(v, IntView::Const(_)));
				if vals.is_empty() {
					return Ok(());
				}
				let neg_dom = RangeList::from_iter(vals.iter().map(|i| {
					let IntView::Const(i) = i else { unreachable!() };
					*i..=*i
				}));
				for v in &vars {
					self.diff_int_domain(v, &neg_dom, con)?
				}
				Some(Constraint::AllDifferentInt(vars))
			}
			Constraint::Disjunctive(starts, durations) => {
				// return trivialunsatisfiable if overload is detected
				let (earliest_start, latest_completion) =
					starts.iter().zip(durations.clone()).fold(
						(IntVal::MAX, IntVal::MIN),
						|(earliest_start, latest_completion), (start, duration)| {
							(
								i64::min(
									earliest_start.min(self.get_int_lower_bound(start)),
									earliest_start,
								),
								i64::max(
									latest_completion
										.max(self.get_int_upper_bound(start) + duration),
									latest_completion,
								),
							)
						},
					);
				let total_duration = durations.iter().sum::<IntVal>();
				if earliest_start + total_duration > latest_completion {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				Some(Constraint::Disjunctive(starts, durations))
			}
			Constraint::ArrayIntMaximum(args, m) => {
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
				for a in &args {
					self.set_int_upper_bound(a, ub, con)?;
				}
				Some(Constraint::ArrayIntMaximum(args, m))
			}
			Constraint::ArrayIntMinimum(args, m) => {
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
				for a in &args {
					self.set_int_lower_bound(a, lb, con)?;
				}
				Some(Constraint::ArrayIntMinimum(args, m))
			}
			Constraint::ArrayVarIntElement(args, idx, y) => {
				// make sure idx is within the range of args
				self.set_int_lower_bound(&idx, 1, con)?;
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
				Some(Constraint::ArrayVarIntElement(args, idx, y))
			}
			Constraint::IntLinLessEq(args, cons) => {
				let sum = args
					.iter()
					.map(|v| self.get_int_lower_bound(v))
					.fold(cons, |sum, val| sum - val);

				for v in &args {
					let ub = sum + self.get_int_lower_bound(v);
					self.set_int_upper_bound(v, ub, con)?
				}
				Some(Constraint::IntLinLessEq(args, cons))
			}
			Constraint::IntTimes(x, y, z) => {
				let x_lb = self.get_int_lower_bound(&x);
				let x_ub = self.get_int_upper_bound(&x);
				let y_lb = self.get_int_lower_bound(&y);
				let y_ub = self.get_int_upper_bound(&y);
				let z_lb = self.get_int_lower_bound(&z);
				let z_ub = self.get_int_upper_bound(&z);

				let bounds = [x_lb * y_lb, x_lb * y_ub, x_ub * y_lb, x_ub * y_ub];
				self.set_int_lower_bound(&z, *bounds.iter().min().unwrap(), con)?;
				self.set_int_upper_bound(&z, *bounds.iter().max().unwrap(), con)?;

				if y_lb > 0 || y_ub < 0 {
					let bounds = [(z_lb, y_lb), (z_lb, y_ub), (z_ub, y_lb), (z_ub, y_ub)];
					let min = bounds
						.iter()
						.filter_map(|(z, y)| {
							let y = NonZeroIntVal::new(*y)?;
							Some(div_ceil(*z, y))
						})
						.min()
						.unwrap();
					self.set_int_lower_bound(&x, min, con)?;

					let max = bounds
						.iter()
						.filter_map(|(z, y)| {
							let y = NonZeroIntVal::new(*y)?;
							Some(div_floor(*z, y))
						})
						.max()
						.unwrap();
					self.set_int_upper_bound(&x, max, con)?;
				}

				if x_lb > 0 || x_ub < 0 {
					let bounds = [(z_lb, x_lb), (z_lb, x_ub), (z_ub, x_lb), (z_ub, x_ub)];
					let min = bounds
						.iter()
						.filter_map(|(z, x)| {
							let x = NonZeroIntVal::new(*x)?;
							Some(div_ceil(*z, x))
						})
						.min()
						.unwrap();
					self.set_int_lower_bound(&y, min, con)?;

					let max = bounds
						.iter()
						.filter_map(|(z, x)| {
							let x = NonZeroIntVal::new(*x)?;
							Some(div_floor(*z, x))
						})
						.max()
						.unwrap();
					self.set_int_upper_bound(&y, max, con)?;
				}

				Some(Constraint::IntTimes(x, y, z))
			}
			con => Some(con),
		};
		match simplified {
			Some(simplified) => self.constraints[con] = simplified,
			None => {
				self.constraints[con] = Constraint::PropLogic(BoolExpr::View(BoolView::Const(true)))
			}
		}
		Ok(())
	}

	pub(crate) fn subscribe(&mut self, con: usize) {
		match &self.constraints[con] {
			Constraint::ArrayIntMaximum(args, m) | Constraint::ArrayIntMinimum(args, m) => {
				for a in args {
					if let IntView::Var(a) = a {
						self.int_vars[a.0 as usize].constraints.push(con);
					}
				}
				if let IntView::Var(m) = m {
					self.int_vars[m.0 as usize].constraints.push(con);
				}
			}
			Constraint::ArrayVarIntElement(args, idx, y) => {
				for a in args {
					if let IntView::Var(a) = a {
						self.int_vars[a.0 as usize].constraints.push(con);
					}
				}
				if let IntView::Var(y) = y {
					self.int_vars[y.0 as usize].constraints.push(con);
				}
				if let IntView::Var(idx) = idx {
					self.int_vars[idx.0 as usize].constraints.push(con);
				}
			}
			_ => {}
		}
	}
}
