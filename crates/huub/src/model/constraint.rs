//! Definitions of constraints that can be used as part of a model.

use std::ops::AddAssign;

use pindakaas::{
	propositional_logic::Formula, solver::propagation::PropagatingSolver, ClauseDatabaseTools,
};
use rangelist::{IntervalIterator, RangeList};

use crate::{
	actions::{ConstraintInitActions, SimplificationActions},
	constraints::{
		all_different_int::AllDifferentInt, array_int_element::ArrayIntElement,
		array_int_minimum::ArrayIntMinimum, array_var_bool_element::ArrayVarBoolElement,
		array_var_int_element::ArrayVarIntElement, disjunctive_strict::DisjunctiveStrict,
		int_abs::IntAbs, int_div::IntDiv, int_linear::IntLinear, int_pow::IntPow,
		int_times::IntTimes, set_in_reif::SetInReif, table_int::TableInt, BoxedConstraint,
		Constraint, SimplificationStatus,
	},
	model::{
		bool::BoolView,
		int::IntExpr,
		reformulate::{ReformulationContext, VariableMap},
	},
	solver::engine::Engine,
	IntSetVal, IntVal, LitMeaning, Model, ReformulationError, Solver,
};

/// Wrapper around [`Model`] that knows the constraint being initialized.
struct ConstraintInitContext<'a> {
	/// Index of the constraint being initialized.
	con: usize,
	/// Reference to the Model in which the constraint exists.
	model: &'a mut Model,
}

#[allow(
	clippy::missing_docs_in_private_items,
	reason = "constraints are generally documented on their own types"
)]
#[derive(Clone, Debug)]
/// An disambiguation of the different constraints objects that can be used in a
/// [`Model`] object.
///
/// This enum type is used to store and analyze the constraints in a [`Model`].
pub(crate) enum ConstraintStore {
	AllDifferentInt(AllDifferentInt),
	ArrayIntElement(ArrayIntElement),
	ArrayIntMinimum(ArrayIntMinimum),
	ArrayVarBoolElement(ArrayVarBoolElement),
	ArrayVarIntElement(ArrayVarIntElement),
	DisjunctiveStrict(DisjunctiveStrict),
	IntAbs(IntAbs),
	IntDiv(IntDiv),
	IntLinear(IntLinear),
	IntPow(IntPow),
	IntTimes(IntTimes),
	/// A constraint given as a propasitional logic formula, which is enforced to
	/// be `true`.
	PropLogic(Formula<BoolView>),
	SetInReif(SetInReif),
	TableInt(TableInt),
	UserCustom(BoxedConstraint),
}

impl ConstraintInitActions for ConstraintInitContext<'_> {
	fn simplify_on_change_bool(&mut self, _var: BoolView) {
		todo!()
	}

	fn simplify_on_change_int(&mut self, var: IntExpr) {
		match var {
			IntExpr::Bool(_, v) => self.simplify_on_change_bool(v),
			IntExpr::Linear(_, v) | IntExpr::Var(v) => {
				self.model.int_vars[v].constraints.push(self.con);
			}
			IntExpr::Const(_) => {}
		}
	}
}

impl ConstraintStore {
	/// Map the constraint into propagators and clauses to be added to the given
	/// solver, using the variable mapping provided.
	pub(crate) fn to_solver<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
	) -> Result<(), ReformulationError> {
		let mut actions = ReformulationContext { slv, map };
		match self {
			ConstraintStore::AllDifferentInt(con) => {
				<AllDifferentInt as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::ArrayIntElement(con) => {
				<ArrayIntElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::ArrayIntMinimum(con) => {
				<ArrayIntMinimum as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::ArrayVarBoolElement(con) => {
				<ArrayVarBoolElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::ArrayVarIntElement(con) => {
				<ArrayVarIntElement as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::DisjunctiveStrict(con) => {
				<DisjunctiveStrict as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntAbs(con) => {
				<IntAbs as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntDiv(con) => {
				<IntDiv as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntLinear(con) => {
				<IntLinear as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntPow(con) => {
				<IntPow as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::IntTimes(con) => {
				<IntTimes as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::PropLogic(exp) => {
				<Formula<BoolView> as Constraint<Model>>::to_solver(exp, &mut actions)
			}
			ConstraintStore::SetInReif(con) => {
				<SetInReif as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::TableInt(con) => {
				<TableInt as Constraint<Model>>::to_solver(con, &mut actions)
			}
			ConstraintStore::UserCustom(con) => con.to_solver(&mut actions),
		}
	}
}

impl Model {
	/// Propagate the constraint at index `con`, updating the domains of the
	/// variables and rewriting the constraint if necessary.
	pub(crate) fn propagate(&mut self, con: usize) -> Result<(), ReformulationError> {
		let Some(mut con_obj) = self.constraints[con].take() else {
			return Ok(());
		};

		let status = match &mut con_obj {
			ConstraintStore::AllDifferentInt(c) => c.simplify(self),
			ConstraintStore::ArrayIntElement(c) => c.simplify(self),
			ConstraintStore::ArrayIntMinimum(c) => c.simplify(self),
			ConstraintStore::ArrayVarBoolElement(c) => c.simplify(self),
			ConstraintStore::ArrayVarIntElement(c) => c.simplify(self),
			ConstraintStore::DisjunctiveStrict(c) => c.simplify(self),
			ConstraintStore::IntAbs(c) => c.simplify(self),
			ConstraintStore::IntDiv(c) => c.simplify(self),
			ConstraintStore::IntLinear(c) => c.simplify(self),
			ConstraintStore::IntPow(c) => c.simplify(self),
			ConstraintStore::IntTimes(c) => c.simplify(self),
			ConstraintStore::PropLogic(exp) => exp.simplify(self),
			ConstraintStore::SetInReif(c) => c.simplify(self),
			ConstraintStore::TableInt(con) => con.simplify(self),
			ConstraintStore::UserCustom(con) => con.simplify(self),
		}?;
		match status {
			SimplificationStatus::Subsumed => {
				// Constraint is known to be satisfied, no need to place back.
			}
			SimplificationStatus::Fixpoint => {
				self.constraints[con] = Some(con_obj);
			}
		}
		Ok(())
	}

	/// Subscribe the constraint located at index `con` to changes in the
	/// variables it depends on.
	pub(crate) fn subscribe(&mut self, con: usize) {
		let con_store = self.constraints[con].take().unwrap();
		let mut ctx = ConstraintInitContext { con, model: self };
		match &con_store {
			ConstraintStore::AllDifferentInt(con) => {
				<AllDifferentInt as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::ArrayIntElement(con) => {
				<ArrayIntElement as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::ArrayIntMinimum(con) => {
				<ArrayIntMinimum as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::ArrayVarBoolElement(con) => {
				<ArrayVarBoolElement as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::ArrayVarIntElement(con) => {
				<ArrayVarIntElement as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::DisjunctiveStrict(con) => {
				<DisjunctiveStrict as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::IntAbs(con) => {
				<IntAbs as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::IntDiv(con) => {
				<IntDiv as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::IntLinear(con) => {
				<IntLinear as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::IntPow(con) => {
				<IntPow as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::IntTimes(con) => {
				<IntTimes as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::PropLogic(exp) => {
				<Formula<BoolView> as Constraint<Model>>::initialize(exp, &mut ctx)
			}
			ConstraintStore::SetInReif(con) => {
				<SetInReif as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::TableInt(con) => {
				<TableInt as Constraint<Model>>::initialize(con, &mut ctx)
			}
			ConstraintStore::UserCustom(con) => con.initialize(&mut ctx),
		}
		self.constraints[con] = Some(con_store);
	}
}

impl SimplificationActions for Model {
	fn add_constraint<C>(&mut self, constraint: C)
	where
		Model: AddAssign<C>,
	{
		*self += constraint;
	}

	fn check_int_in_domain(&self, var: IntExpr, val: IntVal) -> bool {
		match var {
			IntExpr::Var(v) => self.int_vars[v].domain.contains(&val),
			IntExpr::Const(v) => v == val,
			IntExpr::Linear(t, v) => match t.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => self.int_vars[v].domain.contains(&val),
				Err(false) => false,
				_ => unreachable!(),
			},
			IntExpr::Bool(t, _) => match t.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => val == 0 || val == 1,
				Err(false) => false,
				_ => unreachable!(),
			},
		}
	}

	fn get_bool_val(&self, _: BoolView) -> Option<bool> {
		None // TODO
	}

	fn get_int_lower_bound(&self, var: IntExpr) -> IntVal {
		match var {
			IntExpr::Var(v) => {
				let def = &self.int_vars[v];
				*def.domain.lower_bound().unwrap()
			}
			IntExpr::Const(v) => v,
			IntExpr::Linear(t, v) => {
				let def = &self.int_vars[v];
				if t.positive_scale() {
					t.transform(*def.domain.lower_bound().unwrap())
				} else {
					t.transform(*def.domain.upper_bound().unwrap())
				}
			}
			IntExpr::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(0)
				} else {
					t.transform(1)
				}
			}
		}
	}

	fn get_int_upper_bound(&self, var: IntExpr) -> IntVal {
		match var {
			IntExpr::Var(v) => {
				let def = &self.int_vars[v];
				*def.domain.upper_bound().unwrap()
			}
			IntExpr::Const(v) => v,
			IntExpr::Linear(t, v) => {
				let def = &self.int_vars[v];
				if t.positive_scale() {
					t.transform(*def.domain.upper_bound().unwrap())
				} else {
					t.transform(*def.domain.lower_bound().unwrap())
				}
			}
			IntExpr::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(1)
				} else {
					t.transform(0)
				}
			}
		}
	}

	fn set_bool(&mut self, var: BoolView) -> Result<(), ReformulationError> {
		match var {
			BoolView::Lit(l) => Ok(self.cnf.add_clause([l])?),
			BoolView::Const(true) => Ok(()),
			BoolView::Const(false) => Err(ReformulationError::TrivialUnsatisfiable),
			BoolView::IntEq(iv, val) => self.set_int_val(iv.into(), val),
			BoolView::IntGreaterEq(iv, val) => self.set_int_lower_bound(iv.into(), val),
			BoolView::IntLess(iv, val) => self.set_int_upper_bound(iv.into(), val - 1),
			BoolView::IntNotEq(iv, val) => self.set_int_not_eq(iv.into(), val),
		}
	}

	fn set_int_in_set(
		&mut self,
		var: IntExpr,
		values: &IntSetVal,
	) -> Result<(), ReformulationError> {
		match var {
			IntExpr::Var(v) => {
				let intersect: RangeList<_> = self.int_vars[v].domain.intersect(values);
				if intersect.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v].domain == intersect {
					return Ok(());
				}
				self.int_vars[v].domain = intersect;
				let constraints = self.int_vars[v].constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			IntExpr::Const(v) => {
				if !values.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntExpr::Linear(trans, iv) => {
				let values = trans.rev_transform_int_set(values);
				self.set_int_in_set(iv.into(), &values)
			}
			IntExpr::Bool(trans, b) => {
				let values = trans.rev_transform_int_set(values);
				if !values.contains(&0) {
					self.set_bool(b)?;
				}
				if !values.contains(&1) {
					self.set_bool(!b)?;
				}
				Ok(())
			}
		}
	}

	fn set_int_lower_bound(&mut self, var: IntExpr, lb: IntVal) -> Result<(), ReformulationError> {
		match var {
			IntExpr::Var(v) => {
				let def = &mut self.int_vars[v];
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
					self.enqueue(c);
				}
				Ok(())
			}
			IntExpr::Const(v) => {
				if v < lb {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntExpr::Linear(trans, iv) => {
				match trans.rev_transform_lit(LitMeaning::GreaterEq(lb)) {
					Ok(LitMeaning::GreaterEq(val)) => self.set_int_lower_bound(iv.into(), val),
					Ok(LitMeaning::Less(val)) => self.set_int_upper_bound(iv.into(), val - 1),
					_ => unreachable!(),
				}
			}
			IntExpr::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::GreaterEq(lb)) {
				Ok(LitMeaning::GreaterEq(1)) => self.set_bool(b),
				Ok(LitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::GreaterEq(_)) => Ok(()),
				Ok(LitMeaning::Less(1)) => self.set_bool(!b),
				Ok(LitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	fn set_int_upper_bound(&mut self, var: IntExpr, ub: IntVal) -> Result<(), ReformulationError> {
		match var {
			IntExpr::Var(v) => {
				let def = &mut self.int_vars[v];
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
					self.enqueue(c);
				}
				Ok(())
			}
			IntExpr::Const(v) => {
				if v > ub {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntExpr::Linear(trans, iv) => match trans.rev_transform_lit(LitMeaning::Less(ub + 1)) {
				Ok(LitMeaning::GreaterEq(val)) => self.set_int_lower_bound(iv.into(), val),
				Ok(LitMeaning::Less(val)) => self.set_int_upper_bound(iv.into(), val - 1),
				_ => unreachable!(),
			},
			IntExpr::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::Less(ub + 1)) {
				Ok(LitMeaning::GreaterEq(1)) => self.set_bool(b),
				Ok(LitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::GreaterEq(_)) => Ok(()),
				Ok(LitMeaning::Less(1)) => self.set_bool(!b),
				Ok(LitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	fn set_int_val(&mut self, var: IntExpr, val: IntVal) -> Result<(), ReformulationError> {
		match var {
			IntExpr::Var(v) => {
				let def = &mut self.int_vars[v];
				if def.domain.contains(&val) {
					def.domain = RangeList::from(val..=val);
					let constraints = def.constraints.clone();
					for c in constraints {
						self.enqueue(c);
					}
					Ok(())
				} else {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
			}
			IntExpr::Const(i) if i == val => Ok(()),
			IntExpr::Const(_) => Err(ReformulationError::TrivialUnsatisfiable),
			IntExpr::Linear(trans, iv) => match trans.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => self.set_int_val(iv.into(), val),
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
			IntExpr::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => match val {
					0 => self.set_bool(!b),
					1 => self.set_bool(b),
					_ => Err(ReformulationError::TrivialUnsatisfiable),
				},
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
		}
	}

	fn set_int_not_eq(&mut self, var: IntExpr, val: IntVal) -> Result<(), ReformulationError> {
		self.set_int_in_set(var, &(val..=val).into())
	}

	fn set_int_not_in_set(
		&mut self,
		var: IntExpr,
		values: &IntSetVal,
	) -> Result<(), ReformulationError> {
		match var {
			IntExpr::Var(v) => {
				let diff: RangeList<_> = self.int_vars[v].domain.diff(values);
				if diff.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v].domain == diff {
					return Ok(());
				}
				self.int_vars[v].domain = diff;
				let constraints = self.int_vars[v].constraints.clone();
				for c in constraints {
					self.enqueue(c);
				}
				Ok(())
			}
			IntExpr::Const(v) => {
				if values.contains(&v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntExpr::Linear(trans, iv) => {
				let mask = trans.rev_transform_int_set(values);
				self.set_int_not_in_set(iv.into(), &mask)
			}
			IntExpr::Bool(trans, b) => {
				let values = trans.rev_transform_int_set(values);
				if values.contains(&0) {
					self.set_bool(b)?;
				}
				if values.contains(&1) {
					self.set_bool(!b)?;
				}
				Ok(())
			}
		}
	}
}
