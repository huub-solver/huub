//! Structures and algorithms  for the integer linear constraint, including
//! `int_lin_eq`, `int_lin_le`, `int_lin_ne` and their reification. These
//! constraint enforce a condition on the sum of (linear transformations of)
//! integer decision variables.

use itertools::{Either, Itertools};
use pindakaas::{
	bool_linear::{BoolLinAggregator, BoolLinExp, BoolLinVariant, BoolLinear},
	ClauseDatabaseTools, Lit as RawLit, Unsatisfiable,
};

use crate::{
	actions::{
		ConstraintInitActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{
		Conflict, Constraint, ExplanationActions, PropagationActions, Propagator, ReasonBuilder,
		SimplificationStatus,
	},
	helpers::opt_field::OptField,
	reformulate::ReformulationError,
	solver::{
		activation_list::{IntEvent, IntPropCond},
		queue::PriorityLevel,
		trail::TrailedInt,
		BoolView, BoolViewInner, IntView, IntViewInner,
	},
	BoolDecision, BoolFormula, Conjunction, IntDecision, IntVal, LinearTransform, NonZeroIntVal,
};

/// Representation of an integer equality constraint that cannot be unified.
///
/// This constraint enforces that two integer decisions take the same value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct IntEq {
	/// The two integer decisions that must be equal.
	pub(crate) vars: [IntDecision; 2],
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of an integer linear constraint within a model.
///
/// This constraint enforces that a sum of (linear transformations of) integer
/// decision variables is less than, equal, or not equal to a constant value, or
/// the implication or reification or whether this is so.
pub struct IntLinear {
	/// The integer linear terms that are being summed.
	pub(crate) terms: Vec<IntDecision>,
	/// The operator that is used to compare the sum to the right-hand side.
	pub(crate) operator: LinOperator,
	/// The constant right-hand side value.
	pub(crate) rhs: IntVal,
	/// Boolean decision varaible that (half-)reifies the constraint, if any.
	pub(crate) reif: Option<Reification>,
}

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqBounds = IntLinearLessEqBoundsImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not refied, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearLessEqBoundsImpl<const R: usize> {
	/// Variables that are being summed
	terms: Vec<IntView>,
	/// Maximum value of the sum can take
	max: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqImpBounds = IntLinearLessEqBoundsImpl<1>;

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqImpValue = IntLinearNotEqValueImpl<1>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqValue = IntLinearNotEqValueImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not reified, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearNotEqValueImpl<const R: usize> {
	/// Decision variables in the summation
	terms: Vec<IntView>,
	/// Number of decision variables that have been fixed to a single value
	num_fixed: TrailedInt,
	/// The value the summation should not equal
	violation: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Possible operators that can be used for in a linear constraint.
pub(crate) enum LinOperator {
	/// Sum is equal to the constant
	Equal,
	/// Sum is less than or equal to the constant
	LessEq,
	/// Sum is not equal to the constant
	NotEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Reification possibilities for a linear constraint.
pub(crate) enum Reification {
	/// The constraint is half-reified by the given [`BoolDecision`].
	ImpliedBy(BoolDecision),
	/// The constraint is reified by the given [`BoolDecision`].
	ReifiedBy(BoolDecision),
}

impl<S: SimplificationActions> Constraint<S> for IntEq {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for &var in &self.vars {
			actions.simplify_on_change_int(var);
		}
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let (lb_0, ub_0) = actions.get_int_bounds(self.vars[0]);
		let (lb_1, ub_1) = actions.get_int_bounds(self.vars[1]);

		if lb_0 == ub_0 {
			actions.set_int_val(self.vars[1], lb_0)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		if lb_1 == ub_1 {
			actions.set_int_val(self.vars[0], lb_1)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		if lb_0 >= lb_1 {
			actions.set_int_lower_bound(self.vars[1], lb_0)?;
		}
		if lb_1 >= lb_0 {
			actions.set_int_lower_bound(self.vars[0], lb_1)?;
		}
		if ub_0 <= ub_1 {
			actions.set_int_upper_bound(self.vars[1], ub_0)?;
		}
		if ub_1 <= ub_0 {
			actions.set_int_upper_bound(self.vars[0], ub_1)?;
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, actions: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let lin = IntLinear {
			terms: vec![self.vars[0], -self.vars[1]],
			operator: LinOperator::Equal,
			rhs: 0,
			reif: None,
		};
		<IntLinear as Constraint<S>>::to_solver(&lin, actions)
	}
}

impl IntLinear {
	/// Change the integer linear constraint to be implied by the given Boolean
	/// decision variable.
	///
	/// The integer linear constraint must hold when the given Boolean decision
	/// variable is `true`. If the constraint does not hold, then the Boolean
	/// decision variable must be `false`.
	pub fn implied_by(self, b: BoolDecision) -> Self {
		assert!(
			self.reif.is_none(),
			"IntLinear is already implied or reified."
		);
		Self {
			reif: Some(Reification::ImpliedBy(b)),
			..self
		}
	}

	/// Internal method to negate the linear constraint.
	fn negate(self) -> Self {
		match self.operator {
			LinOperator::Equal => Self {
				operator: LinOperator::NotEqual,
				..self
			},
			LinOperator::LessEq => Self {
				terms: self.terms.into_iter().map(|v| -v).collect(),
				rhs: -self.rhs - 1,
				..self
			},
			LinOperator::NotEqual => Self {
				operator: LinOperator::Equal,
				..self
			},
		}
	}

	/// Change the integer linear constraint to be reified by the given Boolean
	/// decision variable.
	///
	/// The integer linear constraint must hold if-and-only-if the given Boolean
	/// decision variable is `true`.
	pub fn reified_by(self, b: BoolDecision) -> Self {
		assert!(
			self.reif.is_none(),
			"IntLinear is already implied or reified."
		);
		Self {
			reif: Some(Reification::ReifiedBy(b)),
			..self
		}
	}
}

impl<S: SimplificationActions> Constraint<S> for IntLinear {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for &v in &self.terms {
			actions.simplify_on_change_int(v);
		}
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			actions.simplify_on_change_bool(r);
		}
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// If the reification of the constraint is known, simplify to non-reified
		// version
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			match actions.get_bool_val(r) {
				Some(true) => {
					let mut lin = self.clone();
					lin.reif = None;
					actions.add_constraint(lin);
					return Ok(SimplificationStatus::Subsumed);
				}
				Some(false) => {
					if matches!(self.reif.unwrap(), Reification::ReifiedBy(_)) {
						let mut lin = self.clone().negate();
						lin.reif = None;
						actions.add_constraint(lin);
					}
					return Ok(SimplificationStatus::Subsumed);
				}
				None => {}
			}
		}

		// Filter known values from the terms
		let (vals, terms): (Vec<_>, _) =
			self.terms
				.iter()
				.partition_map(|&var| match actions.get_int_val(var) {
					Some(val) => Either::Left(val),
					None => Either::Right(var),
				});
		self.terms = terms;
		self.rhs -= vals.iter().sum::<IntVal>();

		// Perform single-term domain changes and any possible unification
		match *self.terms.as_slice() {
			[var] if self.reif.is_none() => {
				match self.operator {
					LinOperator::Equal => actions.set_int_val(var, self.rhs)?,
					LinOperator::LessEq => {
						actions.set_int_upper_bound(*self.terms.last().unwrap(), self.rhs)?;
					}
					LinOperator::NotEqual => actions.set_int_not_eq(var, self.rhs)?,
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[var] => {
				let lit = match self.operator {
					LinOperator::Equal => var.eq(self.rhs),
					LinOperator::LessEq => var.leq(self.rhs),
					LinOperator::NotEqual => var.ne(self.rhs),
				};
				match self.reif.unwrap() {
					Reification::ImpliedBy(r) => actions.add_constraint(BoolFormula::Implies(
						Box::new(BoolFormula::Atom(r)),
						Box::new(BoolFormula::Atom(lit)),
					)),
					Reification::ReifiedBy(r) => actions.unify_bool(r, lit)?,
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[a, b] if self.operator == LinOperator::Equal && self.reif.is_none() => {
				actions.unify_int(-a, b - self.rhs)?;
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Collect variable bounds and create their sums
		let lb = self
			.terms
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect_vec();
		let ub = self
			.terms
			.iter()
			.map(|v| actions.get_int_upper_bound(*v))
			.collect_vec();

		let lb_sum: IntVal = lb.iter().sum();
		let ub_sum: IntVal = ub.iter().sum();

		// Check if the constraint is already known to be true or false
		let known_result = match self.operator {
			LinOperator::Equal if lb_sum > self.rhs || ub_sum < self.rhs => Some(false),
			LinOperator::Equal if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(true)
			}
			LinOperator::LessEq if ub_sum <= self.rhs => Some(true),
			LinOperator::LessEq if lb_sum > self.rhs => Some(false),
			LinOperator::NotEqual if lb_sum > self.rhs || ub_sum < self.rhs => Some(true),
			LinOperator::NotEqual if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(false)
			}
			_ => None,
		};
		if let Some(satisfied) = known_result {
			return match self.reif {
				Some(Reification::ImpliedBy(r)) => {
					if !satisfied {
						actions.set_bool(!r)?;
					}
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) => {
					actions.set_bool(if satisfied { r } else { !r })?;
					Ok(SimplificationStatus::Subsumed)
				}
				None if !satisfied => Err(ReformulationError::TrivialUnsatisfiable),
				None => Ok(SimplificationStatus::Subsumed),
			};
		} else if self.operator == LinOperator::NotEqual {
			// No further bounds propagation possible
			return Ok(SimplificationStatus::NoFixpoint);
		}

		// The difference between the right-hand-side value and the sum of the lower
		// bounds. The current lower bound plus this difference is an upper bound
		// for each variable.
		let lb_diff = self.rhs - lb_sum;
		// Propagate the upper bounds of the variables
		for (i, &v) in self.terms.iter().enumerate() {
			let new_ub = lb_diff + lb[i];
			if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
				if lb[i] > new_ub {
					actions.set_bool(!r)?;
					return Ok(SimplificationStatus::Subsumed);
				}
			} else {
				actions.set_int_upper_bound(v, new_ub)?;
			}
		}

		// For equality constraints, propagate the lower bounds of the variables
		if self.operator == LinOperator::Equal {
			if lb_sum == ub_sum {
				assert_eq!(lb_sum, self.rhs);
				return Ok(SimplificationStatus::Subsumed);
			}

			// The amount the sum of the upper bounds exceeds the right-hand-side
			// value (negated). Used to propagate lower bounds of each variable.
			let ub_diff = self.rhs - ub_sum;
			for (i, &v) in self.terms.iter().enumerate() {
				let new_lb = ub_diff + ub[i];
				if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
					if ub[i] < new_lb {
						actions.set_bool(!r)?;
						return Ok(SimplificationStatus::Subsumed);
					}
				} else {
					actions.set_int_lower_bound(v, new_lb)?;
				}
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		use Reification::*;

		let terms = self
			.terms
			.iter()
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		let r = self.reif.as_ref().map(|&r| {
			slv.get_solver_bool(match r {
				ImpliedBy(r) | ReifiedBy(r) => r,
			})
		});
		let full_reif = matches!(self.reif, Some(ReifiedBy(_)));

		// Detect Pseudo-Boolean constraints, and simplify them if possible.
		let (terms, operator, rhs) = if r.is_none()
			&& self.operator != LinOperator::NotEqual
			&& terms
				.iter()
				.all(|v| matches!(v.0, IntViewInner::Bool { .. }))
		{
			let mut offset = 0;
			let bool_terms: Vec<(RawLit, IntVal)> = terms
				.iter()
				.map(|&v| {
					let IntViewInner::Bool { transformer, lit } = v.0 else {
						unreachable!()
					};
					offset += transformer.offset;
					(lit, transformer.scale.into())
				})
				.collect();
			let bool_lin = BoolLinExp::from_terms(&bool_terms);
			let bool_lin = BoolLinear::new(
				bool_lin,
				match self.operator {
					LinOperator::Equal => pindakaas::bool_linear::Comparator::Equal,
					LinOperator::LessEq => pindakaas::bool_linear::Comparator::LessEq,
					LinOperator::NotEqual => unreachable!(),
				},
				self.rhs - offset,
			);
			let map_cmp = |cmp| match cmp {
				pindakaas::bool_linear::Comparator::Equal => LinOperator::Equal,
				pindakaas::bool_linear::Comparator::LessEq => LinOperator::LessEq,
				pindakaas::bool_linear::Comparator::GreaterEq => unreachable!(),
			};

			let (op, lin) = match BoolLinAggregator::default().aggregate(slv, &bool_lin) {
				Err(Unsatisfiable) => return Err(ReformulationError::TrivialUnsatisfiable),
				Ok(BoolLinVariant::Cardinality(card)) => (map_cmp(card.comparator()), card.into()),
				Ok(BoolLinVariant::CardinalityOne(card))
					if card.comparator() == pindakaas::bool_linear::Comparator::Equal =>
				{
					slv.add_clause(card.iter_lits())?;
					(LinOperator::LessEq, card.into())
				}
				Ok(BoolLinVariant::CardinalityOne(card)) => (LinOperator::LessEq, card.into()),
				Ok(BoolLinVariant::Linear(lin)) => (map_cmp(lin.comparator()), lin),
				Ok(BoolLinVariant::Trivial) => return Ok(()),
			};
			(
				lin.iter_terms()
					.map(|(lit, coeff)| {
						IntView(IntViewInner::Bool {
							transformer: LinearTransform::scaled(
								NonZeroIntVal::new(coeff).unwrap(),
							),
							lit,
						})
					})
					.collect_vec(),
				op,
				lin.rhs(),
			)
		} else {
			(terms, self.operator, self.rhs)
		};

		match (operator, r) {
			(LinOperator::Equal, None) => {
				// coeffs * vars >= c <=> -coeffs * vars <= -c
				IntLinearLessEqBounds::new_in(slv, terms.iter().map(|&v| -v), -rhs);
				// coeffs * vars <= c
				IntLinearLessEqBounds::new_in(slv, terms.clone(), rhs);
			}
			(LinOperator::Equal, Some(r)) => {
				if full_reif {
					IntLinearNotEqImpValue::new_in(slv, terms.clone(), rhs, !r);
				}
				IntLinearLessEqImpBounds::new_in(slv, terms.iter().map(|&v| -v), -rhs, r);
				IntLinearLessEqImpBounds::new_in(slv, terms, rhs, r);
			}
			(LinOperator::LessEq, None) => {
				IntLinearLessEqBounds::new_in(slv, terms, rhs);
			}
			(LinOperator::LessEq, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::new_in(
						slv,
						terms.iter().map(|&v| -v),
						-(rhs + 1),
						!r,
					);
				}
				IntLinearLessEqImpBounds::new_in(slv, terms, rhs, r);
			}
			(LinOperator::NotEqual, None) => {
				IntLinearNotEqValue::new_in(slv, terms, rhs);
			}
			(LinOperator::NotEqual, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::new_in(slv, terms.clone(), rhs, !r);
					IntLinearLessEqImpBounds::new_in(slv, terms.iter().map(|&v| -v), -rhs, !r);
				}
				IntLinearNotEqImpValue::new_in(slv, terms, rhs, r);
			}
		}
		Ok(())
	}
}

impl IntLinearLessEqBounds {
	/// Create a new [`IntLinearLessEqBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(solver: &mut P, vars: impl IntoIterator<Item = IntView>, mut max: IntVal)
	where
		P: PropagatorInitActions + ?Sized,
	{
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				max,
				reification: Default::default(),
			}),
			PriorityLevel::Low,
		);
		solver.enqueue_now(prop);
		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::LowerBound);
		}
	}
}

impl<const R: usize, P, E> Propagator<P, E> for IntLinearLessEqBoundsImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, data: u64) -> Conjunction {
		let i = data as usize;
		let mut var_lits: Vec<RawLit> = self
			.terms
			.iter()
			.enumerate()
			.filter_map(|(j, v)| {
				if j == i {
					return None;
				}
				if let BoolView(BoolViewInner::Lit(lit)) = actions.get_int_lower_bound_lit(*v) {
					Some(lit)
				} else {
					None
				}
			})
			.collect();
		if let Some(r) = self.reification.get() {
			var_lits.push(*r);
		}
		var_lits
	}
	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].lower_bound
	#[tracing::instrument(name = "int_lin_le", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// If the reified variable is false, skip propagation
		if let Some(&r) = self.reification.get() {
			if !actions
				.get_bool_val(BoolView(BoolViewInner::Lit(r)))
				.unwrap_or(true)
			{
				return Ok(());
			}
		}

		// get the difference between the right-hand-side value and the sum of variable
		// lower bounds
		let sum = self
			.terms
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.max, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the
		// right-hand-side value
		if let Some(&r) = self.reification.get() {
			let r = BoolView(BoolViewInner::Lit(r));
			if sum < 0 {
				actions.set_bool(!r, |a: &mut P| {
					self.terms
						.iter()
						.map(|v| a.get_int_lower_bound_lit(*v))
						.collect_vec()
				})?;
			}
			// skip the remaining propagation if the reified variable is not assigned to
			// true
			if !actions.get_bool_val(r).unwrap_or(false) {
				return Ok(());
			}
		}

		// propagate the upper bound of the variables
		for (j, &v) in self.terms.iter().enumerate() {
			let reason = actions.deferred_reason(j as u64);
			let ub = sum + actions.get_int_lower_bound(v);
			actions.set_int_upper_bound(v, ub, reason)?;
		}
		Ok(())
	}
}

impl IntLinearLessEqImpBounds {
	/// Create a new [`IntLinearLessEqImpBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(
		solver: &mut P,
		vars: impl IntoIterator<Item = IntView>,
		mut max: IntVal,
		reification: BoolView,
	) where
		P: PropagatorInitActions + ?Sized,
	{
		let reification = match reification.0 {
			BoolViewInner::Lit(r) => r,
			BoolViewInner::Const(true) => return IntLinearLessEqBounds::new_in(solver, vars, max),
			BoolViewInner::Const(false) => return,
		};
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				max,
				reification: OptField::new(reification),
			}),
			PriorityLevel::Low,
		);
		solver.enqueue_now(prop);
		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::LowerBound);
		}
		solver.enqueue_on_bool_change(prop, BoolView(BoolViewInner::Lit(reification)));
	}
}

impl IntLinearNotEqImpValue {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(
		solver: &mut P,
		vars: impl IntoIterator<Item = IntView>,
		mut violation: IntVal,
		reification: BoolView,
	) where
		P: PropagatorInitActions + ?Sized,
	{
		let reification = match reification.0 {
			BoolViewInner::Lit(r) => r,
			BoolViewInner::Const(true) => {
				return IntLinearNotEqValue::new_in(solver, vars, violation)
			}
			BoolViewInner::Const(false) => return,
		};

		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = solver.get_int_val(v) {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();
		let num_fixed = solver.new_trailed_int(0);

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				violation,
				num_fixed,
				reification: OptField::new(reification),
			}),
			PriorityLevel::Low,
		);

		for (i, &v) in vars.iter().enumerate() {
			solver.advise_on_int_change(prop, v, IntPropCond::Fixed, i as u64);
		}
		solver.advise_on_bool_change(
			prop,
			BoolView(BoolViewInner::Lit(reification)),
			vars.len() as u64,
		);
	}
}

impl IntLinearNotEqValue {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(solver: &mut P, vars: impl IntoIterator<Item = IntView>, mut violation: IntVal)
	where
		P: PropagatorInitActions + ?Sized,
	{
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = solver.get_int_val(v) {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();
		let num_fixed = solver.new_trailed_int(0);

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				violation,
				num_fixed,
				reification: Default::default(),
			}),
			PriorityLevel::Low,
		);

		for (i, &v) in vars.iter().enumerate() {
			solver.advise_on_int_change(prop, v, IntPropCond::Fixed, i as u64);
		}
	}
}

impl<const R: usize> IntLinearNotEqValueImpl<R> {
	/// Increment the number of decision variables that are fixed, returning
	/// whether the propagator should now be enqueued.
	fn increment_num_fixed(&self, actions: &mut impl ExplanationActions) -> bool {
		let num_fixed = actions.get_trailed_int(self.num_fixed) + 1;
		let _ = actions.set_trailed_int(self.num_fixed, num_fixed);
		num_fixed == (self.terms.len() + R - 1) as i64
	}

	/// Helper function to construct the reason for propagation given the index
	/// of the variable in the list of variables to sum or the length of the
	/// list, if explaining the reification.
	fn reason<A: ExplanationActions>(&self, data: usize) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let mut conj: Vec<_> = self
				.terms
				.iter()
				.enumerate()
				.filter_map(|(i, v)| {
					if data != i {
						Some(actions.get_int_val_lit(*v).unwrap())
					} else {
						None
					}
				})
				.collect();
			if let Some(&r) = self.reification.get() {
				if data != self.terms.len() {
					conj.push(BoolView(BoolViewInner::Lit(r)));
				}
			}
			conj
		}
	}
}

impl<const R: usize, P, E> Propagator<P, E> for IntLinearNotEqValueImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn advise_of_bool_change(&mut self, actions: &mut E, _view: BoolView, _data: u64) -> bool {
		debug_assert!(self.reification.get().is_some());
		debug_assert_eq!(_data, self.terms.len() as u64);
		debug_assert!(actions
			.get_bool_val(BoolView(BoolViewInner::Lit(
				*self.reification.get().unwrap()
			)))
			.is_some());

		self.increment_num_fixed(actions)
	}

	fn advise_of_int_change(
		&mut self,
		actions: &mut E,
		_view: IntView,
		_event: IntEvent,
		_data: u64,
	) -> bool {
		debug_assert!(actions.get_int_val(self.terms[_data as usize]).is_some());

		self.increment_num_fixed(actions)
	}

	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (r, r_fixed) = if let Some(&r) = self.reification.get() {
			let r = BoolView(BoolViewInner::Lit(r));
			match actions.get_bool_val(r) {
				Some(false) => return Ok(()),
				Some(true) => (r, true),
				None => (r, false),
			}
		} else {
			(true.into(), true)
		};
		let mut sum = 0;
		let mut unfixed = None;
		for (i, v) in self.terms.iter().enumerate() {
			if let Some(val) = actions.get_int_val(*v) {
				sum += val;
			} else if unfixed.is_some() {
				debug_assert!(false, "propagator shouldn't have been scheduled");
				return Ok(());
			} else {
				unfixed = Some((i, v));
			}
		}
		if let Some((i, v)) = unfixed {
			if !r_fixed {
				debug_assert!(false, "propagator shouldn't have been scheduled");
				return Ok(());
			}
			let val = self.violation - sum;
			actions.set_int_not_eq(*v, val, self.reason(i))
		} else if sum == self.violation {
			actions.set_bool(!r, self.reason(self.terms.len()))
		} else {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_linear::{
			IntLinear, IntLinearLessEqBounds, IntLinearNotEqValue, LinOperator, Reification,
		},
		reformulate::InitConfig,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		Model, NonZeroIntVal,
	};

	#[test]
	#[traced_test]
	fn test_linear_ge_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::new_in(
			&mut slv,
			vec![a * NonZeroIntVal::new(-2).unwrap(), -b, -c],
			-6,
		);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 2, 2
			2, 1, 1
			2, 1, 2
			2, 2, 1
			2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_linear_ge_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var(1..=2);
		let b = prb.new_int_var(1..=2);
		let c = prb.new_int_var(1..=2);

		prb += (a * 2 + b + c).geq(10);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_le_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::new_in(&mut slv, vec![a * NonZeroIntVal::new(2).unwrap(), b, c], 6);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 1, 1
			1, 1, 2
			1, 2, 1
			1, 2, 2
			2, 1, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_linear_le_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var(1..=4);
		let b = prb.new_int_var(1..=4);
		let c = prb.new_int_var(1..=4);

		prb += (a * 2 + b + c).leq(3);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntLinearNotEqValue::new_in(&mut slv, vec![a * NonZeroIntVal::new(2).unwrap(), b, c], 6);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
		1, 1, 1
		1, 1, 2
		1, 2, 1
		2, 1, 2
		2, 2, 1
		2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ge_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var(1..=2);
		let b = prb.new_int_var(1..=2);
		let c = prb.new_int_var(1..=2);

		prb += (a * 2 + b + c).geq(7).implied_by(r);
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 2, 1, 2
		true, 2, 2, 1
		true, 2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_le_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var(1..=2);
		let b = prb.new_int_var(1..=2);
		let c = prb.new_int_var(1..=2);

		prb += (a * 2 + b + c).leq(5).implied_by(r);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 1, 1, 1
		true, 1, 1, 2
		true, 1, 2, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ne_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var(1..=2);
		let b = prb.new_int_var(1..=2);
		let c = prb.new_int_var(1..=2);

		prb += (a * 2 + b + c).ne(6).implied_by(r);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 1, 1, 1
		true, 1, 1, 2
		true, 1, 2, 1
		true, 2, 1, 2
		true, 2, 2, 1
		true, 2, 2, 2"#]],
		);
	}

	#[test]
	fn test_constraint_rewriting() {
		// Regression test for GitHub issue 233, where a `int_lin_le_reif` known to be
		// false was rewritten incorrectly. It allowed `a` to be 2.
		let mut prb = Model::default();
		let a = prb.new_int_var(1..=2);
		prb += IntLinear {
			terms: vec![-a],
			operator: LinOperator::LessEq,
			rhs: -2,
			reif: Some(Reification::ReifiedBy(false.into())),
		};
		prb.expect_solutions(&[a], expect![[r#"1"#]]);
	}
}
