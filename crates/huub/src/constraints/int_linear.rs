//! Structures and algorithms  for the integer linear constraint, including
//! `int_lin_eq`, `int_lin_le`, `int_lin_ne` and their reification. These
//! constraint enforce a condition on the sum of (linear transformations of)
//! integer decision variables.

use std::ops::AddAssign;

use itertools::{Either, Itertools};
use pindakaas::{
	bool_linear::{BoolLinAggregator, BoolLinExp, BoolLinVariant, BoolLinear},
	Lit as RawLit, Unsatisfiable,
};

use crate::{
	actions::{
		BoolInspectionActions, BoolPostingActions, BoolPropagationActions,
		BoolSimplificationActions, InitializationActions, IntDecisionActions, IntInspectionActions,
		IntPostingActions, IntPropagationActions, IntSimplificationActions, PostingActions,
		PropagationActions, ReasoningEngine, ReformulationActions, SimplificationActions,
		TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelBoolView, ModelIntView, Propagator, ReasonBuilder,
		SimplificationStatus, SolverBoolView, SolverIntView,
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
	/// Boolean decision variable that (half-)reifies the constraint, if any.
	pub(crate) reif: Option<Reification>,
}

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqBounds<IV> = IntLinearLessEqBoundsImpl<0, IV, RawLit>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not reified, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearLessEqBoundsImpl<const R: usize, IV, BV> {
	/// Variables that are being summed
	terms: Vec<IV>,
	/// Maximum value of the sum can take
	max: IntVal,
	/// Reified variable, if any
	reification: OptField<R, BV>,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqImpBounds<IV, BV> = IntLinearLessEqBoundsImpl<1, IV, BV>;

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqImpValue<IV, BV> = IntLinearNotEqValueImpl<1, IV, BV>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqValue<IV> = IntLinearNotEqValueImpl<0, IV, RawLit>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not reified, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearNotEqValueImpl<const R: usize, IV, BV> {
	/// Decision variables in the summation
	terms: Vec<IV>,
	/// Number of decision variables that have been fixed to a single value
	num_fixed: TrailedInt,
	/// The value the summation should not equal
	violation: IntVal,
	/// Reified variable, if any
	reification: OptField<R, BV>,
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

impl<E> Constraint<E> for IntEq
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	IntDecision: ModelIntView<E>,
	BoolDecision: ModelBoolView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		// Note that one variable might be fixed and not the other one. Gaps in domains
		// or linear view might require multiple rounds of propagation to reach a
		// fixpoint.
		if self.vars.iter().all(|v| v.val(ctx).is_some()) {
			Ok(SimplificationStatus::Subsumed)
		} else {
			Ok(SimplificationStatus::NoFixpoint)
		}
	}

	fn to_solver(&self, actions: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let lin = IntLinear {
			terms: vec![self.vars[0], -self.vars[1]],
			operator: LinOperator::Equal,
			rhs: 0,
			reif: None,
		};
		<IntLinear as Constraint<E>>::to_solver(&lin, actions)
	}
}

impl<E> Propagator<E> for IntEq
where
	E: ReasoningEngine,
	IntDecision: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		for iv in self.vars {
			iv.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// Channel bounds of self.vars[0] to self.vars[1]
		self.vars[0].set_lower_bound(
			ctx,
			self.vars[1].lower_bound(ctx),
			[self.vars[1].lower_bound_lit(ctx)],
		)?;
		self.vars[0].set_upper_bound(
			ctx,
			self.vars[1].upper_bound(ctx),
			[self.vars[1].upper_bound_lit(ctx)],
		)?;

		// Channel bounds of self.vars[1] to self.vars[0]
		self.vars[1].set_lower_bound(
			ctx,
			self.vars[0].lower_bound(ctx),
			[self.vars[0].lower_bound_lit(ctx)],
		)?;
		self.vars[1].set_upper_bound(
			ctx,
			self.vars[0].upper_bound(ctx),
			[self.vars[0].upper_bound_lit(ctx)],
		)?;
		Ok(())
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

impl<E> Constraint<E> for IntLinear
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	IntDecision: ModelIntView<E>,
	BoolDecision: ModelBoolView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// If the reification of the constraint is known, simplify to non-reified
		// version
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			match r.val(ctx) {
				Some(true) => {
					let mut lin = self.clone();
					lin.reif = None;
					ctx.add_constraint(lin);
					return Ok(SimplificationStatus::Subsumed);
				}
				Some(false) => {
					if matches!(self.reif.unwrap(), Reification::ReifiedBy(_)) {
						let mut lin = self.clone().negate();
						lin.reif = None;
						ctx.add_constraint(lin);
					}
					return Ok(SimplificationStatus::Subsumed);
				}
				None => {}
			}
		}

		// Filter known values from the terms
		let (vals, terms): (Vec<_>, _) =
			self.terms.iter().partition_map(|&var| match var.val(ctx) {
				Some(val) => Either::Left(val),
				None => Either::Right(var),
			});
		self.terms = terms;
		self.rhs -= vals.iter().sum::<IntVal>();

		// Perform single-term domain changes and any possible unification
		match *self.terms.as_slice() {
			[var] if self.reif.is_none() => {
				match self.operator {
					LinOperator::Equal => var.set_val(ctx, self.rhs, [])?,
					LinOperator::LessEq => var.set_upper_bound(ctx, self.rhs, [])?,
					LinOperator::NotEqual => var.set_not_eq(ctx, self.rhs, [])?,
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
					Reification::ImpliedBy(r) => ctx.add_constraint(BoolFormula::Implies(
						Box::new(BoolFormula::Atom(r)),
						Box::new(BoolFormula::Atom(lit)),
					)),
					Reification::ReifiedBy(r) => r.unify(ctx, lit)?,
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[a, b] if self.operator == LinOperator::Equal && self.reif.is_none() => {
				(-a).unify(ctx, b - self.rhs)?;
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Collect variable bounds and create their sums
		let lb = self.terms.iter().map(|v| v.lower_bound(ctx)).collect_vec();
		let ub = self.terms.iter().map(|v| v.upper_bound(ctx)).collect_vec();

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
		let fail_reason = |ctx: &mut E::PropagationCtx<'_>| {
			self.terms
				.iter()
				.map(|v| match self.operator {
					LinOperator::Equal if lb_sum > self.rhs => v.lower_bound_lit(ctx),
					LinOperator::Equal if ub_sum < self.rhs => v.upper_bound_lit(ctx),
					LinOperator::LessEq => v.lower_bound_lit(ctx),
					LinOperator::NotEqual => v.val_lit(ctx).unwrap(),
					_ => unreachable!(),
				})
				.collect_vec()
		};

		if let Some(satisfied) = known_result {
			return match self.reif {
				Some(Reification::ImpliedBy(r)) => {
					if !satisfied {
						r.set_val(ctx, false, fail_reason)?;
					}
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) if satisfied => {
					r.set(ctx, |ctx: &mut E::PropagationCtx<'_>| {
						self.terms
							.iter()
							.flat_map(|v| match self.operator {
								LinOperator::NotEqual if lb_sum > self.rhs => {
									vec![v.lower_bound_lit(ctx)]
								}
								LinOperator::NotEqual if ub_sum < self.rhs => {
									vec![v.upper_bound_lit(ctx)]
								}
								LinOperator::LessEq => vec![v.upper_bound_lit(ctx)],
								LinOperator::NotEqual => {
									vec![v.lower_bound_lit(ctx), v.upper_bound_lit(ctx)]
								}
								_ => unreachable!(),
							})
							.collect_vec()
					})?;
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) => {
					debug_assert!(!satisfied);
					r.set_val(ctx, false, fail_reason)?;
					Ok(SimplificationStatus::Subsumed)
				}
				None if !satisfied => Err(ctx.declare_conflict(fail_reason)),
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
		for (i, v) in self.terms.iter().enumerate() {
			let new_ub = lb_diff + lb[i];
			let reason = |ctx: &mut E::PropagationCtx<'_>| {
				self.terms
					.iter()
					.enumerate()
					.filter(|&(j, _)| j != i)
					.map(|(_, w)| w.lower_bound_lit(ctx))
					.collect_vec()
			};
			if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
				if lb[i] > new_ub {
					r.set_val(ctx, false, reason)?;
					return Ok(SimplificationStatus::Subsumed);
				}
			} else {
				v.set_upper_bound(ctx, new_ub, reason)?;
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
			for (i, v) in self.terms.iter().enumerate() {
				let new_lb = ub_diff + ub[i];
				let reason = |ctx: &mut E::PropagationCtx<'_>| {
					self.terms
						.iter()
						.enumerate()
						.filter(|&(j, _)| j != i)
						.map(|(_, &w)| w.upper_bound_lit(ctx))
						.collect_vec()
				};
				if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
					if ub[i] < new_lb {
						r.set_val(ctx, false, reason)?;
						return Ok(SimplificationStatus::Subsumed);
					}
				} else {
					v.set_lower_bound(ctx, new_lb, reason)?;
				}
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		use Reification::*;

		let terms = self.terms.iter().map(|&v| slv.solver_int(v)).collect_vec();
		let r = self.reif.as_ref().map(|&r| {
			slv.solver_bool(match r {
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

			let mut wrapper = slv.clause_database_wrapper();
			let (op, lin) = match BoolLinAggregator::default().aggregate(&mut wrapper, &bool_lin) {
				Err(Unsatisfiable) => return Err(wrapper.error.unwrap()),
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

impl<E> Propagator<E> for IntLinear
where
	E: ReasoningEngine,
	IntDecision: SolverIntView<E>,
	BoolDecision: SolverBoolView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		for &iv in &self.terms {
			iv.enqueue_when(ctx, IntPropCond::Bounds);
		}
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			r.enqueue_when_fixed(ctx);
		}
	}

	fn propagate(&mut self, _: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		unreachable!()
	}
}

impl IntLinearLessEqBounds<IntView> {
	/// Create a new [`IntLinearLessEqBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(solver: &mut E, vars: impl IntoIterator<Item = IntView>, mut max: IntVal)
	where
		E: AddAssign<BoxedPropagator> + InitializationActions + ?Sized,
		IntView: IntInspectionActions<E>,
	{
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let Some(c) = v.val(solver) {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		*solver += Box::new(Self {
			terms: vars.clone(),
			max,
			reification: Default::default(),
		});
	}
}

impl<const R: usize, BV, E, IV> Propagator<E> for IntLinearLessEqBoundsImpl<R, IV, BV>
where
	E: ReasoningEngine,
	BV: SolverBoolView<E>,
	IV: SolverIntView<E>,
{
	fn explain(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		_: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let i = data as usize;
		let mut var_lits: Vec<_> = self
			.terms
			.iter()
			.enumerate()
			.filter_map(|(j, v)| {
				if j == i {
					return None;
				}
				Some(v.lower_bound_lit(ctx))
			})
			.collect();
		if let Some(r) = self.reification.get() {
			var_lits.push(r.clone().into());
		}
		var_lits
	}

	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in self.terms.iter() {
			v.enqueue_when(ctx, IntPropCond::LowerBound);
		}
		if let Some(r) = self.reification.get() {
			r.enqueue_when_fixed(ctx);
		}
	}

	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].lower_bound
	#[tracing::instrument(name = "int_lin_le", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// If the reified variable is false, skip propagation
		if let Some(r) = self.reification.get() {
			if !r.val(ctx).unwrap_or(true) {
				return Ok(());
			}
		}

		// get the difference between the right-hand-side value and the sum of variable
		// lower bounds
		let sum = self
			.terms
			.iter()
			.map(|v| v.lower_bound(ctx))
			.fold(self.max, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the
		// right-hand-side value
		if let Some(r) = self.reification.get() {
			if sum < 0 {
				r.set_val(ctx, false, |ctx: &mut E::PropagationCtx<'_>| {
					self.terms
						.iter()
						.map(|v| v.lower_bound_lit(ctx))
						.collect_vec()
				})?;
			}
			// skip the remaining propagation if the reified variable is not assigned to
			// true
			if !r.val(ctx).unwrap_or(false) {
				return Ok(());
			}
		}

		// propagate the upper bound of the variables
		for (j, v) in self.terms.iter().enumerate() {
			let reason = ctx.deferred_reason(j as u64);
			let ub = sum + v.lower_bound(ctx);
			v.set_upper_bound(ctx, ub, reason)?;
		}
		Ok(())
	}
}

impl IntLinearLessEqImpBounds<IntView, RawLit> {
	/// Create a new [`IntLinearLessEqImpBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = IntView>,
		mut max: IntVal,
		reification: BoolView,
	) where
		E: AddAssign<BoxedPropagator> + InitializationActions + ?Sized,
		IntView: IntInspectionActions<E>,
	{
		let reification = match reification.0 {
			BoolViewInner::Lit(r) => r,
			BoolViewInner::Const(true) => {
				return IntLinearLessEqBounds::<IntView>::new_in(solver, vars, max)
			}
			BoolViewInner::Const(false) => return,
		};
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let Some(c) = v.val(solver) {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		*solver += Box::new(Self {
			terms: vars.clone(),
			max,
			reification: OptField::new(reification),
		});
	}
}

impl IntLinearNotEqImpValue<IntView, RawLit> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = IntView>,
		mut violation: IntVal,
		reification: BoolView,
	) where
		E: AddAssign<BoxedPropagator> + InitializationActions + ?Sized,
		IntView: IntInspectionActions<E>,
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
				if let Some(c) = v.val(solver) {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();
		let num_fixed = solver.new_trailed_int(0);

		*solver += Box::new(Self {
			terms: vars.clone(),
			violation,
			num_fixed,
			reification: OptField::new(reification),
		});
	}
}

impl IntLinearNotEqValue<IntView> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(solver: &mut E, vars: impl IntoIterator<Item = IntView>, mut violation: IntVal)
	where
		E: AddAssign<BoxedPropagator> + InitializationActions + ?Sized,
		IntView: IntInspectionActions<E>,
	{
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = v.val(solver) {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();
		let num_fixed = solver.new_trailed_int(0);

		*solver += Box::new(Self {
			terms: vars.clone(),
			violation,
			num_fixed,
			reification: Default::default(),
		});
	}
}

impl<const R: usize, IV, BV> IntLinearNotEqValueImpl<R, IV, BV> {
	/// Increment the number of decision variables that are fixed, returning
	/// whether the propagator should now be enqueued.
	fn increment_num_fixed<Ctx>(&self, ctx: &mut Ctx) -> bool
	where
		Ctx: TrailingActions,
	{
		let num_fixed = ctx.trailed_int(self.num_fixed) + 1;
		ctx.set_trailed_int(self.num_fixed, num_fixed);
		num_fixed == (self.terms.len() + R - 1) as i64
	}

	/// Helper function to construct the reason for propagation given the index
	/// of the variable in the list of variables to sum or the length of the
	/// list, if explaining the reification.
	fn reason<Ctx, A>(&self, data: usize) -> impl ReasonBuilder<Ctx, A> + '_
	where
		IV: IntDecisionActions<Ctx, Atom = A>,
		BV: Clone + Into<A>,
	{
		move |ctx: &mut Ctx| {
			let mut conj: Vec<_> = self
				.terms
				.iter()
				.enumerate()
				.filter_map(|(i, v)| {
					if data != i {
						Some(v.val_lit(ctx).unwrap())
					} else {
						None
					}
				})
				.collect();
			if let Some(r) = self.reification.get() {
				if data != self.terms.len() {
					conj.push(r.clone().into());
				}
			}
			conj
		}
	}
}

impl<const R: usize, BV, IV, E> Propagator<E> for IntLinearNotEqValueImpl<R, IV, BV>
where
	E: ReasoningEngine,
	E::Atom: SolverBoolView<E> + From<bool>,
	IV: SolverIntView<E>,
	BV: SolverBoolView<E>,
{
	fn advise_of_bool_change(&mut self, ctx: &mut E::NotificationCtx<'_>, _data: u64) -> bool {
		debug_assert!(self.reification.get().is_some());
		debug_assert_eq!(_data, self.terms.len() as u64);
		debug_assert!(self.reification.get().unwrap().val(ctx).is_some());

		self.increment_num_fixed(ctx)
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationCtx<'_>,
		_data: u64,
		_event: IntEvent,
	) -> bool {
		debug_assert!(self.terms[_data as usize].val(ctx).is_some());
		debug_assert_eq!(_event, IntEvent::Fixed);
		self.increment_num_fixed(ctx)
	}
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::High);
		for (i, v) in self.terms.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		if let Some(r) = self.reification.get() {
			r.advise_when_fixed(ctx, self.terms.len() as u64);
		}
	}

	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let (r, r_fixed): (E::Atom, _) = if let Some(r) = self.reification.get() {
			match r.val(ctx) {
				Some(false) => return Ok(()),
				Some(true) => (r.clone().into(), true),
				None => (r.clone().into(), false),
			}
		} else {
			(true.into(), true)
		};
		let mut sum = 0;
		let mut unfixed = None;
		for (i, v) in self.terms.iter().enumerate() {
			if let Some(val) = v.val(ctx) {
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
			v.set_not_eq(ctx, val, self.reason(i))
		} else if sum == self.violation {
			r.set_val(ctx, false, self.reason(self.terms.len()))
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
		constraints::int_linear::{IntLinearLessEqBounds, IntLinearNotEqValue},
		reformulate::InitConfig,
		rel,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		BoolDecision, Model, NonZeroIntVal,
	};

	#[test]
	fn test_constraint_rewriting() {
		// Regression test for GitHub issue 233, where a `int_lin_le_reif` known to be
		// false was rewritten incorrectly. It allowed `a` to be 2.
		let mut prb = Model::default();
		let a = prb.new_int_var(1..=2);
		let r: BoolDecision = false.into();

		rel!(&mut prb, r <-> -2 >= -a);

		prb.expect_solutions(&[a], expect![[r#"1"#]]);
	}

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

		rel!(&mut prb, 10 <= a * 2 + b + c);
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

		rel!(&mut prb, 3 >= a * 2 + b + c);

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

		rel!(&mut prb, r -> 7 <= a * 2 + b + c);

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

		rel!(&mut prb, r -> 5 >= a * 2 + b + c);

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

		rel!(&mut prb, r -> 6 != a * 2 + b + c);

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
}
