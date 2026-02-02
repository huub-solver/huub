//! Structures and algorithms  for the integer linear constraint, including
//! `int_lin_eq`, `int_lin_le`, `int_lin_ne` and their reification. These
//! constraint enforce a condition on the sum of (linear transformations of)
//! integer decision variables.

use std::{any::TypeId, num::NonZero};

use itertools::{Either, Itertools};
use pindakaas::{
	Lit as RawLit, Unsatisfiable,
	bool_linear::{BoolLinAggregator, BoolLinExp, BoolLinVariant, BoolLinear},
};

use crate::{
	Conjunction, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions,
		InitActions, IntDecisionActions, IntInitActions, IntInspectionActions,
		IntPropagationActions, IntSimplificationActions, PostingActions, PropagationActions,
		ReasoningContext, ReasoningEngine, SimplificationActions, Trailed, TrailingActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, IntModelActions, IntSolverActions,
		Propagator, ReasonBuilder, SimplificationStatus,
	},
	helpers::{
		overflow::{OverflowImpossible, OverflowMode, OverflowPossible},
		true_type::True,
	},
	lower::{LoweringContext, LoweringError},
	model::{self, expressions::bool_formula::BoolFormula},
	solver::{
		self, BoolView, Decision, IntLitMeaning,
		activation_list::{IntEvent, IntPropCond},
		queue::PriorityLevel,
		view::integer::IntView,
	},
	views::LinearBoolView,
};

/// A type with double the amount of bits of [`IntVal`], allowing for large
/// intermediate value computation.
type DoubleIntVal = i128;

/// Representation of an integer equality constraint that cannot be unified.
///
/// This constraint enforces that two integer decisions take the same value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct IntEq {
	/// The two integer decisions that must be equal.
	pub(crate) vars: [model::View<IntVal>; 2],
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of an integer linear constraint within a model.
///
/// This constraint enforces that a sum of (linear transformations of) integer
/// decision variables is less than, equal, or not equal to a constant value, or
/// the implication or reification or whether this is so.
pub struct IntLinear<OF: OverflowMode> {
	/// The integer linear terms that are being summed.
	pub(crate) terms: Vec<model::View<IntVal>>,
	/// The operator that is used to compare the sum to the right-hand side.
	pub(crate) comparator: LinComparator,
	/// The constant right-hand side value.
	pub(crate) rhs: OF::Accumulator,
	/// Boolean decision variable that (half-)reifies the constraint, if any.
	pub(crate) reif: Option<Reification>,
}

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqBounds<OV, IV> = IntLinearLessEqBoundsImpl<OV, IV, True>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
pub struct IntLinearLessEqBoundsImpl<OV: OverflowMode, IV, BV> {
	/// Variables that are being summed
	terms: Vec<IV>,
	/// Maximum value of the sum can take
	max: OV::Accumulator,
	/// Reified variable, if any
	reification: BV,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqImpBounds<OV, IV, BV> = IntLinearLessEqBoundsImpl<OV, IV, BV>;

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqImpValue<OF, IV, BV> = IntLinearNotEqValueImpl<OF, IV, BV>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqValue<OF, IV> = IntLinearNotEqValueImpl<OF, IV, True>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
pub struct IntLinearNotEqValueImpl<OF: OverflowMode, IV, BV> {
	/// Decision variables in the summation
	terms: Vec<IV>,
	/// Number of decision variables that have been not yet been fixed to a
	/// single value
	num_free: Trailed<usize>,
	/// The value the summation should not equal
	violation: OF::Accumulator,
	/// Reified variable, if any
	reification: BV,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Possible operators that can be used for in a linear constraint.
pub(crate) enum LinComparator {
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
	ImpliedBy(model::View<bool>),
	/// The constraint is reified by the given [`BoolDecision`].
	ReifiedBy(model::View<bool>),
}

impl<E> Constraint<E> for IntEq
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
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

	fn to_solver(&self, actions: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let lin = IntLinear::<OverflowPossible> {
			terms: vec![self.vars[0], -self.vars[1]],
			comparator: LinComparator::Equal,
			rhs: 0,
			reif: None,
		};
		<_ as Constraint<E>>::to_solver(&lin, actions)
	}
}

impl<E> Propagator<E> for IntEq
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		for iv in self.vars {
			iv.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// Channel bounds of self.vars[0] to self.vars[1]
		self.vars[0].tighten_min(ctx, self.vars[1].min(ctx), [self.vars[1].min_lit(ctx)])?;
		self.vars[0].tighten_max(ctx, self.vars[1].max(ctx), [self.vars[1].max_lit(ctx)])?;

		// Channel bounds of self.vars[1] to self.vars[0]
		self.vars[1].tighten_min(ctx, self.vars[0].min(ctx), [self.vars[0].min_lit(ctx)])?;
		self.vars[1].tighten_max(ctx, self.vars[0].max(ctx), [self.vars[0].max_lit(ctx)])?;
		Ok(())
	}
}

impl<OF: OverflowMode> IntLinear<OF> {
	/// Internal method to negate the linear constraint.
	fn negate<Ctx>(self, ctx: &mut Ctx) -> Result<Self, Ctx::Conflict>
	where
		Ctx: ReasoningContext + ?Sized,
		model::View<IntVal>: IntPropagationActions<Ctx>,
	{
		Ok(match self.comparator {
			LinComparator::Equal => Self {
				comparator: LinComparator::NotEqual,
				..self
			},
			LinComparator::LessEq => Self {
				terms: self
					.terms
					.into_iter()
					.map(|v| v.bounding_neg(ctx))
					.try_collect()?,
				rhs: -self.rhs - 1.into(),
				..self
			},
			LinComparator::NotEqual => Self {
				comparator: LinComparator::Equal,
				..self
			},
		})
	}

	/// Try to convert the integer linear constraint into a [`BoolLinear`]
	/// constraint, where the given terms are the [`IntView`] representations of
	/// the [`IntDecision`] terms in `self`.
	///
	/// This only succeeds if the linear constraint is not implied, all terms
	/// are [`BoolLinView`]s, and the comparator is not
	/// [`LinOperator::NotEqual`].
	fn try_bool_lin(&self, terms: &[solver::View<IntVal>]) -> Option<BoolLinear> {
		if self.reif.is_some() || self.comparator == LinComparator::NotEqual {
			return None;
		}

		let mut offset = OF::Accumulator::from(0);
		let terms: Vec<(RawLit, IntVal)> = terms
			.iter()
			.map(|&v| {
				if let IntView::Bool(lin) = v.0 {
					offset += lin.offset.into();
					Ok((lin.var.0, lin.scale.into()))
				} else {
					Err(())
				}
			})
			.collect::<Result<_, ()>>()
			.ok()?;
		let rhs = (self.rhs - offset).try_into().ok()?;

		let bool_lin = BoolLinExp::from_terms(&terms);
		let bool_lin = BoolLinear::new(
			bool_lin,
			match self.comparator {
				LinComparator::Equal => pindakaas::bool_linear::Comparator::Equal,
				LinComparator::LessEq => pindakaas::bool_linear::Comparator::LessEq,
				LinComparator::NotEqual => unreachable!(),
			},
			rhs,
		);
		Some(bool_lin)
	}
}

impl IntLinear<OverflowPossible> {
	/// Returns whether the given terms that are summed in integer linear
	/// expressions can overflow.
	///
	/// Note that the order of the terms matters. If the terms are reordered,
	/// then the result of this method may change.
	pub(crate) fn can_overflow<Ctx, IV>(ctx: &Ctx, terms: &[IV]) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		IV: IntInspectionActions<Ctx>,
	{
		let mut acc_min: IntVal = 0;
		let mut acc_max: IntVal = 0;
		for iv in terms {
			let (lb, ub) = iv.bounds(ctx);
			if let Some(min) = acc_min.checked_sub(lb) {
				acc_min = min;
			} else {
				return true;
			}
			if let Some(max) = acc_max.checked_add(ub) {
				acc_max = max;
			} else {
				return true;
			}
		}
		false
	}
}

impl<E, OF> Constraint<E> for IntLinear<OF>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
	OF: OverflowMode,
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
					ctx.post_constraint(lin);
					return Ok(SimplificationStatus::Subsumed);
				}
				Some(false) => {
					if matches!(self.reif.unwrap(), Reification::ReifiedBy(_)) {
						let mut lin = self.clone().negate(ctx)?;
						lin.reif = None;
						ctx.post_constraint(lin);
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
		self.rhs -= vals.into_iter().map(OF::Accumulator::from).sum();

		// Perform single-term domain changes and any possible unification
		match *self.terms.as_slice() {
			[var] if self.reif.is_none() => {
				match (self.comparator, self.rhs.try_into()) {
					(LinComparator::Equal, Ok(rhs)) => var.fix(ctx, rhs, [])?,
					(LinComparator::Equal, Err(_)) => return Err(ctx.declare_conflict([])),
					(LinComparator::LessEq, Ok(rhs)) => var.tighten_max(ctx, rhs, [])?,
					(LinComparator::LessEq, Err(_)) if self.rhs < IntVal::MIN.into() => {
						return Err(ctx.declare_conflict([]));
					}
					(LinComparator::LessEq, Err(_)) => {
						debug_assert!(self.rhs > IntVal::MAX.into());
					}
					(LinComparator::NotEqual, Ok(rhs)) => var.remove_val(ctx, rhs, [])?,
					(LinComparator::NotEqual, Err(_)) => {}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[var] => {
				let lit = match (self.comparator, self.rhs.try_into()) {
					(LinComparator::Equal, Ok(rhs)) => var.eq(rhs),
					(LinComparator::Equal, Err(_)) => false.into(),
					(LinComparator::LessEq, Ok(rhs)) => var.leq(rhs),
					(LinComparator::LessEq, Err(_)) if self.rhs < IntVal::MIN.into() => {
						false.into()
					}
					(LinComparator::LessEq, Err(_)) => {
						debug_assert!(self.rhs > IntVal::MAX.into());
						true.into()
					}
					(LinComparator::NotEqual, Ok(rhs)) => var.ne(rhs),
					(LinComparator::NotEqual, Err(_)) => false.into(),
				};
				match self.reif.unwrap() {
					Reification::ImpliedBy(r) => ctx.post_constraint(BoolFormula::Implies(
						Box::new(BoolFormula::Atom(r)),
						Box::new(BoolFormula::Atom(lit)),
					)),
					Reification::ReifiedBy(r) => r.unify(ctx, lit)?,
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[a, b] if self.comparator == LinComparator::Equal && self.reif.is_none() => {
				match self.rhs.try_into() {
					Ok(rhs) => {
						let b = b.bounding_neg(ctx)?.bounding_add(ctx, rhs)?;
						a.unify(ctx, b)?;
					}
					Err(_) => {
						// TODO: might be incorrect
						return Err(ctx.declare_conflict([]));
					}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Collect variable bounds and create their sums
		let lb = self.terms.iter().map(|v| v.min(ctx)).collect_vec();
		let ub = self.terms.iter().map(|v| v.max(ctx)).collect_vec();

		let lb_sum: OF::Accumulator = lb.iter().copied().map(OF::Accumulator::from).sum();
		let ub_sum: OF::Accumulator = ub.iter().copied().map(OF::Accumulator::from).sum();

		// Check if the constraint is already known to be true or false
		let known_result = match self.comparator {
			LinComparator::Equal if lb_sum > self.rhs || ub_sum < self.rhs => Some(false),
			LinComparator::Equal if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(true)
			}
			LinComparator::LessEq if ub_sum <= self.rhs => Some(true),
			LinComparator::LessEq if lb_sum > self.rhs => Some(false),
			LinComparator::NotEqual if lb_sum > self.rhs || ub_sum < self.rhs => Some(true),
			LinComparator::NotEqual if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(false)
			}
			_ => None,
		};
		let fail_reason = |ctx: &mut E::PropagationCtx<'_>| {
			self.terms
				.iter()
				.map(|v| match self.comparator {
					LinComparator::Equal if lb_sum > self.rhs => v.min_lit(ctx),
					LinComparator::Equal if ub_sum < self.rhs => v.max_lit(ctx),
					LinComparator::LessEq => v.min_lit(ctx),
					LinComparator::NotEqual => v.val_lit(ctx).unwrap(),
					_ => unreachable!(),
				})
				.collect_vec()
		};

		if let Some(satisfied) = known_result {
			return match self.reif {
				Some(Reification::ImpliedBy(r)) => {
					if !satisfied {
						r.fix(ctx, false, fail_reason)?;
					}
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) if satisfied => {
					r.require(ctx, |ctx: &mut E::PropagationCtx<'_>| {
						self.terms
							.iter()
							.flat_map(|v| match self.comparator {
								LinComparator::NotEqual if lb_sum > self.rhs => {
									vec![v.min_lit(ctx)]
								}
								LinComparator::NotEqual if ub_sum < self.rhs => {
									vec![v.max_lit(ctx)]
								}
								LinComparator::LessEq => vec![v.max_lit(ctx)],
								LinComparator::NotEqual => {
									vec![v.min_lit(ctx), v.max_lit(ctx)]
								}
								_ => unreachable!(),
							})
							.collect_vec()
					})?;
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) => {
					debug_assert!(!satisfied);
					r.fix(ctx, false, fail_reason)?;
					Ok(SimplificationStatus::Subsumed)
				}
				None if !satisfied => Err(ctx.declare_conflict(fail_reason)),
				None => Ok(SimplificationStatus::Subsumed),
			};
		} else if self.comparator == LinComparator::NotEqual {
			// No further bounds propagation possible
			return Ok(SimplificationStatus::NoFixpoint);
		}

		// The difference between the right-hand-side value and the sum of the lower
		// bounds. The current lower bound plus this difference is an upper bound
		// for each variable.
		let lb_diff = self.rhs - lb_sum;
		// Propagate the upper bounds of the variables
		for (i, v) in self.terms.iter().enumerate() {
			let lb_i = lb[i].into();
			let new_ub = lb_diff + lb_i;
			let reason = |ctx: &mut E::PropagationCtx<'_>| {
				self.terms
					.iter()
					.enumerate()
					.filter(|&(j, _)| j != i)
					.map(|(_, w)| w.min_lit(ctx))
					.collect_vec()
			};
			if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
				if lb_i > new_ub {
					r.fix(ctx, false, reason)?;
					return Ok(SimplificationStatus::Subsumed);
				}
			} else {
				match new_ub.try_into() {
					Ok(new_ub) => v.tighten_max(ctx, new_ub, reason)?,
					Err(_) if new_ub < IntVal::MIN.into() => return Err(ctx.declare_conflict([])),
					Err(_) => {
						debug_assert!(new_ub > IntVal::MAX.into());
					}
				}
			}
		}

		// For equality constraints, propagate the lower bounds of the variables
		if self.comparator == LinComparator::Equal {
			if lb_sum == ub_sum {
				assert_eq!(lb_sum, self.rhs);
				return Ok(SimplificationStatus::Subsumed);
			}

			// The amount the sum of the upper bounds exceeds the right-hand-side
			// value (negated). Used to propagate lower bounds of each variable.
			let ub_diff = self.rhs - ub_sum;
			for (i, v) in self.terms.iter().enumerate() {
				let ub_i = ub[i].into();
				let new_lb = ub_diff + ub_i;
				let reason = |ctx: &mut E::PropagationCtx<'_>| {
					self.terms
						.iter()
						.enumerate()
						.filter(|&(j, _)| j != i)
						.map(|(_, &w)| w.max_lit(ctx))
						.collect_vec()
				};
				if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
					if ub_i < new_lb {
						r.fix(ctx, false, reason)?;
						return Ok(SimplificationStatus::Subsumed);
					}
				} else {
					match new_lb.try_into() {
						Ok(new_lb) => v.tighten_min(ctx, new_lb, reason)?,
						Err(_) if new_lb > IntVal::MAX.into() => {
							return Err(ctx.declare_conflict([]));
						}
						Err(_) => {
							debug_assert!(new_lb < IntVal::MAX.into());
						}
					}
				}

				// We create a negated view in [`Self::to_solver`], ensure that it is correctly
				// bounded.
				let _ = v.bounding_neg(ctx)?;
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		use Reification::*;

		let terms = self.terms.iter().map(|&v| slv.solver_view(v)).collect_vec();
		let r = self.reif.as_ref().map(|&r| {
			slv.solver_view(match r {
				ImpliedBy(r) | ReifiedBy(r) => r,
			})
		});
		let full_reif = matches!(self.reif, Some(ReifiedBy(_)));

		// Detect Pseudo-Boolean constraints, and simplify them if possible.
		let (terms, operator, rhs) = if let Some(bool_lin) = self.try_bool_lin(&terms) {
			let map_cmp = |cmp| match cmp {
				pindakaas::bool_linear::Comparator::Equal => LinComparator::Equal,
				pindakaas::bool_linear::Comparator::LessEq => LinComparator::LessEq,
				pindakaas::bool_linear::Comparator::GreaterEq => unreachable!(),
			};

			let (op, lin) = match BoolLinAggregator::default().aggregate(slv, &bool_lin) {
				Err(Unsatisfiable) => return Err(slv.error.take().unwrap()),
				Ok(BoolLinVariant::Cardinality(card)) => (map_cmp(card.comparator()), card.into()),
				Ok(BoolLinVariant::CardinalityOne(card))
					if card.comparator() == pindakaas::bool_linear::Comparator::Equal =>
				{
					slv.add_clause(card.iter_lits().map(Decision))?;
					(LinComparator::LessEq, card.into())
				}
				Ok(BoolLinVariant::CardinalityOne(card)) => (LinComparator::LessEq, card.into()),
				Ok(BoolLinVariant::Linear(lin)) => (map_cmp(lin.comparator()), lin),
				Ok(BoolLinVariant::Trivial) => return Ok(()),
			};
			(
				lin.iter_terms()
					.map(|(lit, coeff)| {
						LinearBoolView::new(NonZero::new(coeff).unwrap(), 0, Decision(lit)).into()
					})
					.collect_vec(),
				op,
				lin.rhs().into(),
			)
		} else {
			(terms, self.comparator, self.rhs)
		};

		let negate_terms = |terms: &[solver::View<IntVal>]| terms.iter().map(|&v| -v).collect_vec();

		match (operator, r) {
			(LinComparator::Equal, None) => {
				// coeffs * vars >= c <=> -coeffs * vars <= -c
				IntLinearLessEqBounds::post(slv, negate_terms(&terms), -rhs);
				// coeffs * vars <= c
				IntLinearLessEqBounds::post(slv, terms.clone(), rhs);
			}
			(LinComparator::Equal, Some(r)) => {
				if full_reif {
					IntLinearNotEqImpValue::<_, _, Decision<bool>>::post(
						slv,
						terms.clone(),
						rhs,
						!r,
					);
				}
				IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(
					slv,
					negate_terms(&terms),
					-rhs,
					r,
				);
				IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(slv, terms, rhs, r);
			}
			(LinComparator::LessEq, None) => {
				IntLinearLessEqBounds::post(slv, terms, rhs);
			}
			(LinComparator::LessEq, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(
						slv,
						negate_terms(&terms),
						-(rhs + 1.into()),
						!r,
					);
				}
				IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(slv, terms, rhs, r);
			}
			(LinComparator::NotEqual, None) => {
				IntLinearNotEqValue::post(slv, terms, rhs);
			}
			(LinComparator::NotEqual, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(
						slv,
						terms.clone(),
						rhs,
						!r,
					);
					IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(
						slv,
						negate_terms(&terms),
						-rhs,
						!r,
					);
				}
				IntLinearNotEqImpValue::<_, _, Decision<bool>>::post(slv, terms, rhs, r);
			}
		}
		Ok(())
	}
}

impl<E, OF> Propagator<E> for IntLinear<OF>
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
	model::View<bool>: BoolSolverActions<E>,
	OF: OverflowMode,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
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

impl IntLinearLessEqBounds<OverflowPossible, solver::View<IntVal>> {
	/// Create a new [`IntLinearLessEqBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let mut max = max.into();
		let vars: Vec<solver::View<IntVal>> = vars
			.into_iter()
			.filter(|v| {
				if let Some(c) = v.val(solver) {
					max -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();

		solver.add_propagator(Box::new(Self {
			terms: vars.clone(),
			max,
			reification: True,
		}));
	}
}

impl<OF, BV, E, IV> Propagator<E> for IntLinearLessEqBoundsImpl<OF, IV, BV>
where
	OF: OverflowMode,
	E: ReasoningEngine,
	BV: BoolSolverActions<E>,
	IV: IntSolverActions<E>,
	E::Atom: BoolSolverActions<E>,
{
	fn explain(
		&mut self,
		ctx: &mut E::ExplanationCtx<'_>,
		_: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let i = data as usize;
		let const_true: bool = TypeId::of::<BV>() == TypeId::of::<True>();
		debug_assert!(i <= self.terms.len());
		debug_assert!(!const_true || i < self.terms.len());

		let mut conj = Vec::with_capacity(self.terms.len() - const_true as usize);
		for (j, t) in self.terms.iter().enumerate() {
			if j != i {
				conj.push(t.min_lit(ctx));
			}
		}
		if !const_true && i < self.terms.len() {
			conj.push(self.reification.clone().into());
		}
		conj
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in self.terms.iter() {
			v.enqueue_when(ctx, IntPropCond::LowerBound);
		}
		self.reification.enqueue_when_fixed(ctx);
	}

	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].lower_bound
	#[tracing::instrument(name = "int_lin_le", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// If the reified variable is false, skip propagation
		let r_val = self.reification.val(ctx);
		if r_val == Some(false) {
			return Ok(());
		}

		// Compute the sum of the lower bounds of all terms
		let lb_sum = self
			.terms
			.iter()
			.map(|v| OF::Accumulator::from(v.min(ctx)))
			.sum();

		if TypeId::of::<BV>() != TypeId::of::<True>() {
			// Propagate the reified variable if the sum of lower bounds is greater than the
			// right-hand-side value
			if lb_sum > self.max {
				self.reification
					.fix(ctx, false, |ctx: &mut E::PropagationCtx<'_>| {
						self.terms.iter().map(|v| v.min_lit(ctx)).collect_vec()
					})?;
			}
		}

		// skip the remaining propagation if the reified variable is not assigned to
		// true
		if r_val != Some(true) {
			return Ok(());
		}

		// propagate the upper bound of the variables
		for (j, v) in self.terms.iter().enumerate() {
			let reason = ctx.deferred_reason(j as u64);
			let ub = (self.max - lb_sum) + v.min(ctx).into();
			match ub.try_into() {
				Ok(ub) => v.tighten_max(ctx, ub, reason)?,
				Err(_) if ub < IntVal::MIN.into() => v
					.lit(ctx, IntLitMeaning::Less(IntVal::MIN))
					.require(ctx, reason)?,
				Err(_) => {
					debug_assert!(ub > v.max(ctx).into());
				}
			}
		}
		Ok(())
	}
}

impl IntLinearLessEqImpBounds<OverflowPossible, solver::View<IntVal>, Decision<bool>> {
	/// Create a new [`IntLinearLessEqImpBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
		reification: solver::View<bool>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let mut max = max.into();
		let reification = match reification.0 {
			BoolView::Lit(r) => r,
			BoolView::Const(true) => {
				return IntLinearLessEqBounds::post(solver, vars, max);
			}
			BoolView::Const(false) => return,
		};
		let vars: Vec<_> = vars
			.into_iter()
			.filter(|v| {
				if let Some(c) = v.val(solver) {
					max -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();

		solver.add_propagator(Box::new(Self {
			terms: vars.clone(),
			max,
			reification,
		}));
	}
}

impl IntLinearNotEqImpValue<OverflowPossible, solver::View<IntVal>, Decision<bool>> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		violation: impl Into<DoubleIntVal>,
		reification: solver::View<bool>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
		solver::View<bool>: BoolInspectionActions<E>,
	{
		let mut violation = violation.into();
		let reification = match reification.val(solver) {
			None => {
				let BoolView::Lit(r) = reification.0 else {
					unreachable!()
				};
				r
			}
			Some(true) => {
				return IntLinearNotEqValue::<OverflowPossible, _>::post(solver, vars, violation);
			}
			Some(false) => return,
		};

		let vars: Vec<_> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = v.val(solver) {
					violation -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();
		let num_free = solver.new_trailed(vars.len() + 1);

		if IntLinear::can_overflow(solver, &vars) || IntVal::try_from(violation).is_err() {
			solver.add_propagator(Box::new(IntLinearNotEqImpValue::<OverflowPossible, _, _> {
				terms: vars.clone(),
				violation,
				num_free,
				reification,
			}));
		} else {
			solver.add_propagator(Box::new(
				IntLinearNotEqImpValue::<OverflowImpossible, _, _> {
					terms: vars.clone(),
					violation: violation as IntVal,
					num_free,
					reification,
				},
			));
		}
	}
}

impl IntLinearNotEqValue<OverflowPossible, solver::View<IntVal>> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		violation: impl Into<DoubleIntVal>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let mut violation = violation.into();
		let vars: Vec<_> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = v.val(solver) {
					violation -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();
		let num_free = solver.new_trailed(vars.len());

		if IntLinear::can_overflow(solver, &vars) || IntVal::try_from(violation).is_err() {
			solver.add_propagator(Box::new(IntLinearNotEqValue::<OverflowPossible, _> {
				terms: vars.clone(),
				violation,
				num_free,
				reification: True,
			}));
		} else {
			solver.add_propagator(Box::new(IntLinearNotEqValue::<OverflowImpossible, _> {
				terms: vars.clone(),
				violation: violation as IntVal,
				num_free,
				reification: True,
			}));
		}
	}
}

impl<OF, IV, BV> IntLinearNotEqValueImpl<OF, IV, BV>
where
	OF: OverflowMode,
{
	/// Increment the number of decision variables that are fixed, returning
	/// whether the propagator should now be enqueued.
	fn decrement_num_free<Ctx>(&self, ctx: &mut Ctx) -> bool
	where
		Ctx: TrailingActions,
	{
		let num_free = ctx.trailed(self.num_free);
		debug_assert!(num_free >= 1);
		let num_free = num_free - 1;
		ctx.set_trailed(self.num_free, num_free);
		num_free <= 1
	}

	/// Helper function to construct the reason for propagation given the index
	/// of the variable in the list of variables to sum or the length of the
	/// list, if explaining the reification.
	fn reason<Ctx>(&self, data: usize) -> impl ReasonBuilder<Ctx> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		IV: IntDecisionActions<Ctx>,
		BV: Clone + Into<Ctx::Atom> + 'static,
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
			if TypeId::of::<BV>() != TypeId::of::<True>() && data != self.terms.len() {
				conj.push(self.reification.clone().into());
			}
			conj
		}
	}
}

impl<OF, BV, IV, E> Propagator<E> for IntLinearNotEqValueImpl<OF, IV, BV>
where
	OF: OverflowMode,
	E: ReasoningEngine,
	E::Atom: BoolSolverActions<E> + From<bool>,
	IV: IntSolverActions<E>,
	BV: BoolSolverActions<E>,
{
	fn advise_of_bool_change(&mut self, ctx: &mut E::NotificationCtx<'_>, _data: u64) -> bool {
		debug_assert_ne!(TypeId::of::<BV>(), TypeId::of::<True>());
		debug_assert_eq!(_data, self.terms.len() as u64);
		debug_assert!(self.reification.val(ctx).is_some());

		self.decrement_num_free(ctx)
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationCtx<'_>,
		_data: u64,
		_event: IntEvent,
	) -> bool {
		debug_assert!(self.terms[_data as usize].val(ctx).is_some());
		debug_assert_eq!(_event, IntEvent::Fixed);
		self.decrement_num_free(ctx)
	}
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::High);
		for (i, v) in self.terms.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		self.reification
			.advise_when_fixed(ctx, self.terms.len() as u64);
	}

	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		let r_fixed = match self.reification.val(ctx) {
			Some(false) => return Ok(()),
			Some(true) => true,
			None => false,
		};

		let mut sum = OF::Accumulator::from(0);
		let mut unfixed = None;
		for (i, v) in self.terms.iter().enumerate() {
			if let Some(val) = v.val(ctx) {
				sum += val.into();
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
			if let Ok(val) = val.try_into() {
				v.remove_val(ctx, val, self.reason(i))?;
			}
			Ok(())
		} else if sum == self.violation {
			self.reification
				.fix(ctx, false, self.reason(self.terms.len()))
		} else {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use expect_test::expect;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		IntVal, Model,
		constraints::int_linear::{DoubleIntVal, IntLinearLessEqBounds, IntLinearNotEqValue},
		lower::InitConfig,
		model::view::View,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	fn double_int_val() {
		assert_eq!(size_of::<DoubleIntVal>(), 2 * size_of::<IntVal>());
	}

	#[test]
	fn test_constraint_rewriting() {
		// Regression test for GitHub issue 233, where a `int_lin_le_reif` known to be
		// false was rewritten incorrectly. It allowed `a` to be 2.
		let mut prb = Model::default();
		let a = prb.new_int_decision(1..=2);
		let r: View<bool> = false.into();

		prb.linear(-a).le(-2).reified_by(r).post();

		prb.expect_solutions(&[a], expect![[r#"1"#]]);
	}

	#[test]
	#[traced_test]
	fn test_linear_ge_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::post(&mut slv, vec![a * NonZero::new(-2).unwrap(), -b, -c], -6);

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
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c).ge(10).post();
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_le_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::post(&mut slv, vec![a * NonZero::new(2).unwrap(), b, c], 6);

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
		let a = prb.new_int_decision(1..=4);
		let b = prb.new_int_decision(1..=4);
		let c = prb.new_int_decision(1..=4);

		prb.linear(a * 2 + b + c).le(3).post();

		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntLinearNotEqValue::post(&mut slv, vec![a * NonZero::new(2).unwrap(), b, c], 6);

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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c).ge(7).implied_by(r).post();

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c).le(5).implied_by(r).post();

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c).ne(6).implied_by(r).post();

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
