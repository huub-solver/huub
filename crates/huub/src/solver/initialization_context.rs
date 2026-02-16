//! [`ReasoningEngine::PostingCtx`] to [`Propagator`] implementations when they
//! are posted to a [`Solver`].

//! This module contains the [`PostingContext`] struct, which is used to provide

use std::num::NonZero;

use pindakaas::Var as RawVar;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, InitActions, IntInitActions, IntInspectionActions,
		ReasoningContext, ReasoningEngine,
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, IntPropCond},
		decision::Decision,
		engine::{AdvRef, AdvisorDef, Engine, PropRef, State},
		queue::PriorityLevel,
		view::{View, boolean::BoolView, integer::IntView},
	},
	views::{LinearBoolView, LinearView, OffsetView},
};

#[derive(Debug)]
/// The context given to [`Propagator`] implementations (during
/// [`Propagators::post`]) when added to [`Solver`].
pub struct InitializationContext<'a> {
	/// State object of the solver.
	state: &'a mut State,
	/// Internal propagator reference used to add propagator to activations
	/// lists.
	prop: PropRef,
	/// The priority level at which the propagator will be enqueued.
	priority: PriorityLevel,
	/// Whether to enqueue `on_change` subscriptions of the propagator would
	/// suggest the propagator should be enqueued.
	semantic_enqueue: bool,
	/// Whether the propagator explicitly requested to be enqueued or not
	/// enqueued.
	decision_enqueue: Option<bool>,
	/// List of Boolean variables to mark as observed
	pub(crate) observed_variables: Vec<RawVar>,
}

impl BoolInitActions<InitializationContext<'_>> for Decision<bool> {
	fn advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		if self.val(ctx.state).is_some() {
			// The literal will never change, so we don't need to add an advisor.
			return;
		}
		// Otherwise, add the advisor to the engine
		ctx.add_lit_advisor(*self, data, false);
	}
	fn enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		if self.val(ctx.state).is_some() {
			ctx.semantic_enqueue = true;
		} else {
			ctx.state
				.bool_activation
				.entry(self.0.var())
				.or_insert_with(|| {
					ctx.observed_variables.push(self.0.var());
					Vec::new()
				})
				.push(ActivationAction::Enqueue(ctx.prop).into());
		}
	}
}

impl BoolInspectionActions<InitializationContext<'_>> for Decision<bool> {
	fn val(&self, ctx: &InitializationContext<'_>) -> Option<bool> {
		self.val(ctx.state)
	}
}

impl IntInitActions<InitializationContext<'_>> for Decision<IntVal> {
	fn advise_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond, data: u64) {
		View::from(*self).advise_when(ctx, condition, data);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond) {
		if self.val(ctx.state).is_some() {
			ctx.semantic_enqueue = true;
			// No further change will happen, so we don't need to the propagator to any
			// activation lists.
			return;
		}
		if condition != IntPropCond::Fixed {
			ctx.semantic_enqueue = true;
		}
		ctx.state.int_activation[self.idx()].add(ActivationAction::Enqueue(ctx.prop), condition);
	}
}

impl IntInspectionActions<InitializationContext<'_>> for Decision<IntVal> {
	fn bounds(&self, ctx: &InitializationContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.state)
	}

	fn domain(&self, ctx: &InitializationContext<'_>) -> IntSet {
		self.domain(ctx.state)
	}

	fn in_domain(&self, ctx: &InitializationContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.state, val)
	}

	fn lit_meaning(
		&self,
		ctx: &InitializationContext<'_>,
		lit: View<bool>,
	) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.state, lit)
	}

	fn max(&self, ctx: &InitializationContext<'_>) -> IntVal {
		self.max(ctx.state)
	}

	fn max_lit(&self, ctx: &InitializationContext<'_>) -> View<bool> {
		self.max_lit(ctx.state)
	}

	fn min(&self, ctx: &InitializationContext<'_>) -> IntVal {
		self.min(ctx.state)
	}

	fn min_lit(&self, ctx: &InitializationContext<'_>) -> View<bool> {
		self.min_lit(ctx.state)
	}

	fn try_lit(
		&self,
		ctx: &InitializationContext<'_>,
		meaning: IntLitMeaning,
	) -> Option<View<bool>> {
		self.try_lit(ctx.state, meaning)
	}

	fn val(&self, ctx: &InitializationContext<'_>) -> Option<IntVal> {
		self.val(ctx.state)
	}
}

impl InitializationContext<'_> {
	/// Internal method used to add an advisor that is triggered when a
	/// [`RawLit`] changes.
	///
	/// Used by [`Solver::advise_on_bool_change`] and
	/// [`Solver::advise_on_int_change`].
	fn add_lit_advisor(&mut self, lit: Decision<bool>, data: u64, bool2int: bool) {
		// Otherwise, add the advisor to the engine
		self.state.advisors.push(AdvisorDef {
			bool2int,
			data,
			negated: false,
			propagator: self.prop,
		});
		let adv = AdvRef::new(self.state.advisors.len() - 1);
		self.state
			.bool_activation
			.entry(lit.0.var())
			.or_insert_with(|| {
				self.observed_variables.push(lit.0.var());
				Vec::new()
			})
			.push(ActivationAction::<_, PropRef>::Advise(adv).into());
	}
}

impl<'a> InitializationContext<'a> {
	/// Returns whether the propagator should be enqueued based on explicit
	/// propagator requests and the semantics of the subscriptions of the
	/// propagator.
	///
	/// Note that when `from_model` is set, the semantic enqueue is ignored, as
	/// it is assumed that the propagator is already at fix-point.
	pub(crate) fn enqueue(&self, from_model: bool) -> bool {
		if let Some(enqueue) = self.decision_enqueue {
			enqueue
		} else if !from_model {
			self.semantic_enqueue
		} else {
			false
		}
	}
	/// Create a new posting context for a [`Solver`] to post a [`Propagator`]
	/// that will be referred to using [`PropRef`].
	pub(crate) fn new(state: &'a mut State, prop: PropRef) -> Self {
		Self {
			state,
			prop,
			priority: PriorityLevel::Medium,
			semantic_enqueue: false,
			decision_enqueue: None,
			observed_variables: Vec::new(),
		}
	}

	/// Returns the propagation priority of the propagator.
	pub(crate) fn priority(&self) -> PriorityLevel {
		self.priority
	}
}

impl InitActions for InitializationContext<'_> {
	fn advise_on_backtrack(&mut self) {
		self.state.notify_of_backtrack.push(self.prop);
	}

	fn enqueue_now(&mut self, option: bool) {
		self.decision_enqueue = Some(option);
	}

	fn set_priority(&mut self, priority: PriorityLevel) {
		self.priority = priority;
	}
}

impl ReasoningContext for InitializationContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl IntInitActions<InitializationContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut InitializationContext<'_>, _: IntPropCond, _: u64) {
		// constant will never change, so we don't need to add an
		// advisor.
	}
	fn enqueue_when(&self, ctx: &mut InitializationContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue = true;
	}
}

impl<'a> IntInitActions<InitializationContext<'a>>
	for LinearBoolView<NonZero<IntVal>, IntVal, Decision<bool>>
{
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, _: IntPropCond, data: u64) {
		ctx.add_lit_advisor(self.var, data, true);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		if condition != IntPropCond::Fixed {
			ctx.semantic_enqueue = true;
		}
		self.var.enqueue_when_fixed(ctx);
	}
}

impl<'a> IntInitActions<InitializationContext<'a>>
	for LinearView<NonZero<IntVal>, IntVal, Decision<IntVal>>
{
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		let negated = self.scale.is_negative();
		let cond = match condition {
			IntPropCond::LowerBound if self.scale.is_negative() => IntPropCond::UpperBound,
			IntPropCond::UpperBound if self.scale.is_negative() => IntPropCond::LowerBound,
			_ => condition,
		};
		ctx.state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated,
			propagator: ctx.prop,
		});
		let adv = AdvRef::new(ctx.state.advisors.len() - 1);
		ctx.state.int_activation[self.var.idx()]
			.add(ActivationAction::<_, PropRef>::Advise(adv), cond);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		let condition = match condition {
			IntPropCond::LowerBound if self.scale.is_negative() => IntPropCond::UpperBound,
			IntPropCond::UpperBound if self.scale.is_negative() => IntPropCond::LowerBound,
			_ => condition,
		};
		self.var.enqueue_when(ctx, condition);
	}
}

impl<'a, Var> IntInitActions<InitializationContext<'a>> for OffsetView<IntVal, Var>
where
	Var: IntInitActions<InitializationContext<'a>>,
{
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		self.var.advise_when(ctx, condition, data);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		self.var.enqueue_when(ctx, condition);
	}
}

impl BoolInitActions<InitializationContext<'_>> for View<bool> {
	fn advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		match self.0 {
			BoolView::Lit(lit) => lit.advise_when_fixed(ctx, data),
			BoolView::Const(_) => {
				// constant will never change, so we don't need to add an
				// advisor.
			}
		}
	}
	fn enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		match self.0 {
			BoolView::Lit(lit) => lit.enqueue_when_fixed(ctx),
			BoolView::Const(_) => {
				ctx.semantic_enqueue = true;
			}
		}
	}
}

impl<'a> IntInitActions<InitializationContext<'a>> for View<IntVal> {
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		match self.0 {
			IntView::Linear(lin) => {
				lin.advise_when(ctx, condition, data);
			}
			IntView::Const(_) => {
				// The variable will never change, so we don't need to add an
				// advisor.
			}
			IntView::Bool(lin) => {
				lin.advise_when(ctx, condition, data);
			}
		}
	}
	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		match self.0 {
			IntView::Const(_) => {
				ctx.semantic_enqueue = true;
				// No further change will happen, so we don't need to add the
				// propagator to any activation lists.
			}
			IntView::Linear(lin) => {
				lin.enqueue_when(ctx, condition);
			}
			IntView::Bool(lin) => {
				lin.enqueue_when(ctx, condition);
			}
		}
	}
}

impl BoolInitActions<InitializationContext<'_>> for bool {
	fn advise_when_fixed(&self, _: &mut InitializationContext<'_>, _: u64) {
		// The literal will never change, so we don't need to add an advisor.
	}
	fn enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		ctx.semantic_enqueue = true;
	}
}
