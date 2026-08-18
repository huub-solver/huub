//! [`ReasoningEngine::PostingCtx`] to [`Propagator`] implementations when they
//! are posted to a [`Solver`].

//! This module contains the [`PostingContext`] struct, which is used to provide

use std::num::NonZero;

use pindakaas::Var as RawVar;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, InitActions, IntInitActions, IntInspectionActions,
		IntPropCond, ReasoningContext, ReasoningEngine,
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, ActivationActionS},
		decision::Decision,
		engine::{AdvisorDef, AdvisorId, Engine, PropagatorId, State},
		queue::PriorityLevel,
		view::{View, boolean::BoolView, integer::IntView},
	},
	views::{LinearBoolView, LinearView, OffsetView, ScaledView},
};

/// The context given to [`Propagator`] implementations (during
/// [`Propagators::post`]) when added to [`Solver`].
#[derive(Debug)]
pub struct InitializationContext<'a> {
	/// State object of the solver.
	state: &'a mut State,
	/// Internal propagator reference used to add propagator to activations
	/// lists.
	prop: PropagatorId,
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

/// Whether the activation is an advisor of `prop` that was registered with the
/// given data.
fn is_advisor_of(
	advisors: &[AdvisorDef],
	act: ActivationActionS,
	prop: PropagatorId,
	data: u64,
) -> bool {
	match act.into() {
		ActivationAction::<AdvisorId, PropagatorId>::Advise(adv) => {
			let advisor = &advisors[adv.index()];
			advisor.propagator == prop && advisor.data == data
		}
		ActivationAction::Enqueue(_) => false,
	}
}

impl BoolInitActions<InitializationContext<'_>> for Decision<bool> {
	fn advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		if self.val(ctx.state).is_some() {
			// The literal will never change, so we don't need to add an
			// advisor.
			return;
		}
		// Otherwise, add the advisor to the engine
		ctx.add_lit_advisor(*self, data, false);
	}
	fn cancel_advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		ctx.cancel_lit_advisor(*self, data);
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		ctx.cancel_lit_enqueue(*self);
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

	fn cancel_advise_when(
		&self,
		ctx: &mut InitializationContext<'_>,
		condition: IntPropCond,
		data: u64,
	) {
		View::from(*self).cancel_advise_when(ctx, condition, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond) {
		let target = ActivationActionS::from(ActivationAction::<AdvisorId, _>::Enqueue(ctx.prop));
		let _ = ctx.state.int_activation[self.idx()].remove(condition, |act| act == target);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond) {
		if self.val(ctx.state).is_some() {
			ctx.semantic_enqueue = true;
			// No further change will happen, so we don't need to the propagator
			// to any activation lists.
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
		let adv = AdvisorId::new(self.state.advisors.len() - 1);
		self.state
			.bool_activation
			.entry(lit.0.var())
			.or_insert_with(|| {
				self.observed_variables.push(lit.0.var());
				Vec::new()
			})
			.push(ActivationAction::<_, PropagatorId>::Advise(adv).into());
	}

	/// Internal method used to remove an advisor of the propagator being
	/// initialized from the activation list of an integer decision variable.
	fn cancel_int_advisor(&mut self, var: Decision<IntVal>, condition: IntPropCond, data: u64) {
		let prop = self.prop;
		let advisors = &self.state.advisors;
		let _ = self.state.int_activation[var.idx()]
			.remove(condition, |act| is_advisor_of(advisors, act, prop, data));
	}

	/// Internal method used to remove an advisor of the propagator being
	/// initialized from the activation list of a [`RawLit`].
	fn cancel_lit_advisor(&mut self, lit: Decision<bool>, data: u64) {
		let prop = self.prop;
		let advisors = &self.state.advisors;
		let Some(activations) = self.state.bool_activation.get_mut(&lit.0.var()) else {
			return;
		};
		if let Some(pos) = activations
			.iter()
			.position(|&act| is_advisor_of(advisors, act, prop, data))
		{
			let _ = activations.swap_remove(pos);
		}
	}

	/// Internal method used to remove the enqueue subscription of the
	/// propagator being initialized from the activation list of a [`RawLit`].
	fn cancel_lit_enqueue(&mut self, lit: Decision<bool>) {
		let target = ActivationActionS::from(ActivationAction::<AdvisorId, _>::Enqueue(self.prop));
		let Some(activations) = self.state.bool_activation.get_mut(&lit.0.var()) else {
			return;
		};
		if let Some(pos) = activations.iter().position(|&act| act == target) {
			let _ = activations.swap_remove(pos);
		}
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
	/// that will be referred to using [`PropagatorId`].
	pub(crate) fn new(state: &'a mut State, prop: PropagatorId) -> Self {
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

	/// Create a new context to revise the subscriptions of a propagator that
	/// has already been posted.
	///
	/// Unlike [`Self::new`], the context starts from the priority the
	/// propagator was given when it was posted, so that a propagator that does
	/// not set its priority again keeps the one it has.
	pub(crate) fn update(state: &'a mut State, prop: PropagatorId) -> Self {
		let priority = state.propagator_queue.info[prop.index()].priority;
		Self {
			state,
			prop,
			priority,
			semantic_enqueue: false,
			decision_enqueue: None,
			observed_variables: Vec::new(),
		}
	}
}

impl InitActions for InitializationContext<'_> {
	fn advise_on_backtrack(&mut self) {
		// Registering is idempotent, since a propagator is allowed to run its
		// initialization actions again after it has been posted, and a
		// duplicate entry would advise it of every backtrack twice.
		if !self.state.notify_of_backtrack.contains(&self.prop) {
			self.state.notify_of_backtrack.push(self.prop);
		}
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
}

impl IntInitActions<InitializationContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut InitializationContext<'_>, _: IntPropCond, _: u64) {
		// constant will never change, so we don't need to add an
		// advisor.
	}
	fn cancel_advise_when(&self, _: &mut InitializationContext<'_>, _: IntPropCond, _: u64) {
		// A constant never subscribed, so there is nothing to cancel.
	}
	fn cancel_enqueue_when(&self, _: &mut InitializationContext<'_>, _: IntPropCond) {
		// A constant never subscribed, so there is nothing to cancel.
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

	fn cancel_advise_when(&self, ctx: &mut InitializationContext<'a>, _: IntPropCond, data: u64) {
		ctx.cancel_lit_advisor(self.var, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'a>, _: IntPropCond) {
		self.var.cancel_enqueue_when_fixed(ctx);
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
		let cond = self.scale_condition(condition);
		ctx.state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated,
			propagator: ctx.prop,
		});
		let adv = AdvisorId::new(ctx.state.advisors.len() - 1);
		ctx.state.int_activation[self.var.idx()]
			.add(ActivationAction::<_, PropagatorId>::Advise(adv), cond);
	}

	fn cancel_advise_when(
		&self,
		ctx: &mut InitializationContext<'a>,
		condition: IntPropCond,
		data: u64,
	) {
		ctx.cancel_int_advisor(self.var, self.scale_condition(condition), data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		self.var
			.cancel_enqueue_when(ctx, self.scale_condition(condition));
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		self.var.enqueue_when(ctx, self.scale_condition(condition));
	}
}

impl<'a, Var> IntInitActions<InitializationContext<'a>> for OffsetView<IntVal, Var>
where
	Var: IntInitActions<InitializationContext<'a>>,
{
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		self.var.advise_when(ctx, condition, data);
	}

	fn cancel_advise_when(
		&self,
		ctx: &mut InitializationContext<'a>,
		condition: IntPropCond,
		data: u64,
	) {
		self.var.cancel_advise_when(ctx, condition, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		self.var.cancel_enqueue_when(ctx, condition);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		self.var.enqueue_when(ctx, condition);
	}
}

impl IntInitActions<InitializationContext<'_>> for ScaledView<NonZero<IntVal>, Decision<IntVal>> {
	fn advise_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond, data: u64) {
		View::from(*self).advise_when(ctx, condition, data);
	}

	fn cancel_advise_when(
		&self,
		ctx: &mut InitializationContext<'_>,
		condition: IntPropCond,
		data: u64,
	) {
		View::from(*self).cancel_advise_when(ctx, condition, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond) {
		View::from(*self).cancel_enqueue_when(ctx, condition);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond) {
		View::from(*self).enqueue_when(ctx, condition);
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
	fn cancel_advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		match self.0 {
			BoolView::Lit(lit) => lit.cancel_advise_when_fixed(ctx, data),
			BoolView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
			}
		}
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		match self.0 {
			BoolView::Lit(lit) => lit.cancel_enqueue_when_fixed(ctx),
			BoolView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
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
	fn cancel_advise_when(
		&self,
		ctx: &mut InitializationContext<'a>,
		condition: IntPropCond,
		data: u64,
	) {
		match self.0 {
			IntView::Linear(lin) => lin.cancel_advise_when(ctx, condition, data),
			IntView::Bool(lin) => lin.cancel_advise_when(ctx, condition, data),
			IntView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
			}
		}
	}

	fn cancel_enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		match self.0 {
			IntView::Linear(lin) => lin.cancel_enqueue_when(ctx, condition),
			IntView::Bool(lin) => lin.cancel_enqueue_when(ctx, condition),
			IntView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
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
	fn cancel_advise_when_fixed(&self, _: &mut InitializationContext<'_>, _: u64) {
		// A constant never subscribed, so there is nothing to cancel.
	}
	fn cancel_enqueue_when_fixed(&self, _: &mut InitializationContext<'_>) {
		// A constant never subscribed, so there is nothing to cancel.
	}
	fn enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		ctx.semantic_enqueue = true;
	}
}
