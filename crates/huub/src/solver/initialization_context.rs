//! This module contains the [`PostingContext`] struct, which is used to provide
//! [`ReasoningEngine::PostingCtx`] to [`Propagator`] implementations when they
//! are posted to a [`Solver`].

use std::num::NonZero;

use pindakaas::{Lit as RawLit, Var as RawVar};

use crate::{
	actions::{
		BoolInitActions, BoolInspectionActions, InitActions, IntInitActions, IntInspectionActions,
		ReasoningContext, ReasoningEngine,
	},
	solver::{
		activation_list::{ActivationAction, IntPropCond},
		engine::{AdvisorDef, Engine, PropRef, State},
		int_var::IntVarRef,
		queue::PriorityLevel,
		BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner,
	},
	views::{linear_bool_view::LinearBoolView, linear_view::LinearView, offset_view::OffsetView},
	IntSetVal, IntVal,
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

impl BoolInitActions<InitializationContext<'_>> for BoolView {
	fn advise_when_fixed(&self, ctx: &mut InitializationContext<'_>, data: u64) {
		match self.0 {
			BoolViewInner::Lit(lit) => lit.advise_when_fixed(ctx, data),
			BoolViewInner::Const(_) => {
				// constant will never change, so we don't need to add an
				// advisor.
			}
		}
	}
	fn enqueue_when_fixed(&self, ctx: &mut InitializationContext<'_>) {
		match self.0 {
			BoolViewInner::Lit(lit) => lit.enqueue_when_fixed(ctx),
			BoolViewInner::Const(_) => {
				ctx.semantic_enqueue = true;
			}
		}
	}
}

impl InitializationContext<'_> {
	/// Internal method used to add an advisor that is triggered when a
	/// [`RawLit`] changes.
	///
	/// Used by [`Solver::advise_on_bool_change`] and
	/// [`Solver::advise_on_int_change`].
	fn add_lit_advisor(&mut self, lit: RawLit, data: u64, bool2int: bool) {
		// Otherwise, add the advisor to the engine
		let adv = self.state.advisors.push(AdvisorDef {
			bool2int,
			data,
			negated: false,
			propagator: self.prop,
		});
		self.state
			.bool_activation
			.entry(lit.var())
			.or_insert_with(|| {
				self.observed_variables.push(lit.var());
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

impl IntInitActions<InitializationContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut InitializationContext<'_>, _: IntPropCond, _: u64) {
		// constant will never change, so we don't need to add an
		// advisor.
	}
	fn enqueue_when(&self, ctx: &mut InitializationContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue = true;
	}
}

impl IntInitActions<InitializationContext<'_>> for IntVarRef {
	fn advise_when(&self, ctx: &mut InitializationContext<'_>, condition: IntPropCond, data: u64) {
		IntView(IntViewInner::Linear((*self).into())).advise_when(ctx, condition, data);
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
		ctx.state.int_activation[*self].add(ActivationAction::Enqueue(ctx.prop), condition);
	}
}

impl IntInspectionActions<InitializationContext<'_>> for IntVarRef {
	fn domain(&self, ctx: &InitializationContext<'_>) -> IntSetVal {
		self.domain(ctx.state)
	}

	fn in_domain(&self, ctx: &InitializationContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.state, val)
	}

	fn lit_meaning(&self, ctx: &InitializationContext<'_>, lit: BoolView) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.state, lit)
	}

	fn lower_bound(&self, ctx: &InitializationContext<'_>) -> IntVal {
		self.lower_bound(ctx.state)
	}

	fn lower_bound_lit(&self, ctx: &InitializationContext<'_>) -> BoolView {
		self.lower_bound_lit(ctx.state)
	}

	fn try_lit(&self, ctx: &InitializationContext<'_>, meaning: IntLitMeaning) -> Option<BoolView> {
		self.try_lit(ctx.state, meaning)
	}

	fn upper_bound(&self, ctx: &InitializationContext<'_>) -> IntVal {
		self.upper_bound(ctx.state)
	}

	fn upper_bound_lit(&self, ctx: &InitializationContext<'_>) -> BoolView {
		self.upper_bound_lit(ctx.state)
	}

	fn bounds(&self, ctx: &InitializationContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.state)
	}

	fn val(&self, ctx: &InitializationContext<'_>) -> Option<IntVal> {
		self.val(ctx.state)
	}
}

impl<'a> IntInitActions<InitializationContext<'a>> for IntView {
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		match self.0 {
			IntViewInner::Linear(lin) => {
				lin.advise_when(ctx, condition, data);
			}
			IntViewInner::Const(_) => {
				// The variable will never change, so we don't need to add an
				// advisor.
			}
			IntViewInner::Bool(lin) => {
				lin.advise_when(ctx, condition, data);
			}
		}
	}
	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		match self.0 {
			IntViewInner::Const(_) => {
				ctx.semantic_enqueue = true;
				// No further change will happen, so we don't need to add the
				// propagator to any activation lists.
			}
			IntViewInner::Linear(lin) => {
				lin.enqueue_when(ctx, condition);
			}
			IntViewInner::Bool(lin) => {
				lin.enqueue_when(ctx, condition);
			}
		}
	}
}

impl<'a> IntInitActions<InitializationContext<'a>>
	for LinearBoolView<NonZero<IntVal>, IntVal, RawLit>
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
	for LinearView<NonZero<IntVal>, IntVal, IntVarRef>
{
	fn advise_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond, data: u64) {
		let negated = self.scale.get() < 0;
		let cond = match condition {
			IntPropCond::LowerBound if self.scale.get() < 0 => IntPropCond::UpperBound,
			IntPropCond::UpperBound if self.scale.get() < 0 => IntPropCond::LowerBound,
			_ => condition,
		};
		let adv = ctx.state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated,
			propagator: ctx.prop,
		});
		ctx.state.int_activation[self.var].add(ActivationAction::<_, PropRef>::Advise(adv), cond);
	}

	fn enqueue_when(&self, ctx: &mut InitializationContext<'a>, condition: IntPropCond) {
		let condition = match condition {
			IntPropCond::LowerBound if self.scale.get() < 0 => IntPropCond::UpperBound,
			IntPropCond::UpperBound if self.scale.get() < 0 => IntPropCond::LowerBound,
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

impl BoolInitActions<InitializationContext<'_>> for RawLit {
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
				.entry(self.var())
				.or_insert_with(|| {
					ctx.observed_variables.push(self.var());
					Vec::new()
				})
				.push(ActivationAction::Enqueue(ctx.prop).into());
		}
	}
}

impl BoolInspectionActions<InitializationContext<'_>> for RawLit {
	fn val(&self, ctx: &InitializationContext<'_>) -> Option<bool> {
		self.val(ctx.state)
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

impl ReasoningContext for InitializationContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}
