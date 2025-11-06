//! This module contains the [`PostingContext`] struct, which is used to provide
//! [`ReasoningEngine::PostingCtx`] to [`Propagator`] implementations when they
//! are posted to a [`Solver`].

use pindakaas::{Lit as RawLit, Var as RawVar};

use crate::{
	actions::{
		BoolInspectionActions, BoolPostingActions, IntInspectionActions, IntPostingActions,
		PostingActions,
	},
	solver::{
		activation_list::{ActivationAction, IntPropCond},
		engine::{AdvisorDef, PropRef, State},
		int_var::IntVarRef,
		queue::PriorityLevel,
		BoolView, BoolViewInner, IntView, IntViewInner,
	},
	IntVal,
};

#[derive(Debug)]
/// The context given to [`Propagator`] implementations (during
/// [`Propagators::post`]) when added to [`Solver`].
pub struct PostingContext<'a> {
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

impl BoolPostingActions<PostingContext<'_>> for BoolView {
	fn advise_when_fixed(&self, ctx: &mut PostingContext<'_>, data: u64) {
		match self.0 {
			BoolViewInner::Lit(lit) => lit.advise_when_fixed(ctx, data),
			BoolViewInner::Const(_) => {
				// constant will never change, so we don't need to add an
				// advisor.
			}
		}
	}
	fn enqueue_when_fixed(&self, ctx: &mut PostingContext<'_>) {
		match self.0 {
			BoolViewInner::Lit(lit) => lit.enqueue_when_fixed(ctx),
			BoolViewInner::Const(_) => {
				ctx.semantic_enqueue = true;
			}
		}
	}
}

impl IntInspectionActions<PostingContext<'_>> for IntVal {
	type Atom = <Self as IntInspectionActions<State>>::Atom;

	fn check_in_domain(&self, ctx: &PostingContext<'_>, val: IntVal) -> bool {
		self.check_in_domain(ctx.state, val)
	}

	fn get_domain(&self, _: &PostingContext<'_>) -> crate::IntSetVal {
		(*self..=*self).into()
	}

	fn get_lit_meaning(
		&self,
		ctx: &PostingContext<'_>,
		lit: Self::Atom,
	) -> Option<super::IntLitMeaning> {
		self.get_lit_meaning(ctx.state, lit)
	}

	fn get_lower_bound(&self, ctx: &PostingContext<'_>) -> IntVal {
		self.get_lower_bound(ctx.state)
	}

	fn get_lower_bound_lit(&self, ctx: &PostingContext<'_>) -> Self::Atom {
		self.get_lower_bound_lit(ctx.state)
	}

	fn get_upper_bound(&self, ctx: &PostingContext<'_>) -> IntVal {
		self.get_upper_bound(ctx.state)
	}

	fn get_upper_bound_lit(&self, ctx: &PostingContext<'_>) -> Self::Atom {
		self.get_upper_bound_lit(ctx.state)
	}

	fn try_lit(
		&self,
		ctx: &PostingContext<'_>,
		meaning: super::IntLitMeaning,
	) -> Option<Self::Atom> {
		self.try_lit(ctx.state, meaning)
	}
}

impl IntPostingActions<PostingContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut PostingContext<'_>, _: IntPropCond, _: u64) {
		// constant will never change, so we don't need to add an
		// advisor.
	}
	fn enqueue_when(&self, ctx: &mut PostingContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue = true;
	}
}

impl IntInspectionActions<PostingContext<'_>> for IntVarRef {
	type Atom = <Self as IntInspectionActions<State>>::Atom;

	fn check_in_domain(&self, ctx: &PostingContext<'_>, val: IntVal) -> bool {
		self.check_in_domain(ctx.state, val)
	}

	fn get_domain(&self, ctx: &PostingContext<'_>) -> crate::IntSetVal {
		self.get_domain(ctx.state)
	}

	fn get_lit_meaning(
		&self,
		ctx: &PostingContext<'_>,
		lit: Self::Atom,
	) -> Option<super::IntLitMeaning> {
		self.get_lit_meaning(ctx.state, lit)
	}

	fn get_lower_bound(&self, ctx: &PostingContext<'_>) -> IntVal {
		self.get_lower_bound(ctx.state)
	}

	fn get_lower_bound_lit(&self, ctx: &PostingContext<'_>) -> Self::Atom {
		self.get_lower_bound_lit(ctx.state)
	}

	fn get_upper_bound(&self, ctx: &PostingContext<'_>) -> IntVal {
		self.get_upper_bound(ctx.state)
	}

	fn get_upper_bound_lit(&self, ctx: &PostingContext<'_>) -> Self::Atom {
		self.get_upper_bound_lit(ctx.state)
	}

	fn try_lit(
		&self,
		ctx: &PostingContext<'_>,
		meaning: super::IntLitMeaning,
	) -> Option<Self::Atom> {
		self.try_lit(ctx.state, meaning)
	}
}

impl IntPostingActions<PostingContext<'_>> for IntVarRef {
	fn advise_when(&self, ctx: &mut PostingContext<'_>, condition: IntPropCond, data: u64) {
		IntView(IntViewInner::VarRef(*self)).advise_when(ctx, condition, data);
	}
	fn enqueue_when(&self, ctx: &mut PostingContext<'_>, condition: IntPropCond) {
		if self.get_val(ctx.state).is_some() {
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

impl<'a> IntPostingActions<PostingContext<'a>> for IntView {
	fn advise_when(&self, ctx: &mut PostingContext<'a>, condition: IntPropCond, data: u64) {
		let (var, cond, negated) = match self.0 {
			IntViewInner::VarRef(var) => (var, condition, false),
			IntViewInner::Linear { transformer, var } => {
				let condition = match condition {
					IntPropCond::LowerBound if !transformer.positive_scale() => {
						IntPropCond::UpperBound
					}
					IntPropCond::UpperBound if !transformer.positive_scale() => {
						IntPropCond::LowerBound
					}
					_ => condition,
				};
				(var, condition, !transformer.positive_scale())
			}
			IntViewInner::Const(_) => {
				// The variable will never change, so we don't need to add an
				// advisor.
				return;
			}
			IntViewInner::Bool { lit, .. } => {
				return ctx.add_lit_advisor(lit, data, true);
			}
		};
		let adv = ctx.state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated,
			propagator: ctx.prop,
		});
		ctx.state.int_activation[var].add(ActivationAction::<_, PropRef>::Advise(adv), cond);
	}
	fn enqueue_when(&self, ctx: &mut PostingContext<'a>, condition: IntPropCond) {
		match self.0 {
			IntViewInner::VarRef(iv) => iv.enqueue_when(ctx, condition),
			IntViewInner::Const(_) => {
				ctx.semantic_enqueue = true;
				// No further change will happen, so we don't need to add the
				// propagator to any activation lists.
			}
			IntViewInner::Linear { transformer, var } => {
				let condition = match condition {
					IntPropCond::LowerBound if !transformer.positive_scale() => {
						IntPropCond::UpperBound
					}
					IntPropCond::UpperBound if !transformer.positive_scale() => {
						IntPropCond::LowerBound
					}
					_ => condition,
				};
				var.enqueue_when(ctx, condition);
			}
			IntViewInner::Bool { lit, .. } => {
				if condition != IntPropCond::Fixed {
					ctx.semantic_enqueue = true;
				}
				lit.enqueue_when_fixed(ctx);
			}
		}
	}
}

impl PostingContext<'_> {
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

impl<'a> PostingContext<'a> {
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

impl PostingActions for PostingContext<'_> {
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

impl BoolInspectionActions<PostingContext<'_>> for RawLit {
	fn get_val(&self, ctx: &PostingContext<'_>) -> Option<bool> {
		self.get_val(ctx.state)
	}
}

impl BoolPostingActions<PostingContext<'_>> for RawLit {
	fn advise_when_fixed(&self, ctx: &mut PostingContext<'_>, data: u64) {
		if self.get_val(ctx.state).is_some() {
			// The literal will never change, so we don't need to add an advisor.
			return;
		}
		// Otherwise, add the advisor to the engine
		ctx.add_lit_advisor(*self, data, false);
	}
	fn enqueue_when_fixed(&self, ctx: &mut PostingContext<'_>) {
		if self.get_val(ctx.state).is_some() {
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

impl BoolPostingActions<PostingContext<'_>> for bool {
	fn advise_when_fixed(&self, _: &mut PostingContext<'_>, _: u64) {
		// The literal will never change, so we don't need to add an advisor.
	}
	fn enqueue_when_fixed(&self, ctx: &mut PostingContext<'_>) {
		ctx.semantic_enqueue = true;
	}
}
