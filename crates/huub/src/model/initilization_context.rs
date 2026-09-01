//! Initialization context used when model constraints subscribe to events.

use crate::{
	IntSet, IntVal,
	actions::{
		BoolAnalyzeActions, BoolInitActions, BoolInspectionActions, InitActions, IntAnalyzeActions,
		IntInitActions, IntInspectionActions, IntPropCond, ReasoningContext, ReasoningEngine,
	},
	model::{
		Advisor, AdvisorId, ConstraintId, Decision, Model,
		decision::Tier,
		resolved::Resolved,
		view::{View, boolean::BoolView, integer::IntView},
	},
	solver::{
		IntLitMeaning, Polarity,
		activation_list::{ActivationAction, ActivationActionS},
		queue::PriorityLevel,
	},
};

/// Wrapper around [`Model`] that knows the constraint being
/// initialized.
#[derive(Debug)]
pub struct ModelInitContext<'a> {
	/// Index of the constraint being initialized.
	con: ConstraintId,
	/// Reference to the Model in which the constraint exists.
	model: &'a mut Model,
	/// The priority level at which the constraint will be enqueued.
	pub(crate) priority: PriorityLevel,
	/// Whether the subscriptions of the propagator would suggest the propagator
	/// should be enqueued.
	semantic_enqueue: bool,
	/// Whether the propagator explicitly requested to be enqueued or not
	/// enqueued.
	decision_enqueue: Option<bool>,
}

/// Whether the activation is an advisor of `con` that was registered with the
/// given data.
fn is_advisor_of(
	advisors: &[Advisor],
	act: ActivationActionS,
	con: ConstraintId,
	data: u64,
) -> bool {
	match act.into() {
		ActivationAction::<AdvisorId, ConstraintId>::Advise(adv) => {
			let advisor = &advisors[adv.index()];
			advisor.con == con && advisor.data == data
		}
		ActivationAction::Enqueue(_) => false,
	}
}

impl BoolAnalyzeActions<ModelInitContext<'_>> for Decision<bool> {
	fn polarity(&self, ctx: &mut ModelInitContext<'_>, polarity: Polarity) {
		ctx.model
			.observe_bool_polarity((*self).into(), Tier::Constraint, polarity);
	}
}

impl BoolInitActions<ModelInitContext<'_>> for Decision<bool> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		self.resolve_alias(ctx.model).advise_when_fixed(ctx, data);
	}

	fn cancel_advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		self.resolve_alias(ctx.model)
			.cancel_advise_when_fixed(ctx, data);
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		self.resolve_alias(ctx.model).cancel_enqueue_when_fixed(ctx);
	}

	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		self.resolve_alias(ctx.model).enqueue_when_fixed(ctx);
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for Decision<bool> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl IntAnalyzeActions<ModelInitContext<'_>> for Decision<IntVal> {
	fn polarity(&self, ctx: &mut ModelInitContext<'_>, polarity: Polarity) {
		ctx.model
			.observe_int_polarity((*self).into(), Tier::Constraint, polarity);
	}

	fn request_direct_eager(&self, ctx: &mut ModelInitContext<'_>) {
		if let Some(dec) = self.resolve_alias(ctx.model).integer_decision() {
			ctx.model.int_vars[dec.idx()].eager_direct = true;
		}
	}

	fn request_order_eager(&self, ctx: &mut ModelInitContext<'_>) {
		if let Some(dec) = self.resolve_alias(ctx.model).integer_decision() {
			ctx.model.int_vars[dec.idx()].eager_order = true;
		}
	}
}

impl IntInitActions<ModelInitContext<'_>> for Decision<IntVal> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		self.resolve_alias(ctx.model).advise_when(ctx, cond, data);
	}

	fn cancel_advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		self.resolve_alias(ctx.model)
			.cancel_advise_when(ctx, cond, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		self.resolve_alias(ctx.model)
			.cancel_enqueue_when(ctx, condition);
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		self.resolve_alias(ctx.model).enqueue_when(ctx, condition);
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for Decision<IntVal> {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSet {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn max(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.max(ctx.model)
	}

	fn max_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.max_lit(ctx.model)
	}

	fn min(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.min(ctx.model)
	}

	fn min_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.min_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(ctx.model, meaning)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl IntInitActions<ModelInitContext<'_>> for IntVal {
	fn advise_when(&self, _: &mut ModelInitContext<'_>, _: IntPropCond, _: u64) {
		// Value will never change, so no advisor will ever be called
	}

	fn cancel_advise_when(&self, _: &mut ModelInitContext<'_>, _: IntPropCond, _: u64) {
		// A constant never subscribed, so there is nothing to cancel.
	}

	fn cancel_enqueue_when(&self, _: &mut ModelInitContext<'_>, _: IntPropCond) {
		// A constant never subscribed, so there is nothing to cancel.
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue();
	}
}

impl<'a> ModelInitContext<'a> {
	/// Internal method used to remove an advisor of the constraint being
	/// initialized from the activation list of a Boolean decision variable.
	fn cancel_bool_advisor(&mut self, idx: usize, data: u64) {
		let con = self.con;
		let advisors = &self.model.advisors;
		let activations = &self.model.bool_vars[idx].constraints;
		let Some(pos) = activations
			.iter()
			.position(|&act| is_advisor_of(advisors, act, con, data))
		else {
			return;
		};
		let _ = self.model.bool_vars[idx].constraints.swap_remove(pos);
	}

	/// Internal method used to remove the enqueue subscription of the
	/// constraint being initialized from the activation list of a Boolean
	/// decision variable.
	fn cancel_bool_enqueue(&mut self, idx: usize) {
		let target = ActivationActionS::from(ActivationAction::<AdvisorId, _>::Enqueue(self.con));
		let activations = &mut self.model.bool_vars[idx].constraints;
		if let Some(pos) = activations.iter().position(|&act| act == target) {
			let _ = activations.swap_remove(pos);
		}
	}

	/// Internal method used to remove an advisor of the constraint being
	/// initialized from the activation list of an integer decision variable.
	fn cancel_int_advisor(&mut self, idx: usize, condition: IntPropCond, data: u64) {
		let con = self.con;
		let advisors = &self.model.advisors;
		let _ = self.model.int_vars[idx]
			.constraints
			.remove(condition, |act| is_advisor_of(advisors, act, con, data));
	}

	/// Internal method used to remove the enqueue subscription of the
	/// constraint being initialized from the activation list of an integer
	/// decision variable.
	fn cancel_int_enqueue(&mut self, idx: usize, condition: IntPropCond) {
		let target = ActivationActionS::from(ActivationAction::<AdvisorId, _>::Enqueue(self.con));
		let _ = self.model.int_vars[idx]
			.constraints
			.remove(condition, |act| act == target);
	}

	/// Returns whether to enqueue the propagator based on its explicit requests
	/// or otherwise the semantics of its subscriptions.
	pub(crate) fn enqueue(&self) -> bool {
		if let Some(enqueue) = self.decision_enqueue {
			enqueue
		} else {
			self.semantic_enqueue
		}
	}
	/// Creates a new [`ModelPostingContext`] for the given constraint
	/// reference.
	pub(crate) fn new(model: &'a mut Model, con: ConstraintId) -> Self {
		ModelInitContext {
			con,
			model,
			priority: PriorityLevel::Medium,
			semantic_enqueue: false,
			decision_enqueue: None,
		}
	}

	/// Mark that subscriptions imply the propagator should be enqueued now.
	pub(crate) fn semantic_enqueue(&mut self) {
		self.semantic_enqueue = true;
	}

	/// Creates a new [`ModelInitContext`] to revise the subscriptions of a
	/// constraint that has already been posted.
	///
	/// Unlike [`Self::new`], the context starts from the priority the
	/// constraint was given when it was posted, so that a constraint that does
	/// not set its priority again keeps the one it has.
	pub(crate) fn update(model: &'a mut Model, con: ConstraintId) -> Self {
		let priority = model.propagator_queue.info[con.index()].priority;
		ModelInitContext {
			con,
			model,
			priority,
			semantic_enqueue: false,
			decision_enqueue: None,
		}
	}
}

impl InitActions for ModelInitContext<'_> {
	fn advise_on_backtrack(&mut self) {
		// Model does not backtrack, so no advisor is required.
	}

	fn enqueue_now(&mut self, option: bool) {
		self.decision_enqueue = Some(option);
	}

	fn set_priority(&mut self, priority: PriorityLevel) {
		self.priority = priority;
	}
}

impl ReasoningContext for ModelInitContext<'_> {
	type Atom = <Model as ReasoningEngine>::Atom;
}

impl BoolInitActions<ModelInitContext<'_>> for Resolved<Decision<bool>> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		ctx.model.advisors.push(Advisor {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: None,
		});
		let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
		ctx.model.bool_vars[self.0.idx()]
			.constraints
			.push(ActivationAction::Advise(adv).into());
	}

	fn cancel_advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		ctx.cancel_bool_advisor(self.0.idx(), data);
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		ctx.cancel_bool_enqueue(self.0.idx());
	}

	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		ctx.model.bool_vars[self.0.idx()]
			.constraints
			.push(ActivationAction::Enqueue(ctx.con).into());
	}
}

impl BoolInitActions<ModelInitContext<'_>> for Resolved<View<bool>> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		let (iv, cond, event) = match self.0.0 {
			BoolView::Decision(lit) => return Resolved(lit).advise_when_fixed(ctx, data),
			BoolView::Const(_) => {
				// Value does not change, so no advisor will ever be called.
				return;
			}
			BoolView::IntEq(iv, v) => (iv, IntLitMeaning::Eq(v), IntPropCond::Domain),
			BoolView::IntGreaterEq(iv, v) => (iv, IntLitMeaning::GreaterEq(v), IntPropCond::Bounds),
			BoolView::IntLess(iv, v) => (iv, IntLitMeaning::Less(v), IntPropCond::Bounds),
			BoolView::IntNotEq(iv, v) => (iv, IntLitMeaning::NotEq(v), IntPropCond::Domain),
		};
		ctx.model.advisors.push(Advisor {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: Some(cond),
		});
		let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
		ctx.model.int_vars[iv.idx()]
			.constraints
			.add(ActivationAction::Advise(adv), event);
	}

	fn cancel_advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		let (iv, event) = match self.0.0 {
			BoolView::Decision(lit) => {
				return Resolved(lit).cancel_advise_when_fixed(ctx, data);
			}
			BoolView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
				return;
			}
			BoolView::IntEq(iv, _) | BoolView::IntNotEq(iv, _) => (iv, IntPropCond::Domain),
			BoolView::IntGreaterEq(iv, _) | BoolView::IntLess(iv, _) => (iv, IntPropCond::Bounds),
		};
		ctx.cancel_int_advisor(iv.idx(), event, data);
	}

	fn cancel_enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		match self.0.0 {
			BoolView::Decision(lit) => Resolved(lit).cancel_enqueue_when_fixed(ctx),
			BoolView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
			}
			BoolView::IntEq(iv, _) | BoolView::IntNotEq(iv, _) => {
				iv.cancel_enqueue_when(ctx, IntPropCond::Domain);
			}
			BoolView::IntGreaterEq(iv, _) | BoolView::IntLess(iv, _) => {
				iv.cancel_enqueue_when(ctx, IntPropCond::Bounds);
			}
		}
	}

	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		match self.0.0 {
			BoolView::Decision(lit) => Resolved(lit).enqueue_when_fixed(ctx),
			BoolView::Const(_) => ctx.semantic_enqueue(),
			// TODO: These definitions might enqueue when the boolean is not fixed. Use advisors
			// instead?
			BoolView::IntEq(iv, _) | BoolView::IntNotEq(iv, _) => {
				iv.enqueue_when(ctx, IntPropCond::Domain);
			}
			BoolView::IntGreaterEq(iv, _) | BoolView::IntLess(iv, _) => {
				iv.enqueue_when(ctx, IntPropCond::Bounds);
			}
		}
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for Resolved<Decision<bool>> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.0.val(ctx.model)
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for Resolved<View<bool>> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl IntInitActions<ModelInitContext<'_>> for Resolved<Decision<IntVal>> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		ctx.model.advisors.push(Advisor {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: None,
		});
		let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
		ctx.model.int_vars[self.idx()]
			.constraints
			.add(ActivationAction::Advise(adv), cond);
	}

	fn cancel_advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		ctx.cancel_int_advisor(self.idx(), cond, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		ctx.cancel_int_enqueue(self.idx(), condition);
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		if condition != IntPropCond::Fixed {
			ctx.semantic_enqueue();
		}
		ctx.model.int_vars[self.idx()]
			.constraints
			.add(ActivationAction::Enqueue(ctx.con), condition);
	}
}

impl IntInitActions<ModelInitContext<'_>> for Resolved<View<IntVal>> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		match self.0.0 {
			IntView::Linear(lin) => {
				let negated = lin.scale.is_negative();
				ctx.model.advisors.push(Advisor {
					con: ctx.con,
					data,
					negated,
					bool2int: false,
					condition: None,
				});
				let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
				ctx.model.int_vars[lin.var.idx()]
					.constraints
					.add(ActivationAction::Advise(adv), cond);
			}
			IntView::Const(_) => ctx.semantic_enqueue(),
			IntView::Bool(lin) => {
				let var = lin.var.resolve_alias(ctx.model);
				let (iv, cond, event) = match var.into_inner().0 {
					BoolView::Decision(lit) => {
						ctx.model.advisors.push(Advisor {
							con: ctx.con,
							data,
							negated: false,
							bool2int: true,
							condition: None,
						});
						let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
						ctx.model.bool_vars[lit.idx()]
							.constraints
							.push(ActivationAction::Advise(adv).into());
						return;
					}
					BoolView::Const(_) => {
						// Value does not change, so no advisor will ever be
						// called
						return;
					}
					BoolView::IntEq(iv, v) => (iv, IntLitMeaning::Eq(v), IntPropCond::Domain),
					BoolView::IntGreaterEq(iv, v) => {
						(iv, IntLitMeaning::GreaterEq(v), IntPropCond::Bounds)
					}
					BoolView::IntLess(iv, v) => (iv, IntLitMeaning::Less(v), IntPropCond::Bounds),
					BoolView::IntNotEq(iv, v) => (iv, IntLitMeaning::NotEq(v), IntPropCond::Domain),
				};
				ctx.model.advisors.push(Advisor {
					con: ctx.con,
					data,
					negated: false,
					bool2int: true,
					condition: Some(cond),
				});
				let adv = AdvisorId::new(ctx.model.advisors.len() - 1);
				ctx.model.int_vars[iv.idx()]
					.constraints
					.add(ActivationAction::Advise(adv), event);
			}
		}
	}

	fn cancel_advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		match self.0.0 {
			IntView::Linear(lin) => ctx.cancel_int_advisor(lin.var.idx(), cond, data),
			IntView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
			}
			IntView::Bool(lin) => {
				let var = lin.var.resolve_alias(ctx.model);
				let (iv, event) = match var.into_inner().0 {
					BoolView::Decision(lit) => {
						return ctx.cancel_bool_advisor(lit.idx(), data);
					}
					BoolView::Const(_) => {
						// A constant never subscribed, so there is nothing to
						// cancel.
						return;
					}
					BoolView::IntEq(iv, _) | BoolView::IntNotEq(iv, _) => (iv, IntPropCond::Domain),
					BoolView::IntGreaterEq(iv, _) | BoolView::IntLess(iv, _) => {
						(iv, IntPropCond::Bounds)
					}
				};
				ctx.cancel_int_advisor(iv.idx(), event, data);
			}
		}
	}

	fn cancel_enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		match self.0.0 {
			IntView::Linear(lin) => {
				Resolved(lin.var).cancel_enqueue_when(ctx, lin.scale_condition(condition));
			}
			IntView::Const(_) => {
				// A constant never subscribed, so there is nothing to cancel.
			}
			IntView::Bool(lin) => lin.var.cancel_enqueue_when_fixed(ctx),
		}
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		match self.0.0 {
			IntView::Linear(lin) => {
				Resolved(lin.var).enqueue_when(ctx, lin.scale_condition(condition));
			}
			IntView::Const(_) => ctx.semantic_enqueue(),
			IntView::Bool(lin) => {
				if condition != IntPropCond::Fixed {
					ctx.semantic_enqueue();
				}
				lin.var.enqueue_when_fixed(ctx);
			}
		}
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for Resolved<Decision<IntVal>> {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSet {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn max(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.max(ctx.model)
	}

	fn max_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.max_lit(ctx.model)
	}

	fn min(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.min(ctx.model)
	}

	fn min_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.min_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(ctx.model, meaning)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for Resolved<View<IntVal>> {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSet {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn max(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.max(ctx.model)
	}

	fn max_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.max_lit(ctx.model)
	}

	fn min(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.min(ctx.model)
	}

	fn min_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.min_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(ctx.model, meaning)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl BoolInitActions<ModelInitContext<'_>> for View<bool> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		self.resolve_alias(ctx.model).advise_when_fixed(ctx, data);
	}
	fn cancel_advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		self.resolve_alias(ctx.model)
			.cancel_advise_when_fixed(ctx, data);
	}
	fn cancel_enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		self.resolve_alias(ctx.model).cancel_enqueue_when_fixed(ctx);
	}
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		self.resolve_alias(ctx.model).enqueue_when_fixed(ctx);
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for View<bool> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl IntInitActions<ModelInitContext<'_>> for View<IntVal> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		self.resolve_alias(ctx.model).advise_when(ctx, cond, data);
	}

	fn cancel_advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		self.resolve_alias(ctx.model)
			.cancel_advise_when(ctx, cond, data);
	}

	fn cancel_enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		self.resolve_alias(ctx.model)
			.cancel_enqueue_when(ctx, condition);
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		self.resolve_alias(ctx.model).enqueue_when(ctx, condition);
	}
}

impl IntInspectionActions<ModelInitContext<'_>> for View<IntVal> {
	fn bounds(&self, ctx: &ModelInitContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.model)
	}

	fn domain(&self, ctx: &ModelInitContext<'_>) -> IntSet {
		self.domain(ctx.model)
	}

	fn in_domain(&self, ctx: &ModelInitContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.model, val)
	}

	fn lit_meaning(&self, ctx: &ModelInitContext<'_>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.model, lit)
	}

	fn max(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.max(ctx.model)
	}

	fn max_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.max_lit(ctx.model)
	}

	fn min(&self, ctx: &ModelInitContext<'_>) -> IntVal {
		self.min(ctx.model)
	}

	fn min_lit(&self, ctx: &ModelInitContext<'_>) -> View<bool> {
		self.min_lit(ctx.model)
	}

	fn try_lit(&self, ctx: &ModelInitContext<'_>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(ctx.model, meaning)
	}

	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<IntVal> {
		self.val(ctx.model)
	}
}

impl BoolInitActions<ModelInitContext<'_>> for bool {
	fn advise_when_fixed(&self, _: &mut ModelInitContext<'_>, _: u64) {
		// Value does not change, so no advisor will ever be called
	}
	fn cancel_advise_when_fixed(&self, _: &mut ModelInitContext<'_>, _: u64) {
		// A constant never subscribed, so there is nothing to cancel.
	}
	fn cancel_enqueue_when_fixed(&self, _: &mut ModelInitContext<'_>) {
		// A constant never subscribed, so there is nothing to cancel.
	}
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		ctx.semantic_enqueue();
	}
}
