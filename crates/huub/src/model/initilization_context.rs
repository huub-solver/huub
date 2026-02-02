//! Initialization context used when model constraints subscribe to events.

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, InitActions, IntInitActions, IntInspectionActions,
		ReasoningContext, ReasoningEngine,
	},
	model::{
		AdvRef, Advisor, ConRef, Decision, Model,
		view::{View, boolean::BoolView, integer::IntView},
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, IntPropCond},
		queue::PriorityLevel,
	},
};

#[derive(Debug)]
/// Wrapper around [`Model`] that knows the constraint being
/// initialized.
pub struct ModelInitContext<'a> {
	/// Index of the constraint being initialized.
	con: ConRef,
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

impl BoolInitActions<ModelInitContext<'_>> for Decision<bool> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		let view: View<bool> = (*self).into();
		view.advise_when_fixed(ctx, data);
	}

	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		let view: View<bool> = (*self).into();
		view.enqueue_when_fixed(ctx);
	}
}

impl BoolInspectionActions<ModelInitContext<'_>> for Decision<bool> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl IntInitActions<ModelInitContext<'_>> for Decision<IntVal> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		ctx.model.advisors.push(Advisor {
			con: ctx.con,
			data,
			negated: false,
			bool2int: false,
			condition: None,
		});
		let adv = AdvRef::new(ctx.model.advisors.len() - 1);
		ctx.model.int_vars[self.idx()]
			.constraints
			.add(ActivationAction::Advise(adv), cond);
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

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, _: IntPropCond) {
		ctx.semantic_enqueue();
	}
}

impl<'a> ModelInitContext<'a> {
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
	pub(crate) fn new(model: &'a mut Model, con: ConRef) -> Self {
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
	type Conflict = <Model as ReasoningEngine>::Conflict;
}

impl BoolInitActions<ModelInitContext<'_>> for View<bool> {
	fn advise_when_fixed(&self, ctx: &mut ModelInitContext<'_>, data: u64) {
		let var = self.resolve_alias(ctx.model);
		let (iv, cond, event) = match var.0 {
			BoolView::Decision(lit) => {
				ctx.model.advisors.push(Advisor {
					con: ctx.con,
					data,
					negated: false,
					bool2int: false,
					condition: None,
				});
				let adv = AdvRef::new(ctx.model.advisors.len() - 1);
				ctx.model.bool_vars[lit.idx()]
					.constraints
					.push(ActivationAction::Advise(adv).into());
				return;
			}
			BoolView::Const(_) => {
				// Value does not change, so no advisor will ever be called
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
		let adv = AdvRef::new(ctx.model.advisors.len() - 1);
		ctx.model.int_vars[iv.idx()]
			.constraints
			.add(ActivationAction::Advise(adv), event);
	}
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		let var = self.resolve_alias(ctx.model);
		match var.0 {
			BoolView::Decision(lit) => ctx.model.bool_vars[lit.idx()]
				.constraints
				.push(ActivationAction::Enqueue(ctx.con).into()),
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

impl BoolInspectionActions<ModelInitContext<'_>> for View<bool> {
	fn val(&self, ctx: &ModelInitContext<'_>) -> Option<bool> {
		self.val(ctx.model)
	}
}

impl IntInitActions<ModelInitContext<'_>> for View<IntVal> {
	fn advise_when(&self, ctx: &mut ModelInitContext<'_>, cond: IntPropCond, data: u64) {
		let var = self.resolve_alias(ctx.model);

		match var.0 {
			IntView::Linear(lin) => {
				let negated = lin.scale.is_negative();
				ctx.model.advisors.push(Advisor {
					con: ctx.con,
					data,
					negated,
					bool2int: false,
					condition: None,
				});
				let adv = AdvRef::new(ctx.model.advisors.len() - 1);
				ctx.model.int_vars[lin.var.idx()]
					.constraints
					.add(ActivationAction::Advise(adv), cond);
			}
			IntView::Const(_) => ctx.semantic_enqueue(),
			IntView::Bool(lin) => {
				let var = lin.var.resolve_alias(ctx.model);
				let (iv, cond, event) = match var.0 {
					BoolView::Decision(lit) => {
						ctx.model.advisors.push(Advisor {
							con: ctx.con,
							data,
							negated: false,
							bool2int: true,
							condition: None,
						});
						let adv = AdvRef::new(ctx.model.advisors.len() - 1);
						ctx.model.bool_vars[lit.idx()]
							.constraints
							.push(ActivationAction::Advise(adv).into());
						return;
					}
					BoolView::Const(_) => {
						// Value does not change, so no advisor will ever be called
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
				let adv = AdvRef::new(ctx.model.advisors.len() - 1);
				ctx.model.int_vars[iv.idx()]
					.constraints
					.add(ActivationAction::Advise(adv), event);
			}
		}
	}

	fn enqueue_when(&self, ctx: &mut ModelInitContext<'_>, condition: IntPropCond) {
		let var = self.resolve_alias(ctx.model);

		match var.0 {
			IntView::Linear(lin) => {
				let condition = match condition {
					IntPropCond::LowerBound if lin.scale.is_negative() => IntPropCond::UpperBound,
					IntPropCond::UpperBound if lin.scale.is_negative() => IntPropCond::LowerBound,
					_ => condition,
				};
				lin.var.enqueue_when(ctx, condition);
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
	fn enqueue_when_fixed(&self, ctx: &mut ModelInitContext<'_>) {
		ctx.semantic_enqueue();
	}
}
