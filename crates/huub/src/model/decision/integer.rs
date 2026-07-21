//! Integer decision variable definitions for the model layer.

use std::mem;

use rangelist::IntervalIterator;

use crate::{
	IntSet, IntVal,
	actions::{
		IntDecisionActions, IntEvent, IntInspectionActions, IntPropCond, IntPropagationActions,
		IntSimplificationActions, ReasoningContext,
	},
	constraints::{Conflict, NO_REASON, Nogood},
	model::{
		AdvRef, ConRef, Decision, Model, SimplificationContext, SimplificationReasonSink,
		decision::{DecisionReference, PolarityScore, private},
		resolved::Resolved,
		view::{View, boolean::BoolView, integer::IntView},
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, ActivationList},
	},
};

/// Wrapper type to distinguish between a variable with a domain, and an alias
/// to another variable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Domain<E, Alias> {
	/// A normal variable with a domain.
	Domain(E),
	/// An alias to another variable.
	Alias(Alias),
}

/// Definition of an integer decision variable in a [`Model`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntDecision {
	/// The set of possible values that the variable can take.
	pub(crate) domain: Domain<IntSet, View<IntVal>>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: ActivationList,
	/// Whether the analyze stage requested the direct encoding (the `x = i`
	/// equality literals) to be created eagerly.
	pub(crate) eager_direct: bool,
	/// Whether the analyze stage requested the order encoding (the `x < i`
	/// inequality literals) to be created eagerly.
	pub(crate) eager_order: bool,
	/// Accumulated polarity evidence collected during the analyze stage.
	pub(crate) polarity: PolarityScore,
}

impl Decision<IntVal> {
	/// Return the index used to access this decision in model storage.
	pub(crate) fn idx(&self) -> usize {
		self.0 as usize
	}
}

impl IntDecisionActions<Model> for Decision<IntVal> {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> View<bool> {
		self.resolve_alias(ctx).lit(ctx, meaning)
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<View<bool>> {
		self.resolve_alias(ctx).val_lit(ctx)
	}
}

impl IntDecisionActions<SimplificationContext<'_>> for Decision<IntVal> {
	fn lit(&self, ctx: &mut SimplificationContext<'_>, meaning: IntLitMeaning) -> View<bool> {
		self.lit(&mut *ctx.0, meaning)
	}

	fn val_lit(&self, ctx: &mut SimplificationContext<'_>) -> Option<View<bool>> {
		self.val_lit(&mut *ctx.0)
	}
}

impl IntInspectionActions<Model> for Decision<IntVal> {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		self.resolve_alias(ctx).bounds(ctx)
	}

	fn domain(&self, ctx: &Model) -> IntSet {
		self.resolve_alias(ctx).domain(ctx)
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		self.resolve_alias(ctx).in_domain(ctx, val)
	}

	fn lit_meaning(
		&self,
		ctx: &Model,
		lit: <Model as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		self.resolve_alias(ctx).lit_meaning(ctx, lit)
	}

	fn max(&self, ctx: &Model) -> IntVal {
		self.resolve_alias(ctx).max(ctx)
	}

	fn max_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		self.resolve_alias(ctx).max_lit(ctx)
	}

	fn min(&self, ctx: &Model) -> IntVal {
		self.resolve_alias(ctx).min(ctx)
	}

	fn min_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		self.resolve_alias(ctx).min_lit(ctx)
	}

	fn try_lit(
		&self,
		ctx: &Model,
		meaning: IntLitMeaning,
	) -> Option<<Model as ReasoningContext>::Atom> {
		self.resolve_alias(ctx).try_lit(ctx, meaning)
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		self.resolve_alias(ctx).val(ctx)
	}
}

impl IntInspectionActions<SimplificationContext<'_>> for Decision<IntVal> {
	fn bounds(&self, ctx: &SimplificationContext<'_>) -> (IntVal, IntVal) {
		self.bounds(&*ctx.0)
	}

	fn domain(&self, ctx: &SimplificationContext<'_>) -> IntSet {
		self.domain(&*ctx.0)
	}

	fn in_domain(&self, ctx: &SimplificationContext<'_>, val: IntVal) -> bool {
		self.in_domain(&*ctx.0, val)
	}

	fn lit_meaning(
		&self,
		ctx: &SimplificationContext<'_>,
		lit: <SimplificationContext<'_> as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		self.lit_meaning(&*ctx.0, lit)
	}

	fn max(&self, ctx: &SimplificationContext<'_>) -> IntVal {
		self.max(&*ctx.0)
	}

	fn max_lit(
		&self,
		ctx: &SimplificationContext<'_>,
	) -> <SimplificationContext<'_> as ReasoningContext>::Atom {
		self.max_lit(&*ctx.0)
	}

	fn min(&self, ctx: &SimplificationContext<'_>) -> IntVal {
		self.min(&*ctx.0)
	}

	fn min_lit(
		&self,
		ctx: &SimplificationContext<'_>,
	) -> <SimplificationContext<'_> as ReasoningContext>::Atom {
		self.min_lit(&*ctx.0)
	}

	fn try_lit(
		&self,
		ctx: &SimplificationContext<'_>,
		meaning: IntLitMeaning,
	) -> Option<<SimplificationContext<'_> as ReasoningContext>::Atom> {
		self.try_lit(&*ctx.0, meaning)
	}

	fn val(&self, ctx: &SimplificationContext<'_>) -> Option<IntVal> {
		self.val(&*ctx.0)
	}
}

impl IntPropagationActions<Model> for Decision<IntVal> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.fix(
			&mut SimplificationContext(ctx),
			val,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}

	fn remove_val(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.remove_val(
			&mut SimplificationContext(ctx),
			val,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}

	fn tighten_max(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.tighten_max(
			&mut SimplificationContext(ctx),
			val,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}

	fn tighten_min(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.tighten_min(
			&mut SimplificationContext(ctx),
			val,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}
}

impl<'a> IntPropagationActions<SimplificationContext<'a>> for Decision<IntVal> {
	fn fix(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).fix(ctx, val, reason)
	}

	fn remove_val(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).remove_val(ctx, val, reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).tighten_max(ctx, val, reason)
	}

	fn tighten_min(
		&self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).tighten_min(ctx, val, reason)
	}
}

impl IntSimplificationActions<Model> for Decision<IntVal> {
	fn exclude(
		&self,
		ctx: &mut Model,
		values: &IntSet,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.exclude(
			&mut SimplificationContext(ctx),
			values,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}

	fn restrict_domain(
		&self,
		ctx: &mut Model,
		domain: &IntSet,
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> Result<(), Nogood<View<bool>>> {
		self.restrict_domain(
			&mut SimplificationContext(ctx),
			domain,
			Model::adapt_reason(reason),
		)
		.map_err(Conflict::into_model_nogood)
	}

	fn unify(&self, ctx: &mut Model, other: impl Into<Self>) -> Result<(), Nogood<View<bool>>> {
		self.unify(&mut SimplificationContext(ctx), other)
			.map_err(Conflict::into_model_nogood)
	}
}

impl<'a> IntSimplificationActions<SimplificationContext<'a>> for Decision<IntVal> {
	fn exclude(
		&self,
		ctx: &mut SimplificationContext<'a>,
		values: &IntSet,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0).exclude(ctx, values, reason)
	}

	fn restrict_domain(
		&self,
		ctx: &mut SimplificationContext<'a>,
		domain: &IntSet,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.resolve_alias(&*ctx.0)
			.restrict_domain(ctx, domain, reason)
	}

	fn unify(
		&self,
		ctx: &mut SimplificationContext<'a>,
		other: impl Into<Self>,
	) -> Result<(), Conflict<View<bool>>> {
		let me = self.resolve_alias(&*ctx.0);
		let other = other.into().resolve_alias(&*ctx.0);
		me.unify(ctx, other)?;
		Ok(())
	}
}

impl IntDecision {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSet) -> Self {
		Self {
			domain: Domain::Domain(dom),
			constraints: Default::default(),
			eager_direct: false,
			eager_order: false,
			polarity: PolarityScore::default(),
		}
	}
}

impl DecisionReference for IntVal {
	type Ref = u32;
}
impl private::Sealed for IntVal {}

impl Resolved<Decision<IntVal>> {
	/// Internal method performing unification under the assumption that the
	/// receiver is an integer decision index that is not already aliased, and
	/// that it can be aliased to directly point to `target`.
	pub(crate) fn unify_internal(
		self,
		ctx: &mut SimplificationContext<'_>,
		target: View<IntVal>,
	) -> Result<(), Conflict<View<bool>>> {
		let idx = self.idx();
		debug_assert!(matches!(ctx.0.int_vars[idx].domain, Domain::Domain(_)));

		// Set the domain on the variable to be aliased to trigger subscription
		// events.
		self.restrict_domain(ctx, &target.domain(ctx), NO_REASON)?;
		// Change variable to point to the target
		match mem::replace(&mut ctx.0.int_vars[idx].domain, Domain::Alias(target)) {
			// Restrict the domain of the target variable using the variable domain
			// being aliased.
			Domain::Domain(dom) => target.restrict_domain(ctx, &dom, NO_REASON)?,
			Domain::Alias(View(IntView::Const(v))) => target.fix(ctx, v, NO_REASON)?,
			_ => unreachable!(),
		};
		// Process any pending integer events for the variable being aliased.
		if let Some(event) = ctx.0.int_events.remove(&(idx as u32)) {
			ctx.0.notify_int_event(idx as u32, event);
		}
		// Transfer any constraints from the aliased variable to the target variable
		let constraints = mem::take(&mut ctx.0.int_vars[idx].constraints);
		// Move subscriptions to target decision variable
		match target.0 {
			IntView::Linear(lin) => {
				ctx.0.int_vars[lin.var.idx()]
					.constraints
					.extend(constraints);
			}
			IntView::Bool(lin) => match lin.var.0 {
				inner @ (BoolView::IntEq(j, _)
				| BoolView::IntNotEq(j, _)
				| BoolView::IntGreaterEq(j, _)
				| BoolView::IntLess(j, _)) => {
					let model = &mut *ctx.0;
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<AdvRef, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut model.advisors[adv.index()];
								def.bool2int = true;
								def.condition = Some(match inner {
									BoolView::IntEq(_, v) => IntLitMeaning::Eq(v),
									BoolView::IntGreaterEq(_, v) => IntLitMeaning::GreaterEq(v),
									BoolView::IntLess(_, v) => IntLitMeaning::Less(v),
									BoolView::IntNotEq(_, v) => IntLitMeaning::NotEq(v),
									_ => unreachable!(),
								});
								def.negated = false;
							}
							let cond = if matches!(
								inner,
								BoolView::IntEq(_, _) | BoolView::IntNotEq(_, _)
							) {
								IntPropCond::Domain
							} else {
								IntPropCond::Bounds
							};
							model.int_vars[j.idx()].constraints.add(act, cond);
						},
					);
				}
				// Move subscription to Boolean decision
				BoolView::Decision(l) => {
					let jdx = l.idx();
					let model = &mut *ctx.0;
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<AdvRef, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut model.advisors[adv.index()];
								def.bool2int = true;
								def.negated = false;
							}
							model.bool_vars[jdx].constraints.push(act.into());
						},
					);
				}
				BoolView::Const(_) => unreachable!(),
			},
			IntView::Const(_) => unreachable!(),
		};
		Ok(())
	}
}

impl Resolved<Decision<IntVal>> {
	/// Consuming variant of [`IntSimplificationActions::exclude`] for
	/// canonical integer decisions.
	pub(crate) fn exclude<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		values: &IntSet,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		let Domain::Domain(dom) = &ctx.0.int_vars[self.idx()].domain else {
			unreachable!()
		};
		let diff: IntSet = dom.diff(values);
		if diff.is_empty() {
			return Err(ctx.make_conflict(
				Some(View(BoolView::IntNotEq(self.0, *values.min().unwrap()))),
				reason,
			));
		}
		if *dom == diff {
			return Ok(());
		}
		let dom_min = *dom.min().unwrap();
		let dom_max = *dom.max().unwrap();
		let min = *diff.min().unwrap();
		let max = *diff.max().unwrap();
		if min == max {
			ctx.0.int_vars[self.idx()].domain = Domain::Alias(min.into());
			ctx.0.int_events.insert(self.0.0, IntEvent::Fixed);
		} else {
			let model = &mut *ctx.0;
			let entry = model.int_events.entry(self.0.0).or_insert(IntEvent::Domain);
			if dom_min != min {
				*entry += IntEvent::LowerBound;
			}
			if dom_max != max {
				*entry += IntEvent::UpperBound;
			}

			model.int_vars[self.idx()].domain = Domain::Domain(diff);
		};
		Ok(())
	}

	/// Consuming variant of [`IntPropagationActions::fix`] for canonical
	/// integer decisions.
	pub(crate) fn fix<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		let Domain::Domain(dom) = &ctx.0.int_vars[self.idx()].domain else {
			unreachable!()
		};
		if dom.contains(&val) {
			let model = &mut *ctx.0;
			model.int_vars[self.idx()].domain = Domain::Alias(val.into());
			model.int_events.insert(self.0.0, IntEvent::Fixed);
			Ok(())
		} else {
			Err(ctx.make_conflict(Some(View(BoolView::IntEq(self.0, val))), reason))
		}
	}

	/// Consuming variant of [`IntPropagationActions::remove_val`] for canonical
	/// integer decisions.
	pub(crate) fn remove_val<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		self.exclude(ctx, &(val..=val).into(), reason)
	}

	/// Consuming variant of [`IntSimplificationActions::restrict_domain`] for
	/// canonical integer decisions.
	pub(crate) fn restrict_domain<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		domain: &IntSet,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		let Domain::Domain(dom) = &ctx.0.int_vars[self.idx()].domain else {
			unreachable!()
		};
		let intersect: IntSet = dom.intersect(domain);
		if intersect.is_empty() {
			let subject = View(BoolView::IntNotEq(self.0, *dom.min().unwrap()));
			return Err(ctx.make_conflict(Some(subject), reason));
		} else if *dom == intersect {
			return Ok(());
		}
		let dom_min = *dom.min().unwrap();
		let dom_max = *dom.max().unwrap();
		let min = *intersect.min().unwrap();
		let max = *intersect.max().unwrap();
		if min == max {
			ctx.0.int_vars[self.idx()].domain = Domain::Alias(min.into());
			ctx.0.int_events.insert(self.0.0, IntEvent::Fixed);
		} else {
			let model = &mut *ctx.0;
			let entry = model.int_events.entry(self.0.0).or_insert(IntEvent::Domain);
			if dom_min != min {
				*entry += IntEvent::LowerBound;
			}
			if dom_max != max {
				*entry += IntEvent::UpperBound;
			}

			model.int_vars[self.idx()].domain = Domain::Domain(intersect);
		}
		Ok(())
	}

	/// Consuming variant of [`IntPropagationActions::tighten_max`] for
	/// canonical integer decisions.
	pub(crate) fn tighten_max<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		{
			let Domain::Domain(dom) = &ctx.0.int_vars[self.idx()].domain else {
				unreachable!()
			};
			if val >= *dom.max().unwrap() {
				return Ok(());
			} else if val < *dom.min().unwrap() {
				return Err(
					ctx.make_conflict(Some(View(BoolView::IntLess(self.0, val + 1))), reason)
				);
			}
		}
		let model = &mut *ctx.0;
		let Domain::Domain(dom) = &mut model.int_vars[self.idx()].domain else {
			unreachable!()
		};
		dom.tighten_max(val);
		let min = *dom.min().unwrap();
		let fixed = min == *dom.max().unwrap();
		if fixed {
			model.int_vars[self.idx()].domain = Domain::Alias(min.into());
			model.int_events.insert(self.0.0, IntEvent::Fixed);
		} else {
			model
				.int_events
				.entry(self.0.0)
				.and_modify(|v| *v += IntEvent::UpperBound)
				.or_insert(IntEvent::UpperBound);
		};
		Ok(())
	}

	/// Consuming variant of [`IntPropagationActions::tighten_min`] for
	/// canonical integer decisions.
	pub(crate) fn tighten_min<'a>(
		self,
		ctx: &mut SimplificationContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink),
	) -> Result<(), Conflict<View<bool>>> {
		{
			let Domain::Domain(dom) = &ctx.0.int_vars[self.idx()].domain else {
				unreachable!()
			};
			if val <= *dom.min().unwrap() {
				return Ok(());
			} else if val > *dom.max().unwrap() {
				return Err(
					ctx.make_conflict(Some(View(BoolView::IntGreaterEq(self.0, val))), reason)
				);
			}
		}
		let model = &mut *ctx.0;
		let Domain::Domain(dom) = &mut model.int_vars[self.idx()].domain else {
			unreachable!()
		};
		dom.tighten_min(val);
		let min = *dom.min().unwrap();
		let fixed = min == *dom.max().unwrap();
		if fixed {
			model.int_vars[self.idx()].domain = Domain::Alias(min.into());
			model.int_events.insert(self.0.0, IntEvent::Fixed);
		} else {
			model
				.int_events
				.entry(self.0.0)
				.and_modify(|e| *e += IntEvent::LowerBound)
				.or_insert(IntEvent::LowerBound);
		};
		Ok(())
	}
}

impl IntDecisionActions<Model> for Resolved<Decision<IntVal>> {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> View<bool> {
		IntInspectionActions::try_lit(self, ctx, meaning).unwrap()
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<View<bool>> {
		let val = self.val(ctx)?;
		Some(View(BoolView::IntEq(self.0, val)))
	}
}

impl IntDecisionActions<SimplificationContext<'_>> for Resolved<Decision<IntVal>> {
	fn lit(&self, ctx: &mut SimplificationContext<'_>, meaning: IntLitMeaning) -> View<bool> {
		self.lit(&mut *ctx.0, meaning)
	}

	fn val_lit(&self, ctx: &mut SimplificationContext<'_>) -> Option<View<bool>> {
		self.val_lit(&mut *ctx.0)
	}
}

impl IntInspectionActions<Model> for Resolved<Decision<IntVal>> {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => (*d.min().unwrap(), *d.max().unwrap()),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn domain(&self, ctx: &Model) -> IntSet {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d.clone(),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d.contains(&val),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn lit_meaning(
		&self,
		_: &Model,
		lit: <Model as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		match lit.0 {
			BoolView::IntEq(idx, val) if idx == self.0 => Some(IntLitMeaning::Eq(val)),
			BoolView::IntGreaterEq(idx, val) if idx == self.0 => {
				Some(IntLitMeaning::GreaterEq(val))
			}
			BoolView::IntLess(idx, val) if idx == self.0 => Some(IntLitMeaning::Less(val)),
			BoolView::IntNotEq(idx, val) if idx == self.0 => Some(IntLitMeaning::NotEq(val)),
			_ => None,
		}
	}

	fn max(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => *d.max().unwrap(),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn max_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d
				.min()
				.map(|&val| View(BoolView::IntLess(self.0, val + 1)))
				.unwrap(),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn min(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => *d.min().unwrap(),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn min_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d
				.min()
				.map(|&val| View(BoolView::IntGreaterEq(self.0, val)))
				.unwrap(),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn try_lit(
		&self,
		ctx: &Model,
		meaning: IntLitMeaning,
	) -> Option<<Model as ReasoningContext>::Atom> {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(_) => Some(View(match meaning {
				IntLitMeaning::Eq(v) => BoolView::IntEq(self.0, v),
				IntLitMeaning::NotEq(v) => BoolView::IntNotEq(self.0, v),
				IntLitMeaning::GreaterEq(v) => BoolView::IntGreaterEq(self.0, v),
				IntLitMeaning::Less(v) => BoolView::IntLess(self.0, v),
			})),
			Domain::Alias(_) => unreachable!(),
		}
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => {
				let (lb, ub) = (d.min().unwrap(), d.max().unwrap());
				if lb == ub { Some(*lb) } else { None }
			}
			Domain::Alias(_) => unreachable!(),
		}
	}
}

impl IntInspectionActions<SimplificationContext<'_>> for Resolved<Decision<IntVal>> {
	fn bounds(&self, ctx: &SimplificationContext<'_>) -> (IntVal, IntVal) {
		self.bounds(&*ctx.0)
	}

	fn domain(&self, ctx: &SimplificationContext<'_>) -> IntSet {
		self.domain(&*ctx.0)
	}

	fn in_domain(&self, ctx: &SimplificationContext<'_>, val: IntVal) -> bool {
		self.in_domain(&*ctx.0, val)
	}

	fn lit_meaning(
		&self,
		ctx: &SimplificationContext<'_>,
		lit: <SimplificationContext<'_> as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		self.lit_meaning(&*ctx.0, lit)
	}

	fn max(&self, ctx: &SimplificationContext<'_>) -> IntVal {
		self.max(&*ctx.0)
	}

	fn max_lit(
		&self,
		ctx: &SimplificationContext<'_>,
	) -> <SimplificationContext<'_> as ReasoningContext>::Atom {
		self.max_lit(&*ctx.0)
	}

	fn min(&self, ctx: &SimplificationContext<'_>) -> IntVal {
		self.min(&*ctx.0)
	}

	fn min_lit(
		&self,
		ctx: &SimplificationContext<'_>,
	) -> <SimplificationContext<'_> as ReasoningContext>::Atom {
		self.min_lit(&*ctx.0)
	}

	fn try_lit(
		&self,
		ctx: &SimplificationContext<'_>,
		meaning: IntLitMeaning,
	) -> Option<<SimplificationContext<'_> as ReasoningContext>::Atom> {
		self.try_lit(&*ctx.0, meaning)
	}

	fn val(&self, ctx: &SimplificationContext<'_>) -> Option<IntVal> {
		self.val(&*ctx.0)
	}
}
