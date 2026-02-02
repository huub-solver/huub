//! Integer decision variable definitions for the model layer.

use std::mem;

use rangelist::{IntervalIterator, RangeList};

use crate::{
	IntSet, IntVal,
	actions::{
		IntDecisionActions, IntInspectionActions, IntPropagationActions, IntSimplificationActions,
		ReasoningContext,
	},
	constraints::ReasonBuilder,
	model::{
		AdvRef, ConRef, Decision, Model,
		decision::{DecisionReference, private},
		view::{View, boolean::BoolView, integer::IntView},
	},
	solver::{
		IntLitMeaning,
		activation_list::{ActivationAction, ActivationList, IntEvent, IntPropCond},
	},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Wrapper type to distinguish between a variable with a domain, and an alias
/// to another variable.
pub(crate) enum Domain<E, Alias> {
	/// A normal variable with a domain.
	Domain(E),
	/// An alias to another variable.
	Alias(Alias),
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Definition of an integer decision variable in a [`Model`].
pub(crate) struct IntDecision {
	/// The set of possible values that the variable can take.
	pub(crate) domain: Domain<IntSet, View<IntVal>>,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: ActivationList,
}

impl Decision<IntVal> {
	/// Return the index used to access this decision in model storage.
	pub(crate) fn idx(&self) -> usize {
		self.0 as usize
	}

	/// Internal method performing unification under the assumption that the
	/// receiver is an integer decision index that is not already aliased, and
	/// that it can be aliased to directly point to `other`.
	pub(crate) fn unify_internal(
		&self,
		ctx: &mut Model,
		target: View<IntVal>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		debug_assert!(matches!(
			ctx.int_vars[self.idx()].domain,
			Domain::Domain(_) | Domain::Alias(View(IntView::Const(_)))
		));

		// Set the domain on the variable to be aliased to trigger subscription
		// events.
		self.restrict_domain(ctx, &target.domain(ctx), [])?;
		// Change variable to point to the target
		match mem::replace(&mut ctx.int_vars[self.idx()].domain, Domain::Alias(target)) {
			// Restrict the domain of the target variable using the variable domain
			// being aliased.
			Domain::Domain(dom) => target.restrict_domain(ctx, &dom, [])?,
			Domain::Alias(View(IntView::Const(v))) => target.fix(ctx, v, [])?,
			_ => unreachable!(),
		};
		// Transfer any constraints from the aliased variable to the target variable
		let constraints = mem::take(&mut ctx.int_vars[self.idx()].constraints);
		// Move subscriptions to target decision variable
		match target.0 {
			IntView::Linear(lin) => {
				ctx.int_vars[lin.var.idx()].constraints.extend(constraints);
			}
			IntView::Bool(lin) => match lin.var.0 {
				inner @ (BoolView::IntEq(j, _)
				| BoolView::IntNotEq(j, _)
				| BoolView::IntGreaterEq(j, _)
				| BoolView::IntLess(j, _)) => {
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<AdvRef, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut ctx.advisors[adv.index()];
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
							ctx.int_vars[j.idx()].constraints.add(act, cond);
						},
					);
				}
				// Move subscription to Boolean decision
				BoolView::Decision(l) => {
					let jdx = l.idx();
					constraints.for_each_activated_by(
						IntEvent::Fixed,
						|act: ActivationAction<AdvRef, ConRef>| {
							if let ActivationAction::Advise(adv) = act {
								let def = &mut ctx.advisors[adv.index()];
								def.bool2int = true;
								def.negated = false;
							}
							ctx.bool_vars[jdx].constraints.push(act.into());
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

impl IntDecisionActions<Model> for Decision<IntVal> {
	fn lit(&self, ctx: &mut Model, meaning: IntLitMeaning) -> View<bool> {
		IntInspectionActions::try_lit(self, ctx, meaning).unwrap()
	}

	fn val_lit(&self, ctx: &mut Model) -> Option<View<bool>> {
		let val = self.val(ctx)?;
		Some(View(BoolView::IntEq(*self, val)))
	}
}

impl IntInspectionActions<Model> for Decision<IntVal> {
	fn bounds(&self, ctx: &Model) -> (IntVal, IntVal) {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => (*d.lower_bound().unwrap(), *d.upper_bound().unwrap()),
			Domain::Alias(alias) => alias.bounds(ctx),
		}
	}

	fn domain(&self, ctx: &Model) -> IntSet {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d.clone(),
			Domain::Alias(alias) => alias.domain(ctx),
		}
	}

	fn in_domain(&self, ctx: &Model, val: IntVal) -> bool {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d.contains(&val),
			Domain::Alias(alias) => alias.in_domain(ctx, val),
		}
	}

	fn lit_meaning(
		&self,
		_: &Model,
		lit: <Model as ReasoningContext>::Atom,
	) -> Option<IntLitMeaning> {
		match lit.0 {
			BoolView::IntEq(idx, val) if idx == *self => Some(IntLitMeaning::Eq(val)),
			BoolView::IntGreaterEq(idx, val) if idx == *self => Some(IntLitMeaning::GreaterEq(val)),
			BoolView::IntLess(idx, val) if idx == *self => Some(IntLitMeaning::Less(val)),
			BoolView::IntNotEq(idx, val) if idx == *self => Some(IntLitMeaning::NotEq(val)),
			_ => None,
		}
	}

	fn max(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => *d.upper_bound().unwrap(),
			Domain::Alias(alias) => alias.max(ctx),
		}
	}

	fn max_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d
				.lower_bound()
				.map(|&val| View(BoolView::IntLess(*self, val + 1)))
				.unwrap(),
			Domain::Alias(alias) => alias.max_lit(ctx),
		}
	}

	fn min(&self, ctx: &Model) -> IntVal {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => *d.lower_bound().unwrap(),
			Domain::Alias(alias) => alias.min(ctx),
		}
	}

	fn min_lit(&self, ctx: &Model) -> <Model as ReasoningContext>::Atom {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => d
				.lower_bound()
				.map(|&val| View(BoolView::IntGreaterEq(*self, val)))
				.unwrap(),
			Domain::Alias(alias) => alias.min_lit(ctx),
		}
	}

	fn try_lit(
		&self,
		ctx: &Model,
		meaning: IntLitMeaning,
	) -> Option<<Model as ReasoningContext>::Atom> {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(_) => Some(View(match meaning {
				IntLitMeaning::Eq(v) => BoolView::IntEq(*self, v),
				IntLitMeaning::NotEq(v) => BoolView::IntNotEq(*self, v),
				IntLitMeaning::GreaterEq(v) => BoolView::IntGreaterEq(*self, v),
				IntLitMeaning::Less(v) => BoolView::IntLess(*self, v),
			})),
			Domain::Alias(alias) => alias.try_lit(ctx, meaning),
		}
	}

	fn val(&self, ctx: &Model) -> Option<IntVal> {
		match &ctx.int_vars[self.idx()].domain {
			Domain::Domain(d) => {
				let (lb, ub) = (d.lower_bound().unwrap(), d.upper_bound().unwrap());
				if lb == ub { Some(*lb) } else { None }
			}
			Domain::Alias(alias) => alias.val(ctx),
		}
	}
}

impl IntPropagationActions<Model> for Decision<IntVal> {
	fn fix(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[self.idx()];
		let Domain::Domain(dom) = &def.domain else {
			unreachable!()
		};
		if dom.contains(&val) {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(self.0, IntEvent::Fixed);
			Ok(())
		} else {
			Err(ctx.create_conflict(View(BoolView::IntEq(*self, val)), reason))
		}
	}

	fn remove_val(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		self.exclude(ctx, &(val..=val).into(), reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[self.idx()];
		let Domain::Domain(dom) = &mut def.domain else {
			unreachable!()
		};
		if val >= *dom.upper_bound().unwrap() {
			return Ok(());
		} else if val < *dom.lower_bound().unwrap() {
			return Err(ctx.create_conflict(View(BoolView::IntLess(*self, val + 1)), reason));
		}
		if val != *dom.lower_bound().unwrap() {
			dom.set_upper_bound(val);
			ctx.int_events
				.entry(self.0)
				.and_modify(|v| *v += IntEvent::UpperBound)
				.or_insert(IntEvent::UpperBound);
		} else {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(self.0, IntEvent::Fixed);
		};
		Ok(())
	}

	fn tighten_min(
		&self,
		ctx: &mut Model,
		val: IntVal,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let def = &mut ctx.int_vars[self.idx()];
		let Domain::Domain(dom) = &mut def.domain else {
			unreachable!()
		};
		if val <= *dom.lower_bound().unwrap() {
			return Ok(());
		} else if val > *dom.upper_bound().unwrap() {
			return Err(ctx.create_conflict(View(BoolView::IntGreaterEq(*self, val)), reason));
		}
		if val != *dom.upper_bound().unwrap() {
			dom.set_lower_bound(val);
			ctx.int_events
				.entry(self.0)
				.and_modify(|e| *e += IntEvent::LowerBound)
				.or_insert(IntEvent::LowerBound);
		} else {
			def.domain = Domain::Alias(val.into());
			ctx.int_events.insert(self.0, IntEvent::Fixed);
		};
		Ok(())
	}
}

impl IntSimplificationActions<Model> for Decision<IntVal> {
	fn exclude(
		&self,
		ctx: &mut Model,
		values: &IntSet,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let Domain::Domain(dom) = &ctx.int_vars[self.idx()].domain else {
			unreachable!()
		};
		let diff: RangeList<_> = dom.diff(values);
		if diff.is_empty() {
			return Err(ctx.create_conflict(
				View(BoolView::IntNotEq(*self, *values.lower_bound().unwrap())),
				reason,
			));
		}
		if *dom == diff {
			return Ok(());
		}
		if diff.card() == Some(1) {
			let val = *diff.lower_bound().unwrap();
			ctx.int_vars[self.idx()].domain = Domain::Alias(val.into());
			ctx.int_events.insert(self.0, IntEvent::Fixed);
		} else {
			let entry = ctx.int_events.entry(self.0).or_insert(IntEvent::Domain);
			if dom.lower_bound().unwrap() == diff.lower_bound().unwrap() {
				*entry += IntEvent::LowerBound;
			}
			if dom.upper_bound().unwrap() == diff.upper_bound().unwrap() {
				*entry += IntEvent::UpperBound;
			}

			ctx.int_vars[self.idx()].domain = Domain::Domain(diff);
		};
		Ok(())
	}

	fn restrict_domain(
		&self,
		ctx: &mut Model,
		domain: &IntSet,
		reason: impl ReasonBuilder<Model>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let Domain::Domain(dom) = &ctx.int_vars[self.idx()].domain else {
			unreachable!()
		};
		let intersect: RangeList<_> = dom.intersect(domain);
		if intersect.is_empty() {
			return Err(ctx.create_conflict(
				View(BoolView::IntNotEq(*self, *dom.lower_bound().unwrap())),
				reason,
			));
		} else if *dom == intersect {
			return Ok(());
		}
		if intersect.card() == Some(1) {
			let val = *intersect.lower_bound().unwrap();
			ctx.int_vars[self.idx()].domain = Domain::Alias(val.into());
			ctx.int_events.insert(self.0, IntEvent::Fixed);
		} else {
			let entry = ctx.int_events.entry(self.0).or_insert(IntEvent::Domain);
			if dom.lower_bound().unwrap() == intersect.lower_bound().unwrap() {
				*entry += IntEvent::LowerBound;
			}
			if dom.upper_bound().unwrap() == intersect.upper_bound().unwrap() {
				*entry += IntEvent::UpperBound;
			}

			ctx.int_vars[self.idx()].domain = Domain::Domain(intersect);
		}
		Ok(())
	}

	fn unify(
		&self,
		ctx: &mut Model,
		other: impl Into<Self>,
	) -> Result<(), <Model as ReasoningContext>::Conflict> {
		let other: Decision<IntVal> = other.into();
		View::<IntVal>::from(*self).unify(ctx, other)
	}
}

impl IntDecision {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSet) -> Self {
		Self {
			domain: Domain::Domain(dom),
			constraints: Default::default(),
		}
	}
}

impl DecisionReference for IntVal {
	type Ref = u32;
}
impl private::Sealed for IntVal {}
