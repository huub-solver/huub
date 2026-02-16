//! during the propagation and solution checking process. This structure
//! contains the implementation of the actions that are exposed to the
//! propagators.
//! Module containing the [`SolvingContext`] structure used to take actions

use std::fmt::{self, Debug, Formatter};

use pindakaas::solver::propagation::SolvingActions;
use tracing::trace;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, BoolPropagationActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, IntPropagationActions, PropagationActions, ReasoningContext,
		ReasoningEngine, Trailed, TrailingActions,
	},
	constraints::{Conflict, DeferredReason, Reason, ReasonBuilder},
	helpers::bytes::Bytes,
	solver::{
		BoxedPropagator, IntLitMeaning,
		activation_list::IntEvent,
		decision::{Decision, integer::LazyLitDef},
		engine::{Engine, LitPropagation, PropRef, State, trace_new_lit},
		view::{View, boolean::BoolView},
	},
};

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
/// Argument type for [`SolvingContext::propagate_int`] to communicate what
/// change to make to the integer decision variable.
///
/// Note that this enum is slightly different from [`IntLitMeaning`] in that it
/// represents the the actual upper bound (less-eq), rather than
/// [`IntLitMeaning::Less`], which has to add `1` potentially causing overflow.
enum ChangeRequest {
	/// Set the lower bound of the integer decision variable to the given value.
	SetLowerBound(IntVal),
	/// Set the upper bound of the integer decision variable to the given value.
	SetUpperBound(IntVal),
	/// Set the value of the integer decision variable to the given value.
	SetValue(IntVal),
	/// Remove the given value from the domain of the integer decision variable.
	RemoveValue(IntVal),
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
/// Type used to communicate whether a change is redundant, conflicting, or new.
enum ChangeType {
	/// Change is redundant, no action needs to be taken.
	Redundant,
	/// Change is new and should be propagated.
	New,
	/// Change is conflicting, and a conflict should be raised.
	Conflicting,
}

/// Helper struct that temporarily captures a built reason to print it for
/// `tracing`.
struct ReasonTracePrint<'a>(&'a Result<Reason<Decision<bool>>, bool>);

/// Structure to hold the internal [`State`] of the propagation engine and the
/// [`SolvingActions`] exposed by the SAT solver.
///
/// This structure is used to run the propagators that have been scheduled.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`BoxedPropagator`] and [`BoxedBrancher`], but it is not intended
/// to be constructed by the user. It should merely be seen as the
/// implementation of the [`PropagationActions`] trait.
pub struct SolvingContext<'a> {
	/// Actions to create new variables in the solver
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object
	pub(crate) state: &'a mut State,
	/// Current propagator being executed
	pub(crate) current_prop: PropRef,
}

impl BoolInspectionActions<SolvingContext<'_>> for Decision<bool> {
	fn val(&self, ctx: &SolvingContext<'_>) -> Option<bool> {
		self.val(ctx.state)
	}
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for Decision<bool> {
	fn fix(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		if val { *self } else { !(*self) }.require(ctx, reason)
	}

	fn require(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		match self.val(&ctx.state.trail) {
			Some(true) => Ok(()),
			Some(false) => Err(Conflict::new(ctx, Some(*self), reason)),
			None => {
				ctx.propagate_lit(*self, reason, None);
				Ok(())
			}
		}
	}
}

impl IntDecisionActions<SolvingContext<'_>> for Decision<IntVal> {
	fn lit(&self, ctx: &mut SolvingContext<'_>, meaning: IntLitMeaning) -> View<bool> {
		let var = &mut ctx.state.int_vars[self.idx()];
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = ctx.slv.new_observed_var();
			ctx.state.trail.grow_to_boolvar(v);
			trace_new_lit!(*self, def, v);
			ctx.state.bool_to_int.insert_lazy(v, *self, def.meaning);
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				ctx.state.clauses.push_back(cl);
			}
			v
		};
		var.lit(meaning, new_var).0
	}
}

impl IntInspectionActions<SolvingContext<'_>> for Decision<IntVal> {
	fn bounds(&self, ctx: &SolvingContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.state)
	}

	fn domain(&self, ctx: &SolvingContext<'_>) -> IntSet {
		self.domain(ctx.state)
	}

	fn in_domain(&self, ctx: &SolvingContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.state, val)
	}

	fn lit_meaning(&self, ctx: &SolvingContext<'_>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.state, lit)
	}

	fn max(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.max(ctx.state)
	}

	fn max_lit(&self, ctx: &SolvingContext<'_>) -> View<bool> {
		self.max_lit(ctx.state)
	}

	fn min(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.min(ctx.state)
	}

	fn min_lit(&self, ctx: &SolvingContext<'_>) -> View<bool> {
		self.min_lit(ctx.state)
	}

	fn try_lit(&self, ctx: &SolvingContext<'_>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(ctx.state, meaning)
	}

	fn val(&self, ctx: &SolvingContext<'_>) -> Option<IntVal> {
		self.val(ctx.state)
	}
}

impl<'a> IntPropagationActions<SolvingContext<'a>> for Decision<IntVal> {
	fn fix(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetValue(val), reason)
	}

	fn remove_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::RemoveValue(val), reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetUpperBound(val), reason)
	}

	fn tighten_min(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetLowerBound(val), reason)
	}
}

impl Debug for ReasonTracePrint<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match self.0 {
			Err(false) => write!(f, "false"),
			Err(true) => write!(f, "[]"),
			Ok(Reason::Eager(conj)) => conj
				.iter()
				.map(|&l| l.0.into())
				.collect::<Vec<i32>>()
				.fmt(f),
			Ok(Reason::Lazy(_)) => write!(f, "lazy"),
			&Ok(Reason::Simple(l)) => vec![i32::from(l.0)].fmt(f),
		}
	}
}

impl<'a> SolvingContext<'a> {
	/// Create a new SolvingContext given the solver actions exposed by the SAT
	/// solver and the engine state.
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropRef::INVALID,
		}
	}

	#[inline]
	/// Internal method used to propagate an integer variable given a literal
	/// description to be enforced.
	fn propagate_int(
		&mut self,
		iv: Decision<IntVal>,
		change_req: ChangeRequest,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict<Decision<bool>>> {
		let (lb, ub) = self.state.int_vars[iv.idx()].bounds(self);
		// Check whether a change is redundant, conflicting, or new with respect to
		// the bounds of an integer variable
		let check = match change_req {
			ChangeRequest::SetValue(i) if lb == i && ub == i => ChangeType::Redundant,
			ChangeRequest::SetValue(i) if i < lb || i > ub => ChangeType::Conflicting,
			ChangeRequest::RemoveValue(i) if i < lb || i > ub => ChangeType::Redundant,
			ChangeRequest::SetLowerBound(i) if i <= lb => ChangeType::Redundant,
			ChangeRequest::SetLowerBound(i) if i > ub => ChangeType::Conflicting,
			ChangeRequest::SetUpperBound(i) if i >= ub => ChangeType::Redundant,
			ChangeRequest::SetUpperBound(i) if i < lb => ChangeType::Conflicting,
			_ => ChangeType::New,
		};

		// Immediate return if there are no further changes
		if check == ChangeType::Redundant {
			return Ok(());
		}

		// Find the right literal, required whether we want to propagate, or raise a
		// conflict
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = self.slv.new_observed_var();
			self.state.trail.grow_to_boolvar(v);
			trace_new_lit!(iv, def, v);
			self.state.bool_to_int.insert_lazy(v, iv, def.meaning);
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				self.state.clauses.push_back(cl);
			}
			v
		};
		let (bv, lit_req) = self.state.int_vars[iv.idx()].lit(
			match change_req {
				ChangeRequest::SetLowerBound(i) => IntLitMeaning::GreaterEq(i),
				ChangeRequest::SetUpperBound(i) => IntLitMeaning::Less(i + 1),
				ChangeRequest::SetValue(i) => IntLitMeaning::Eq(i),
				ChangeRequest::RemoveValue(i) => IntLitMeaning::NotEq(i),
			},
			new_var,
		);

		// Detect propagation conflicts:
		// 1. Always false (and immediate return if always true).
		let lit = match bv.0 {
			BoolView::Const(true) => return Ok(()),
			BoolView::Const(false) => return Err(Conflict::new(self, None, reason)),
			BoolView::Lit(lit) => lit,
		};
		// 2. Bounds check is known to be false.
		if check == ChangeType::Conflicting {
			return Err(Conflict::new(self, lit.into(), reason));
		}
		// 3. Literal is assigned false (and immediate return if assigned true).
		match lit.val(&self.state.trail) {
			Some(true) => return Ok(()),
			Some(false) => return Err(Conflict::new(self, lit.into(), reason)),
			None => {}
		}

		// Normal case:
		// Propagate the literal.
		let event = match lit_req {
			IntLitMeaning::Eq(_) => IntEvent::Fixed,
			IntLitMeaning::NotEq(_) => IntEvent::Domain,
			IntLitMeaning::GreaterEq(_) => IntEvent::LowerBound,
			IntLitMeaning::Less(_) => IntEvent::UpperBound,
		};
		self.propagate_lit(lit, reason, Some((iv, event)));
		// Make the domains match.
		match lit_req {
			IntLitMeaning::Eq(val) => {
				self.state.int_vars[iv.idx()].notify_lower_bound(&mut self.state.trail, val);
				self.state.int_vars[iv.idx()].notify_upper_bound(&mut self.state.trail, val);
			}
			IntLitMeaning::NotEq(_) => {}
			IntLitMeaning::GreaterEq(lb) => {
				self.state.int_vars[iv.idx()].notify_lower_bound(&mut self.state.trail, lb);
			}
			IntLitMeaning::Less(ub) => {
				self.state.int_vars[iv.idx()].notify_upper_bound(&mut self.state.trail, ub - 1);
			}
		};
		Ok(())
	}

	#[inline]
	/// Internal method used to propagate a Boolean literal.
	///
	/// ## Warning
	///
	/// This method assumes that the literal has not already been assigned, not
	/// even to the same value.
	fn propagate_lit(
		&mut self,
		lit: Decision<bool>,
		reason: impl ReasonBuilder<Self>,
		event: Option<(Decision<IntVal>, IntEvent)>,
	) {
		let reason = Reason::from_view(reason.build_reason(self));
		trace!(
			lit = i32::from(lit.0),
			reason = ?ReasonTracePrint(&reason),
			prop = self.current_prop.index(),
			"propagate"
		);
		self.state.propagation_queue.push_back(LitPropagation {
			lit: lit.0,
			reason,
			event,
		});
		let _prev = self.state.trail.assign_lit(lit.0);
		debug_assert_eq!(_prev, None);
	}

	/// Run the propagators in the queue until a propagator detects a conflict,
	/// returns literals to be propagated by the SAT solver, or the queue is
	/// empty.
	pub(crate) fn run_propagators(&mut self, propagators: &mut [BoxedPropagator]) {
		while let Some(p) = self.state.propagator_queue.pop() {
			debug_assert!(!self.state.failed);
			debug_assert!(self.state.conflict.is_none());
			self.current_prop = PropRef::from_raw(p);
			let prop = propagators[self.current_prop.index()].as_mut();
			let res = prop.propagate(self);
			self.state.statistics.propagations += 1;
			self.current_prop = PropRef::INVALID;
			if let Err(conflict) = res {
				trace!(
					lit = conflict
						.subject
						.map(|s| i32::from(s.0))
						.unwrap_or_default(),
					reason = ?ReasonTracePrint(&Ok(conflict.reason.clone())),
					"conflict detected"
				);
				debug_assert!(self.state.conflict.is_none());
				self.state.failed = true;
				self.state.conflict = Some(conflict);
			}
			if self.state.conflict.is_some() || !self.state.propagation_queue.is_empty() {
				return;
			}
		}
	}
}

impl Debug for SolvingContext<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("SolvingContext")
			.field("state", &self.state)
			.field("current_prop", &self.current_prop)
			.finish()
	}
}

impl DecisionActions for SolvingContext<'_> {
	fn num_conflicts(&self) -> u64 {
		self.state.statistics.conflicts
	}
}

impl PropagationActions for SolvingContext<'_> {
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self>) -> Conflict<Decision<bool>> {
		Conflict::new(self, None, reason)
	}

	fn deferred_reason(&self, data: u64) -> DeferredReason {
		DeferredReason {
			propagator: self.current_prop.index() as u32,
			data,
		}
	}
}

impl ReasoningContext for SolvingContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl TrailingActions for SolvingContext<'_> {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		self.state.set_trailed(i, v)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		self.state.trailed(i)
	}
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for View<bool> {
	fn fix(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		if val { *self } else { !(*self) }.require(ctx, reason)
	}

	fn require(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		match self.0 {
			BoolView::Lit(lit) => lit.require(ctx, reason),
			BoolView::Const(false) => Err(Conflict::new(ctx, None, reason)),
			BoolView::Const(true) => Ok(()),
		}
	}
}
