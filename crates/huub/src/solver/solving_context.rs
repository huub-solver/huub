//! The [`SolvingContext`] structure used to take actions during propagation
//! and solution checking.
//!
//! This structure contains the implementation of the action traits that are
//! exposed to propagators.

use std::{
	fmt::{self, Debug, Formatter},
	mem,
};

use pindakaas::{
	Lit as RawLit,
	solver::propagation::{ClauseBuilder, SolvingActions},
};
use tracing::{trace, warn};

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, BoolPropagationActions, DecisionActions, DeferReasonActions,
		IntDecisionActions, IntEvent, IntInspectionActions, IntPropagationActions,
		PropagationActions, PropagationContext, ReasonActions, ReasoningContext, ReasoningEngine,
		Trailed, TrailingActions,
	},
	constraints::{Conflict, ConflictInner},
	helpers::bytes::Bytes,
	solver::{
		BoxedPropagator, IntLitMeaning, Polarity,
		decision::{Decision, integer::LazyLitDef},
		engine::{
			Engine, EngineReason, EngineReasonSink, LitPropagation, PropagatorId, State,
			trace_new_lit,
		},
		view::{View, boolean::BoolView},
	},
};

/// Argument type for [`SolvingContext::propagate_int`] to communicate what
/// change to make to the integer decision variable.
///
/// Note that this enum is slightly different from [`IntLitMeaning`] in that it
/// represents the actual upper bound (less-eq), rather than
/// [`IntLitMeaning::Less`], which has to add `1` potentially causing overflow.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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

/// Type used to communicate whether a change is redundant, conflicting, or new.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ChangeType {
	/// Change is redundant, no action needs to be taken.
	Redundant,
	/// Change is new and should be propagated.
	New,
	/// Change is conflicting, and a conflict should be raised.
	Conflicting,
}

/// Helper struct that prints a [`Conflict`]'s nogood compactly for `tracing`.
struct ConflictTracePrint<'a, A>(&'a Conflict<A>);

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
	/// Actions to create new variables in the solver.
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object.
	pub(crate) state: &'a mut State,
	/// Current propagator being executed.
	pub(crate) current_prop: PropagatorId,
}

/// The reason-build sink for the engine's [`SolvingContext`]: a reason closure
/// either pushes the negated its reason atoms onto the reason trail (through
/// the wrapped [`EngineReasonSink`]) or defers the reason to the current
/// propagator with [`DeferReasonActions::defer`].
#[derive(Debug)]
pub struct SolvingReasonSink<'a> {
	/// The sink that reason atoms are written to.
	pub(crate) conditions: EngineReasonSink<'a>,
	/// `Some(data)` once the reason has been deferred; the propagator index is
	/// folded in by the caller (which owns the current-propagator reference).
	pub(crate) deferred: Option<u64>,
}

impl<A: Debug> Debug for ConflictTracePrint<'_, A> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match &self.0.0 {
			ConflictInner::Clause(lits) => lits.fmt(f),
			ConflictInner::Deferred { subject, .. } => write!(f, "deferred for {subject:?}"),
		}
	}
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
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		if val { *self } else { !(*self) }.require(ctx, reason)
	}

	fn require(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		match self.val(&ctx.state.trail) {
			Some(true) => Ok(()),
			Some(false) => Err(ctx.make_conflict(Some(*self), reason)),
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
		let polarity = var.polarity;
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = ctx.slv.new_observed_var();
			// Apply a phase hint to newly created (lazy) order literals according
			// to the variable's polarity. The positive literal represents
			// `x < val`, so a positive polarity (prefer large values) phases the
			// negation. Direct (equality) literals are left unphased.
			if matches!(def.meaning, IntLitMeaning::Less(_)) {
				match polarity {
					Some(Polarity::Positive) => ctx.slv.phase(!Into::<RawLit>::into(v)),
					Some(Polarity::Negative) => ctx.slv.phase(v.into()),
					None => {}
				}
			}
			ctx.state.statistics.lazy_literals += 1;
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
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetValue(val), reason)
	}

	fn remove_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::RemoveValue(val), reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetUpperBound(val), reason)
	}

	fn tighten_min(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		ctx.propagate_int(*self, ChangeRequest::SetLowerBound(val), reason)
	}
}

impl<'a> SolvingContext<'a> {
	/// Build a [`Conflict`] from a reason closure, tightening the yielded
	/// [`View<bool>`] into [`Decision<bool>`].
	pub(crate) fn make_conflict(
		&mut self,
		subject: Option<Decision<bool>>,
		reason: impl FnOnce(&mut Self, &mut SolvingReasonSink<'_>),
	) -> Conflict<Decision<bool>> {
		let mut clause = Vec::new();
		let deferred = {
			let mut sink = SolvingReasonSink {
				conditions: EngineReasonSink(ClauseBuilder::new(&mut clause)),
				deferred: None,
			};
			reason(self, &mut sink);
			sink.deferred
		};
		match deferred {
			Some(data) => Conflict(ConflictInner::Deferred {
				subject,
				propagator: self.current_prop.index() as u32,
				data,
			}),
			None => {
				// `clause` holds the reason in (partial) clausal form; just add
				// the subject.
				let mut lits: Vec<Decision<bool>> = clause.into_iter().map(Decision).collect();
				match subject {
					Some(subject) => lits.push(subject),
					None if lits.is_empty() => warn!(
						target: "solver",
						"empty conflict detected; additional model simplification reasoning may be possible"
					),
					None => {}
				}
				Conflict(ConflictInner::Clause(lits.into_boxed_slice()))
			}
		}
	}

	/// Create a new SolvingContext given the solver actions exposed by the SAT
	/// solver and the engine state.
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropagatorId::INVALID,
		}
	}

	/// Internal method used to propagate an integer variable given a literal
	/// description to be enforced.
	#[inline]
	fn propagate_int(
		&mut self,
		iv: Decision<IntVal>,
		change_req: ChangeRequest,
		reason: impl FnOnce(&mut Self, &mut SolvingReasonSink<'_>),
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
			BoolView::Const(false) => return Err(self.make_conflict(None, reason)),
			BoolView::Lit(lit) => lit,
		};
		// 2. Bounds check is known to be false.
		if check == ChangeType::Conflicting {
			return Err(self.make_conflict(lit.into(), reason));
		}
		// 3. Literal is assigned false (and immediate return if assigned true).
		match lit.val(&self.state.trail) {
			Some(true) => return Ok(()),
			Some(false) => return Err(self.make_conflict(lit.into(), reason)),
			None => {}
		}

		// Normal case:
		// Propagate the literal.
		let event = match lit_req {
			IntLitMeaning::Eq(_) => IntEvent::Fixed,
			IntLitMeaning::NotEq(_) => IntEvent::Domain,
			IntLitMeaning::GreaterEq(i) if i == ub => IntEvent::Fixed,
			IntLitMeaning::GreaterEq(_) => IntEvent::LowerBound,
			IntLitMeaning::Less(i) if i == lb + 1 => IntEvent::Fixed,
			IntLitMeaning::Less(_) => IntEvent::UpperBound,
		};
		self.propagate_lit(lit, reason, Some((iv, event)));
		// Make the domains match.
		match lit_req {
			IntLitMeaning::Eq(val) => {
				// Only notify when a bound actually changes.
				if val > lb {
					self.state.int_vars[iv.idx()].notify_lower_bound(&mut self.state.trail, val);
				}
				if val < ub {
					self.state.int_vars[iv.idx()].notify_upper_bound(&mut self.state.trail, val);
				}
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

	/// Internal method used to propagate a Boolean literal.
	///
	/// ## Warning
	///
	/// This method assumes that the literal has not already been assigned, not
	/// even to the same value.
	#[inline]
	fn propagate_lit(
		&mut self,
		lit: Decision<bool>,
		reason: impl FnOnce(&mut Self, &mut SolvingReasonSink<'_>),
		event: Option<(Decision<IntVal>, IntEvent)>,
	) {
		// Build the reason directly onto the reason trail.
		let reason = self.with_reason_trail(|ctx, reason_trail| {
			let begin = reason_trail.len();
			let deferred = {
				let mut sink = SolvingReasonSink {
					conditions: EngineReasonSink(ClauseBuilder::new(reason_trail)),
					deferred: None,
				};
				reason(ctx, &mut sink);
				sink.deferred
			};
			let deferred = deferred.map(|data| (ctx.current_prop.index() as u32, data));
			EngineReason::finalize_reason(deferred, reason_trail, begin)
		});
		trace!(
			target: "solver",
			lit = i32::from(lit.0),
			reason = ?reason,
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

	/// Pop the next propagator from the queue and run it exactly once,
	/// returning its propagation result. Unlike [`Self::run_propagators`],
	/// this never advances past a single propagator, so the caller can inspect
	/// the effect of one propagator in isolation (the literals it propagated
	/// are left in `state.propagation_queue`).
	///
	/// Panics if the propagator queue is empty.
	#[cfg(test)]
	pub(crate) fn run_next_propagator(
		&mut self,
		propagators: &mut [BoxedPropagator],
	) -> Result<(), Conflict<Decision<bool>>> {
		let p = self
			.state
			.propagator_queue
			.pop()
			.expect("`run_next_propagator` called with an empty propagator queue");
		self.current_prop = PropagatorId::from_raw(p);
		let res = propagators[self.current_prop.index()]
			.as_mut()
			.propagate(self);
		self.state.statistics.propagations += 1;
		self.current_prop = PropagatorId::INVALID;
		res
	}

	/// Run the propagators in the queue until a propagator detects a conflict,
	/// returns literals to be propagated by the SAT solver, or the queue is
	/// empty.
	pub(crate) fn run_propagators(&mut self, propagators: &mut [BoxedPropagator]) {
		while let Some(p) = self.state.propagator_queue.pop() {
			debug_assert!(!self.state.failed);
			debug_assert!(self.state.conflict.is_none());
			self.current_prop = PropagatorId::from_raw(p);
			let prop = propagators[self.current_prop.index()].as_mut();
			let res = prop.propagate(self);
			self.state.statistics.propagations += 1;
			self.current_prop = PropagatorId::INVALID;
			if let Err(conflict) = res {
				trace!(
					target: "solver",
					conflict = ?ConflictTracePrint(&conflict),
					"conflict detected"
				);
				debug_assert!(self.state.conflict.is_none());
				self.state.failed = true;
				// Convert the conflict object into a conflict clause.
				let mut clause: Vec<RawLit> = Vec::new();
				conflict.explain(propagators, self.state, ClauseBuilder::new(&mut clause));
				self.state.conflict = Some(clause.into_boxed_slice());
			}
			if self.state.conflict.is_some() || !self.state.propagation_queue.is_empty() {
				return;
			}
		}
	}

	/// Run `build` with the reason trail temporarily taken out of the engine
	/// state, restoring it unconditionally afterwards.
	///
	/// The trail is handed to `build` as a `&mut Vec<RawLit>`.
	pub(crate) fn with_reason_trail<R>(
		&mut self,
		build: impl FnOnce(&mut Self, &mut Vec<RawLit>) -> R,
	) -> R {
		let mut reason_trail = mem::take(&mut self.state.trail.reason_trail);
		let result = build(self, &mut reason_trail);
		debug_assert!(self.state.trail.reason_trail.is_empty());
		self.state.trail.reason_trail = reason_trail;
		result
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
	fn declare_conflict(
		&mut self,
		reason: impl FnOnce(&mut Self, &mut SolvingReasonSink<'_>),
	) -> Conflict<Decision<bool>> {
		self.make_conflict(None, reason)
	}
}

impl PropagationContext for SolvingContext<'_> {
	type Conflict = <Engine as ReasoningEngine>::Conflict;
	type ReasonSink<'a> = SolvingReasonSink<'a>;
}

impl ReasoningContext for SolvingContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
}

impl TrailingActions for SolvingContext<'_> {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		self.state.set_trailed(i, v)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		self.state.trailed(i)
	}
}

impl DeferReasonActions<View<bool>> for SolvingReasonSink<'_> {
	fn defer(&mut self, data: u64) {
		self.deferred = Some(data);
	}
}

impl Extend<View<bool>> for SolvingReasonSink<'_> {
	fn extend<T: IntoIterator<Item = View<bool>>>(&mut self, iter: T) {
		self.conditions.extend(iter);
	}
}

impl ReasonActions<View<bool>> for SolvingReasonSink<'_> {
	fn push(&mut self, atom: View<bool>) {
		self.conditions.push(atom);
	}

	fn reserve(&mut self, additional: usize) {
		self.conditions.reserve(additional);
	}
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for View<bool> {
	fn fix(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		if val { *self } else { !(*self) }.require(ctx, reason)
	}

	fn require(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl FnOnce(&mut SolvingContext<'a>, &mut SolvingReasonSink<'_>),
	) -> Result<(), Conflict<Decision<bool>>> {
		match self.0 {
			BoolView::Lit(lit) => lit.require(ctx, reason),
			BoolView::Const(false) => Err(ctx.make_conflict(None, reason)),
			BoolView::Const(true) => Ok(()),
		}
	}
}
