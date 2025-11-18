//! during the propagation and solution checking process. This structure
//! contains the implementation of the actions that are exposed to the
//! propagators.
//! Module containing the [`SolvingContext`] structure used to take actions

use std::fmt::{self, Debug, Formatter};

use index_vec::IndexVec;
use pindakaas::{solver::propagation::SolvingActions, Lit as RawLit};
use tracing::trace;

use crate::{
	actions::{
		BoolInspectionActions, BoolPropagationActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, IntPropagationActions, PropagationActions, ReasoningContext,
		ReasoningEngine, TrailingActions,
	},
	constraints::{Conflict, LazyReason, Reason, ReasonBuilder},
	solver::{
		activation_list::IntEvent,
		engine::{trace_new_lit, Engine, LitPropagation, PropRef, State},
		int_var::{IntVarRef, LazyLitDef},
		trail::TrailedInt,
		BoolView, BoolViewInner, BoxedPropagator,
	},
	IntLitMeaning, IntSetVal, IntVal,
};

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
struct ReasonTracePrint<'a>(&'a Result<Reason<RawLit>, bool>);

/// Structure to hold the internal [`State`] of the propagation engine and the
/// [`SolvingActions`] exposed by the SAT oracle.
///
/// This structure is used to run the propagators that have been scheduled.
///
/// Note that this structure is public to the user to allow the user to
/// construct [`BoxedPropagator`] and [`BoxedBrancher`], but it is not intended
/// to be constructed by the user. It should merely be seen as the
/// implementation of the [`PropagationActions`] trait.
pub struct SolvingContext<'a> {
	/// Actions to create new variables in the oracle
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object
	pub(crate) state: &'a mut State,
	/// Current propagator being executed
	pub(crate) current_prop: PropRef,
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for BoolView {
	fn set(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		match self.0 {
			BoolViewInner::Lit(lit) => lit.set(ctx, reason),
			BoolViewInner::Const(false) => Err(Conflict::new(ctx, None, reason)),
			BoolViewInner::Const(true) => Ok(()),
		}
	}

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		if val { *self } else { !(*self) }.set(ctx, reason)
	}
}

impl IntDecisionActions<SolvingContext<'_>> for IntVarRef {
	fn lit(&self, ctx: &mut SolvingContext<'_>, meaning: IntLitMeaning) -> BoolView {
		let var = &mut ctx.state.int_vars[*self];
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

impl IntInspectionActions<SolvingContext<'_>> for IntVarRef {
	fn domain(&self, ctx: &SolvingContext<'_>) -> IntSetVal {
		self.domain(ctx.state)
	}

	fn in_domain(&self, ctx: &SolvingContext<'_>, val: IntVal) -> bool {
		self.in_domain(ctx.state, val)
	}

	fn lit_meaning(&self, ctx: &SolvingContext<'_>, lit: BoolView) -> Option<IntLitMeaning> {
		self.lit_meaning(ctx.state, lit)
	}

	fn lower_bound(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.lower_bound(ctx.state)
	}

	fn lower_bound_lit(&self, ctx: &SolvingContext<'_>) -> BoolView {
		self.lower_bound_lit(ctx.state)
	}

	fn try_lit(&self, ctx: &SolvingContext<'_>, meaning: IntLitMeaning) -> Option<BoolView> {
		self.try_lit(ctx.state, meaning)
	}

	fn upper_bound(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.upper_bound(ctx.state)
	}

	fn upper_bound_lit(&self, ctx: &SolvingContext<'_>) -> BoolView {
		self.upper_bound_lit(ctx.state)
	}

	fn bounds(&self, ctx: &SolvingContext<'_>) -> (IntVal, IntVal) {
		self.bounds(ctx.state)
	}

	fn val(&self, ctx: &SolvingContext<'_>) -> Option<IntVal> {
		self.val(ctx.state)
	}
}

impl<'a> IntPropagationActions<SolvingContext<'a>> for IntVarRef {
	fn set_lower_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		ctx.propagate_int(*self, IntLitMeaning::GreaterEq(val), reason)
	}

	fn set_not_eq(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		ctx.propagate_int(*self, IntLitMeaning::NotEq(val), reason)
	}

	fn set_upper_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		ctx.propagate_int(*self, IntLitMeaning::Less(val + 1), reason)
	}

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		ctx.propagate_int(*self, IntLitMeaning::Eq(val), reason)
	}
}

impl BoolInspectionActions<SolvingContext<'_>> for RawLit {
	fn val(&self, ctx: &SolvingContext<'_>) -> Option<bool> {
		self.val(ctx.state)
	}
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for RawLit {
	fn set(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		match ctx.state.trail.sat_value(*self) {
			Some(true) => Ok(()),
			Some(false) => Err(Conflict::new(ctx, Some(*self), reason)),
			None => {
				ctx.propagate_lit(*self, reason, None);
				Ok(())
			}
		}
	}

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		if val { *self } else { !(*self) }.set(ctx, reason)
	}
}

impl Debug for ReasonTracePrint<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match self.0 {
			Err(false) => write!(f, "false"),
			Err(true) => write!(f, "[]"),
			Ok(Reason::Eager(conj)) => conj.iter().map(|&l| l.into()).collect::<Vec<i32>>().fmt(f),
			Ok(Reason::Lazy(_)) => write!(f, "lazy"),
			&Ok(Reason::Simple(l)) => vec![i32::from(l)].fmt(f),
		}
	}
}

impl<'a> SolvingContext<'a> {
	/// Create a new SolvingContext given the solver actions exposed by the SAT
	/// oracle and the engine state.
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropRef::new(i32::MAX as usize),
		}
	}

	#[inline]
	/// Internal method used to propagate an integer variable given a literal
	/// description to be enforced.
	fn propagate_int(
		&mut self,
		iv: IntVarRef,
		lit_req: IntLitMeaning,
		reason: impl ReasonBuilder<Self, BoolView>,
	) -> Result<(), Conflict<RawLit>> {
		let (lb, ub) = self.state.int_vars[iv].bounds(self);
		// Check whether a change is redundant, conflicting, or new with respect to
		// the bounds of an integer variable
		let check = match lit_req {
			IntLitMeaning::Eq(i) if lb == i && ub == i => ChangeType::Redundant,
			IntLitMeaning::Eq(i) if i < lb || i > ub => ChangeType::Conflicting,
			IntLitMeaning::NotEq(i) if i < lb || i > ub => ChangeType::Redundant,
			IntLitMeaning::GreaterEq(i) if i <= lb => ChangeType::Redundant,
			IntLitMeaning::GreaterEq(i) if i > ub => ChangeType::Conflicting,
			IntLitMeaning::Less(i) if i > ub => ChangeType::Redundant,
			IntLitMeaning::Less(i) if i <= lb => ChangeType::Conflicting,
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
		let (bv, lit_req) = self.state.int_vars[iv].lit(lit_req, new_var);

		// Detect propagation conflicts:
		// 1. Always false (and immediate return if always true).
		let lit = match bv.0 {
			BoolViewInner::Const(true) => return Ok(()),
			BoolViewInner::Const(false) => return Err(Conflict::new(self, None, reason)),
			BoolViewInner::Lit(lit) => lit,
		};
		// 2. Bounds check is known to be false.
		if check == ChangeType::Conflicting {
			return Err(Conflict::new(self, lit.into(), reason));
		}
		// 3. Literal is assigned false (and immediate return if assigned true).
		match self.state.trail.sat_value(lit) {
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
				self.state.int_vars[iv].notify_lower_bound(&mut self.state.trail, val);
				self.state.int_vars[iv].notify_upper_bound(&mut self.state.trail, val);
			}
			IntLitMeaning::NotEq(_) => {}
			IntLitMeaning::GreaterEq(lb) => {
				self.state.int_vars[iv].notify_lower_bound(&mut self.state.trail, lb);
			}
			IntLitMeaning::Less(ub) => {
				self.state.int_vars[iv].notify_upper_bound(&mut self.state.trail, ub - 1);
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
		lit: RawLit,
		reason: impl ReasonBuilder<Self, BoolView>,
		event: Option<(IntVarRef, IntEvent)>,
	) {
		let reason = Reason::from_view(reason.build_reason(self));
		trace!(
			lit = i32::from(lit),
			reason = ?ReasonTracePrint(&reason),
			prop = usize::from(self.current_prop),
			"propagate"
		);
		self.state
			.propagation_queue
			.push_back(LitPropagation { lit, reason, event });
		let _prev = self.state.trail.assign_lit(lit);
		debug_assert_eq!(_prev, None);
	}

	/// Run the propagators in the queue until a propagator detects a conflict,
	/// returns literals to be propagated by the SAT oracle, or the queue is
	/// empty.
	pub(crate) fn run_propagators(&mut self, propagators: &mut IndexVec<PropRef, BoxedPropagator>) {
		while let Some(p) = self.state.propagator_queue.pop() {
			debug_assert!(!self.state.failed);
			debug_assert!(self.state.conflict.is_none());
			self.current_prop = p;
			let prop = propagators[p].as_mut();
			let res = prop.propagate(self);
			self.state.statistics.propagations += 1;
			self.current_prop = PropRef::new(i32::MAX as usize);
			if let Err(conflict) = res {
				trace!(
					lit = conflict
						.subject
						.map(i32::from)
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
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self, BoolView>) -> Conflict<RawLit> {
		Conflict::new(self, None, reason)
	}

	fn deferred_reason(&self, data: u64) -> LazyReason {
		LazyReason {
			propagator: self.current_prop.raw(),
			data,
		}
	}
}

impl TrailingActions for SolvingContext<'_> {
	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal {
		self.state.set_trailed_int(x, v)
	}

	fn trailed_int(&self, x: TrailedInt) -> IntVal {
		self.state.trailed_int(x)
	}
}

impl ReasoningContext for SolvingContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}
