//! The [`SolvingContext`] structure used to take actions during propagation
//! and solution checking.
//!
//! This structure contains the implementation of the action traits that are
//! exposed to propagators.

use std::fmt::{self, Debug, Formatter};

use pindakaas::{Lit as RawLit, solver::propagation::SolvingActions};
use tracing::trace;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, BoolPropagationActions, DecisionActions, IntDecisionActions,
		IntEvent, IntInspectionActions, IntPropCond, IntPropagationActions, PropagationActions,
		ReasoningContext, ReasoningEngine, Trailed, TrailingActions,
	},
	constraints::{Conflict, DeferredReason, Reason, ReasonBuilder},
	helpers::bytes::Bytes,
	solver::{
		BoxedPropagator, IntLitMeaning, Polarity,
		activation_list::ActivationAction,
		decision::{Decision, integer::LazyLitDef},
		engine::{AdvRef, AdvisorDef, Engine, LitPropagation, PropRef, State, trace_new_lit},
		view::{View, boolean::BoolView, integer::IntView},
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
	/// Actions to create new variables in the solver.
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object.
	pub(crate) state: &'a mut State,
	/// Current propagator being executed.
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
	fn diff_lit(&self, ctx: &mut SolvingContext<'_>, other: Self, d: IntVal) -> View<bool> {
		let x: View<IntVal> = (*self).into();
		let y: View<IntVal> = other.into();
		ctx.diff_logic_lazy_diff_lit(x, y, d)
	}

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

	fn tighten_difference(
		&self,
		ctx: &mut SolvingContext<'a>,
		other: Self,
		d: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>>,
	) -> Result<(), Conflict<Decision<bool>>> {
		let b = self.diff_lit(ctx, other, d);
		b.fix(ctx, true, reason)
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
	/// Mid-search lazy `diff_lit` against the engine-side diff-logic
	/// propagator.
	///
	/// 1. Cache hit (forward or reverse direction) → return.
	/// 2. Probe forward chain neighbours for SAT-subsumption clauses.
	/// 3. Mint a fresh SAT variable for the gate Boolean.
	/// 4. Queue the new edge for the owning [`DiffLogicPropagator`] to install
	///    at the end of this propagation cycle (it owns the graph + trail; we
	///    can't reach into it while another propagator is borrowed for
	///    `propagate`).
	/// 5. Populate the cache in both directions.
	/// 6. Post chain implication clauses to `state.clauses`.
	pub(crate) fn diff_logic_lazy_diff_lit(
		&mut self,
		x: View<IntVal>,
		y: View<IntVal>,
		d: IntVal,
	) -> View<bool> {
		// 1. Cache hits.
		if let Some(b) = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.get(&(x, y))
			.and_then(|m| m.get(&d))
		{
			return *b;
		}
		if let Some(b) = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.get(&(y, x))
			.and_then(|m| m.get(&(-d - 1)))
		{
			return !*b;
		}

		// 2. Probe forward chain neighbours BEFORE allocating.
		let prev_b = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.get(&(x, y))
			.and_then(|m| m.range(..d).next_back().map(|(_, &b)| b));
		let next_b = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.get(&(x, y))
			.and_then(|m| m.range((d + 1)..).next().map(|(_, &b)| b));

		// 3. Allocate a fresh SAT variable for the new gate.
		let raw_var = self.slv.new_observed_var();
		self.state.statistics.lazy_literals += 1;
		self.state.trail.grow_to_boolvar(raw_var);
		let new_lit: pindakaas::Lit = raw_var.into();
		let b: View<bool> = View(BoolView::Lit(Decision(new_lit)));

		// 4. Queue both gated edges for the owning propagator's `register_edge` drain.
		//    The drain happens after the current propagator returns from `propagate`
		//    (see `Self::drain_pending_register_edges`), so we are not re-entrantly
		//    mutating the diff-logic propagator while the caller is propagating.
		self.state
			.diff_lit_map
			.pending_register_edges
			.push((x, y, d, b));
		self.state
			.diff_lit_map
			.pending_register_edges
			.push((y, x, -d - 1, !b));

		// 5. Populate cache in BOTH directions.
		let _ = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.entry((x, y))
			.or_default()
			.insert(d, b);
		let _ = self
			.state
			.diff_lit_map
			.diff_lit_cache
			.entry((y, x))
			.or_default()
			.insert(-d - 1, !b);

		// 6. Push order-encoding chain implication clauses.
		let as_raw = |v: View<bool>| -> pindakaas::Lit {
			match v.0 {
				BoolView::Lit(d) => d.0,
				BoolView::Const(_) => unreachable!(
					"chain neighbour can not be a constant: the cache only stores Lit views"
				),
			}
		};
		if let Some(bp) = prev_b {
			self.state.clauses.push_back(vec![!as_raw(bp), as_raw(b)]);
		}
		if let Some(bn) = next_b {
			self.state.clauses.push_back(vec![!as_raw(b), as_raw(bn)]);
		}

		b
	}

	/// Take the lazily-queued diff-logic edges out of `state.diff_lit_map`
	/// and install them on the owner propagator. Run once after each
	/// propagator returns from `propagate`; safe to call when the queue
	/// is non-empty because the running propagator has already released
	/// its borrow on the propagator slot.
	///
	/// After installing, subscribe `Bounds` advisors on newly-interned
	/// int endpoints and `Fixed` advisors on newly-interned gate
	/// Booleans so the lazy edges participate in the regular
	/// notification flow.
	fn drain_pending_register_edges(&mut self, propagators: &mut [BoxedPropagator]) {
		use crate::constraints::diff_logic::DiffLogicPropagator;

		let pending = std::mem::take(&mut self.state.diff_lit_map.pending_register_edges);
		// `owner` is `Some` whenever lazy edges have been queued — the
		// queue itself is only populated through
		// `diff_logic_lazy_diff_lit`, which sets `owner` lazily during
		// the first mint.
		let owner = self
			.state
			.diff_lit_map
			.owner
			.expect("diff-logic owner not set but pending edges queued");

		// Track newly-interned int endpoints + gates so we can
		// subscribe advisors on them after the prop borrow is dropped.
		let new_int_nodes: Vec<(View<IntVal>, u64)>;
		let new_bool_nodes: Vec<(View<bool>, u64)>;
		{
			let any: &mut dyn std::any::Any = propagators[owner.index()].as_mut();
			let prop = any
				.downcast_mut::<DiffLogicPropagator>()
				.expect("owner propagator must be a DiffLogicPropagator");
			let int_before = prop.int_vars.len();
			let bool_before = prop.bool_vars.len();
			for (x, y, d, gate) in pending {
				let _ = prop.register_edge(&mut self.state.trail, x, y, d, Some(gate));
			}
			new_int_nodes = (int_before..prop.int_vars.len())
				.map(|n| (prop.int_vars[n], n as u64))
				.collect();
			new_bool_nodes = (bool_before..prop.bool_vars.len())
				.map(|n| (prop.bool_vars[n], n as u64))
				.collect();
		}

		// Subscribe bounds advisors on freshly-interned endpoints and
		// fixed advisors on freshly-interned gate Booleans. Owner is
		// the propagator slot we want all of these routed to.
		for (view, data) in new_int_nodes {
			self.subscribe_lazy_int_bounds(owner, view, data);
		}
		for (view, data) in new_bool_nodes {
			self.subscribe_lazy_bool_fixed(owner, view, data);
		}

		// Re-enqueue the owner so its next `propagate` picks up the
		// new edges (its `advise_*` advisors were not invoked because
		// the edges arrive via the lazy path).
		self.state.propagator_queue.enqueue_propagator(owner.raw());
	}

	/// Create a new SolvingContext given the solver actions exposed by the SAT
	/// solver and the engine state.
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropRef::INVALID,
		}
	}

	/// Internal method used to propagate an integer variable given a literal
	/// description to be enforced.
	#[inline]
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
		reason: impl ReasonBuilder<Self>,
		event: Option<(Decision<IntVal>, IntEvent)>,
	) {
		let reason = Reason::from_view(reason.build_reason(self));
		trace!(
			target: "solver",
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
		self.current_prop = PropRef::from_raw(p);
		let res = propagators[self.current_prop.index()]
			.as_mut()
			.propagate(self);
		self.state.statistics.propagations += 1;
		self.current_prop = PropRef::INVALID;
		res
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
					target: "solver",
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

			// Drain mid-search lazy edges that this propagator may have
			// minted via `diff_logic_lazy_diff_lit`. Each entry installs
			// one gated edge on the diff-logic propagator; subscribing
			// advisors on freshly-interned endpoints / gate Booleans is
			// handled at mint time. We do the drain here (outside the
			// inner propagate borrow) to avoid aliasing the propagator
			// twice. Wakes the diff-logic propagator so it processes the
			// new edge on its next turn through the queue.
			if !self.state.diff_lit_map.pending_register_edges.is_empty() {
				self.drain_pending_register_edges(propagators);
			}

			if self.state.conflict.is_some() || !self.state.propagation_queue.is_empty() {
				return;
			}
		}
	}

	/// Mid-search subscription helper for a gating Boolean view
	/// (gate of a freshly-minted lazy edge).
	fn subscribe_lazy_bool_fixed(&mut self, owner: PropRef, view: View<bool>, data: u64) {
		let lit = match view.0 {
			BoolView::Lit(l) => l,
			BoolView::Const(_) => return,
		};
		if lit.val(&self.state.trail).is_some() {
			return;
		}
		let var = lit.0.var();
		self.state.advisors.push(AdvisorDef {
			bool2int: false,
			data,
			negated: false,
			propagator: owner,
		});
		let adv = AdvRef::new(self.state.advisors.len() - 1);
		self.state
			.bool_activation
			.entry(var)
			.or_default()
			.push(ActivationAction::<_, PropRef>::Advise(adv).into());
	}

	/// Mid-search subscription helper used by
	/// [`Self::drain_pending_register_edges`] when a lazy edge's
	/// endpoint hadn't been seen before. The owner propagator handles
	/// `Bounds` advice on the given int view; const views are a no-op.
	fn subscribe_lazy_int_bounds(&mut self, owner: PropRef, view: View<IntVal>, data: u64) {
		match view.0 {
			IntView::Linear(lin) => {
				let negated = lin.scale.is_negative();
				self.state.advisors.push(AdvisorDef {
					bool2int: false,
					data,
					negated,
					propagator: owner,
				});
				let adv = AdvRef::new(self.state.advisors.len() - 1);
				self.state.int_activation[lin.var.idx()].add(
					ActivationAction::<_, PropRef>::Advise(adv),
					IntPropCond::Bounds,
				);
			}
			IntView::Const(_) => {}
			IntView::Bool(lin) => {
				if lin.var.val(&self.state.trail).is_some() {
					return;
				}
				self.state.advisors.push(AdvisorDef {
					bool2int: true,
					data,
					negated: lin.scale.is_negative(),
					propagator: owner,
				});
				let adv = AdvRef::new(self.state.advisors.len() - 1);
				self.state
					.bool_activation
					.entry(lin.var.0.var())
					.or_default()
					.push(ActivationAction::<_, PropRef>::Advise(adv).into());
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
