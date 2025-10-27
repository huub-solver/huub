//! Module containing the [`SolvingContext`] structure used to take actions
//! during the propagation and solution checking process. This structure
//! contains the implementation of the actions that are exposed to the
//! propagators.

use std::fmt::{self, Debug, Formatter};

use index_vec::IndexVec;
use pindakaas::{solver::propagation::SolvingActions, Lit as RawLit};
use tracing::trace;

use crate::{
	actions::{
		BoolInspectionActions, BoolPropagationActions, DecisionActions, IntDecisionActions,
		IntExplanationActions, IntInspectionActions, IntPropagationActions, PropagationActions,
		TrailingActions,
	},
	constraints::{Conflict, LazyReason, Reason, ReasonBuilder},
	solver::{
		activation_list::IntEvent,
		engine::{trace_new_lit, LitPropagation, PropRef, State},
		int_var::{IntVarRef, LazyLitDef},
		trail::TrailedInt,
		BoolView, BoolViewInner, BoxedPropagator, IntView, IntViewInner,
	},
	IntLitMeaning, IntVal,
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
struct ReasonTracePrint<'a>(&'a Result<Reason, bool>);

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
	/// Internal method used to propagate a boolean variable used as a integer
	/// given a literal description to be enforced.
	fn propagate_bool_lin(
		&mut self,
		lit: RawLit,
		lit_req: IntLitMeaning,
		reason: impl ReasonBuilder<Self, BoolView>,
	) -> Result<(), Conflict> {
		let bv = BoolView(BoolViewInner::Lit(lit));
		let todo_reason: Vec<BoolView> = vec![];
		match lit_req {
			IntLitMeaning::Eq(0) | IntLitMeaning::Less(1) | IntLitMeaning::NotEq(1) => {
				bv.set_val(self, false, todo_reason)
			}
			IntLitMeaning::Eq(1) | IntLitMeaning::GreaterEq(1) | IntLitMeaning::NotEq(0) => {
				bv.set(self, todo_reason)
			}
			IntLitMeaning::Eq(_) => Err(Conflict::new(self, None, reason)),
			IntLitMeaning::GreaterEq(i) if i > 1 => Err(Conflict::new(self, None, reason)),
			IntLitMeaning::Less(i) if i <= 0 => Err(Conflict::new(self, None, reason)),
			IntLitMeaning::NotEq(_) | IntLitMeaning::GreaterEq(_) | IntLitMeaning::Less(_) => {
				Ok(())
			}
		}
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
		let reason = Reason::from_iter(reason.build_reason(self));
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

	#[inline]
	/// Internal method used to propagate an integer variable given a literal
	/// description to be enforced.
	fn propagate_int(
		&mut self,
		iv: IntVarRef,
		lit_req: IntLitMeaning,
		reason: impl ReasonBuilder<Self, BoolView>,
	) -> Result<(), Conflict> {
		let (lb, ub) = self.state.int_vars[iv].get_bounds(self);
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
		let (bv, lit_req) = self.state.int_vars[iv].bool_lit(lit_req, new_var);

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
		match self.state.trail.get_sat_value(lit) {
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
	fn get_num_conflicts(&self) -> u64 {
		self.state.statistics.conflicts
	}
}

impl PropagationActions for SolvingContext<'_> {
	fn deferred_reason(&self, data: u64) -> LazyReason {
		LazyReason(self.current_prop, data)
	}
}

impl TrailingActions for SolvingContext<'_> {
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		self.state.get_bool_val(bv)
	}

	fn get_trailed_int(&self, x: TrailedInt) -> IntVal {
		self.state.get_trailed_int(x)
	}

	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal {
		self.state.set_trailed_int(x, v)
	}
}

impl<B> BoolInspectionActions<SolvingContext<'_>> for B
where
	B: BoolInspectionActions<State>,
{
	fn get_val(&self, ctx: &SolvingContext<'_>) -> Option<bool> {
		self.get_val(ctx.state)
	}
}

impl<'a> BoolPropagationActions<SolvingContext<'a>> for BoolView {
	type Atom = BoolView;
	type Conflict = Conflict;

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: bool,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict> {
		if val { *self } else { !(*self) }.set(ctx, reason)
	}

	fn set(
		&self,
		ctx: &mut SolvingContext<'a>,
		reason: impl ReasonBuilder<SolvingContext<'a>, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect();
		match self.0 {
			BoolViewInner::Lit(lit) => match ctx.state.trail.get_sat_value(lit) {
				Some(true) => Ok(()),
				Some(false) => Err(Conflict::new(ctx, lit.into(), reason)),
				None => {
					ctx.propagate_lit(lit, reason, None);
					Ok(())
				}
			},
			BoolViewInner::Const(false) => Err(Conflict::new(ctx, None, reason)),
			BoolViewInner::Const(true) => Ok(()),
		}
	}
}

impl IntDecisionActions<SolvingContext<'_>> for IntVarRef {
	fn get_lit(&self, ctx: &mut SolvingContext<'_>, meaning: IntLitMeaning) -> BoolView {
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
		var.bool_lit(meaning, new_var).0
	}
}

impl IntDecisionActions<SolvingContext<'_>> for IntView {
	fn get_lit(&self, ctx: &mut SolvingContext<'_>, mut meaning: IntLitMeaning) -> BoolView {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			self.0
		{
			match transformer.rev_transform_lit(meaning) {
				Ok(m) => meaning = m,
				Err(v) => return BoolView(BoolViewInner::Const(v)),
			}
		}

		match self.0 {
			IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
				var.get_lit(ctx, meaning)
			}
			IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match meaning {
				IntLitMeaning::Eq(i) => c == i,
				IntLitMeaning::NotEq(i) => c != i,
				IntLitMeaning::GreaterEq(i) => c >= i,
				IntLitMeaning::Less(i) => c < i,
			})),
			IntViewInner::Bool { lit, .. } => {
				let (meaning, negated) =
					if matches!(meaning, IntLitMeaning::NotEq(_) | IntLitMeaning::Less(_)) {
						(!meaning, true)
					} else {
						(meaning, false)
					};
				let bv = BoolView(match meaning {
					IntLitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
					IntLitMeaning::Eq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::Eq(_) => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
					IntLitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
					IntLitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
					_ => unreachable!(),
				});
				if negated {
					!bv
				} else {
					bv
				}
			}
		}
	}
}

impl<I> IntInspectionActions<SolvingContext<'_>> for I
where
	I: IntInspectionActions<State>,
{
	type Atom = <I as IntInspectionActions<State>>::Atom;

	fn get_lower_bound(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.get_lower_bound(ctx.state)
	}

	fn get_upper_bound(&self, ctx: &SolvingContext<'_>) -> IntVal {
		self.get_upper_bound(ctx.state)
	}

	fn check_int_in_domain(&self, ctx: &SolvingContext<'_>, val: IntVal) -> bool {
		self.check_int_in_domain(ctx.state, val)
	}

	fn get_lit_meaning(&self, ctx: &SolvingContext<'_>, lit: Self::Atom) -> Option<IntLitMeaning> {
		self.get_lit_meaning(ctx.state, lit)
	}

	fn get_lower_bound_lit(&self, ctx: &SolvingContext<'_>) -> Self::Atom {
		self.get_lower_bound_lit(ctx.state)
	}

	fn get_upper_bound_lit(&self, ctx: &SolvingContext<'_>) -> Self::Atom {
		self.get_upper_bound_lit(ctx.state)
	}

	fn try_lit(&self, ctx: &SolvingContext<'_>, meaning: IntLitMeaning) -> Option<Self::Atom> {
		self.try_lit(ctx.state, meaning)
	}
}

impl<'a> IntPropagationActions<SolvingContext<'a>> for IntVarRef {
	type Conflict = Conflict;

	fn set_lower_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
		ctx.propagate_int(*self, IntLitMeaning::GreaterEq(val), reason)
	}

	fn set_upper_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
		ctx.propagate_int(*self, IntLitMeaning::Less(val + 1), reason)
	}

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
		ctx.propagate_int(*self, IntLitMeaning::Eq(val), reason)
	}

	fn set_not_eq(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
		ctx.propagate_int(*self, IntLitMeaning::NotEq(val), reason)
	}
}

impl<'a> IntPropagationActions<SolvingContext<'a>> for IntView {
	type Conflict = Conflict;

	fn set_lower_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict> {
		match self.0 {
			IntViewInner::VarRef(var) => var.set_lower_bound(ctx, val, reason),
			IntViewInner::Linear { var, transformer } => match transformer
				.rev_transform_lit(IntLitMeaning::GreaterEq(val))
				.unwrap()
			{
				IntLitMeaning::Less(v) => var.set_upper_bound(ctx, v - 1, reason),
				IntLitMeaning::GreaterEq(v) => var.set_lower_bound(ctx, v, reason),
				_ => unreachable!(),
			},
			IntViewInner::Bool { lit, transformer } => {
				let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
				ctx.propagate_bool_lin(
					lit,
					transformer
						.rev_transform_lit(IntLitMeaning::GreaterEq(val))
						.unwrap(),
					reason,
				)
			}
			IntViewInner::Const(i) => {
				if i < val {
					let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
					Err(Conflict::new(ctx, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}

	fn set_upper_bound(
		&self,
		ctx: &mut SolvingContext<'a>,
		val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict> {
		match self.0 {
			IntViewInner::VarRef(var) => var.set_upper_bound(ctx, val, reason),
			IntViewInner::Linear { var, transformer } => {
				match transformer
					.rev_transform_lit(IntLitMeaning::Less(val + 1))
					.unwrap()
				{
					IntLitMeaning::Less(v) => var.set_upper_bound(ctx, v - 1, reason),
					IntLitMeaning::GreaterEq(v) => var.set_lower_bound(ctx, v, reason),
					_ => unreachable!(),
				}
			}
			IntViewInner::Bool { lit, transformer } => {
				let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
				ctx.propagate_bool_lin(
					lit,
					transformer
						.rev_transform_lit(IntLitMeaning::Less(val + 1))
						.unwrap(),
					reason,
				)
			}
			IntViewInner::Const(i) => {
				if i > val {
					let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
					Err(Conflict::new(ctx, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}

	fn set_val(
		&self,
		ctx: &mut SolvingContext<'a>,
		mut val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict> {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			self.0
		{
			match transformer.rev_transform_lit(IntLitMeaning::Eq(val)) {
				Ok(IntLitMeaning::Eq(v)) => val = v,
				Err(v) => {
					debug_assert!(!v);
					let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
					return Err(Conflict::new(ctx, None, reason));
				}
				_ => unreachable!(),
			}
		}

		match self.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				iv.set_val(ctx, val, reason)
			}
			IntViewInner::Bool { lit, .. } => {
				let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
				ctx.propagate_bool_lin(lit, IntLitMeaning::Eq(val), reason)
			}
			IntViewInner::Const(i) => {
				if i != val {
					let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
					Err(Conflict::new(ctx, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}

	fn set_not_eq(
		&self,
		ctx: &mut SolvingContext<'a>,
		mut val: IntVal,
		reason: impl ReasonBuilder<SolvingContext<'a>, BoolView>,
	) -> Result<(), Conflict> {
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			self.0
		{
			match transformer.rev_transform_lit(IntLitMeaning::NotEq(val)) {
				Ok(IntLitMeaning::NotEq(v)) => val = v,
				Err(v) => {
					debug_assert!(v);
					return Ok(());
				}
				_ => unreachable!(),
			}
		}

		match self.0 {
			IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
				var.set_not_eq(ctx, val, reason)
			}
			IntViewInner::Bool { lit, .. } => {
				let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
				ctx.propagate_bool_lin(lit, IntLitMeaning::NotEq(val), reason)
			}
			IntViewInner::Const(i) => {
				if i == val {
					let reason: Vec<BoolView> = reason.build_reason(ctx).into_iter().collect(); // TODO
					Err(Conflict::new(ctx, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
}
