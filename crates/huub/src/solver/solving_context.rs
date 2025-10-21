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
		DecisionActions, ExplanationActions, InspectionActions, PropagationActions, TrailingActions,
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
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let bv = BoolView(BoolViewInner::Lit(lit));
		match lit_req {
			IntLitMeaning::Eq(0) | IntLitMeaning::Less(1) | IntLitMeaning::NotEq(1) => {
				self.set_bool(!bv, reason)
			}
			IntLitMeaning::Eq(1) | IntLitMeaning::GreaterEq(1) | IntLitMeaning::NotEq(0) => {
				self.set_bool(bv, reason)
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
		reason: impl ReasonBuilder<Self>,
		event: Option<(IntVarRef, IntEvent)>,
	) {
		let reason = reason.build_reason(self);
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
		reason: impl ReasonBuilder<Self>,
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
			return Err(Conflict::new(self, Some(lit), reason));
		}
		// 3. Literal is assigned false (and immediate return if assigned true).
		match self.state.trail.get_sat_value(lit) {
			Some(true) => return Ok(()),
			Some(false) => return Err(Conflict::new(self, Some(lit), reason)),
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
			IntLitMeaning::NotEq(val) if val == lb => {
				let val = self.state.int_vars[iv].tighten_greater_eq_lit(val + 1);
				self.state.int_vars[iv].notify_lower_bound(&mut self.state.trail, val);
			}
			IntLitMeaning::NotEq(val) if val == ub => {
				let val = self.state.int_vars[iv].tighten_less_lit(val);
				self.state.int_vars[iv].notify_upper_bound(&mut self.state.trail, val - 1);
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
	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: IntLitMeaning) -> BoolView {
		let var = &mut self.state.int_vars[iv];
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
		var.bool_lit(meaning, new_var).0
	}

	fn get_num_conflicts(&self) -> u64 {
		self.state.statistics.conflicts
	}
}

impl ExplanationActions for SolvingContext<'_> {
	fn get_int_lit_meaning(&self, var: IntView, lit: RawLit) -> Option<IntLitMeaning> {
		self.state.get_int_lit_meaning(var, lit)
	}

	fn get_int_lit_relaxed(
		&mut self,
		var: IntView,
		meaning: IntLitMeaning,
	) -> (BoolView, IntLitMeaning) {
		self.state.get_int_lit_relaxed(var, meaning)
	}

	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView {
		self.state.get_int_lower_bound_lit(var)
	}

	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView {
		self.state.get_int_upper_bound_lit(var)
	}
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		let val = self.get_int_val(var)?;
		Some(self.get_int_lit(var, IntLitMeaning::Eq(val)))
	}

	fn try_int_lit(&self, var: IntView, meaning: IntLitMeaning) -> Option<BoolView> {
		self.state.try_int_lit(var, meaning)
	}
}

impl InspectionActions for SolvingContext<'_> {
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		self.state.check_int_in_domain(var, val)
	}

	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		self.state.get_int_bounds(var)
	}
	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		self.state.get_int_lower_bound(var)
	}

	fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		self.state.get_int_upper_bound(var)
	}

	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		self.state.get_int_val(var)
	}
}

impl PropagationActions for SolvingContext<'_> {
	fn deferred_reason(&self, data: u64) -> LazyReason {
		LazyReason(self.current_prop, data)
	}
	fn set_bool(&mut self, bv: BoolView, reason: impl ReasonBuilder<Self>) -> Result<(), Conflict> {
		match bv.0 {
			BoolViewInner::Lit(lit) => match self.state.trail.get_sat_value(lit) {
				Some(true) => Ok(()),
				Some(false) => Err(Conflict::new(self, Some(lit), reason)),
				None => {
					self.propagate_lit(lit, reason, None);
					Ok(())
				}
			},
			BoolViewInner::Const(false) => Err(Conflict::new(self, None, reason)),
			BoolViewInner::Const(true) => Ok(()),
		}
	}

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = IntLitMeaning::GreaterEq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i < val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = IntLitMeaning::NotEq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			match transformer.rev_transform_lit(lit_req) {
				Ok(lit) => lit_req = lit,
				Err(v) => {
					debug_assert!(v);
					return Ok(());
				}
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i == val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = IntLitMeaning::Less(val + 1);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i > val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = IntLitMeaning::Eq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			match transformer.rev_transform_lit(lit_req) {
				Ok(lit) => lit_req = lit,
				Err(v) => {
					debug_assert!(!v);
					return Err(Conflict::new(self, None, reason));
				}
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i != val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
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
