use delegate::delegate;
use index_vec::IndexVec;
use pindakaas::{solver::SolvingActions, Lit as RawLit};
use tracing::trace;

use crate::{
	actions::{
		explanation::ExplanationActions, inspection::InspectionActions,
		propagation::PropagationActions, trailing::TrailingActions,
	},
	propagator::{conflict::Conflict, reason::ReasonBuilder},
	solver::{
		engine::{
			int_var::{IntVarRef, LazyLitDef},
			trace_new_lit,
			trail::TrailedInt,
			PropRef, State,
		},
		poster::BoxedPropagator,
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, Clause, IntVal, IntView, LitMeaning,
};

pub(crate) struct PropagationContext<'a> {
	/// Actions to create new variables in the oracle
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object
	pub(crate) state: &'a mut State,
	/// Current propagator being executed
	pub(crate) current_prop: PropRef,
}

impl<'a> PropagationContext<'a> {
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropRef::new(u32::MAX as usize),
		}
	}

	pub(crate) fn run_propagators(&mut self, propagators: &mut IndexVec<PropRef, BoxedPropagator>) {
		while let Some(p) = self.state.prop_queue.pop() {
			self.state.enqueued[p] = false;
			self.current_prop = p;
			let prop = propagators[p].as_mut();
			let res = prop.propagate(self);
			self.state.statistics.propagations += 1;
			self.current_prop = PropRef::new(u32::MAX as usize);
			if let Err(Conflict { subject, reason }) = res {
				self.state.conflict = true;
				let mut clause: Clause = reason.to_clause(propagators, self.state);
				if let Some(subject) = subject {
					clause.push(subject);
				}
				trace!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "conflict detected");
				debug_assert!(!clause.is_empty());
				self.state.changes.add_clause(clause);
			}
			if !self.state.changes.is_empty() {
				return;
			}
			debug_assert!(!self.state.conflict);
		}
	}

	#[inline]
	fn check_satisfied(&self, var: IntVarRef, lit: &LitMeaning) -> bool {
		let (lb, ub) = self.state.int_vars[var].get_bounds(self);
		match lit {
			LitMeaning::Eq(i) => lb == *i && ub == *i,
			LitMeaning::NotEq(i) => {
				if *i < lb || *i > ub {
					true
				} else {
					let eq_lit = self.state.int_vars[var].get_bool_lit(LitMeaning::NotEq(*i));
					if let Some(eq_lit) = eq_lit {
						self.get_bool_val(eq_lit).unwrap_or(false)
					} else {
						false
					}
				}
			}
			LitMeaning::GreaterEq(i) => lb >= *i,
			LitMeaning::Less(i) => ub < *i,
		}
	}

	#[inline]
	fn propagate_int(
		&mut self,
		iv: IntVarRef,
		lit_req: LitMeaning,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		if self.check_satisfied(iv, &lit_req) {
			return Ok(());
		}
		trace!(int_var = usize::from(iv), effect = ?lit_req, "propagate int");
		// TODO: Update domain??
		let bv = self.get_intref_lit(iv, lit_req);
		self.set_bool_val(bv, true, reason)
	}

	#[inline]
	fn propagate_bool_lin(
		&mut self,
		lit: RawLit,
		lit_req: LitMeaning,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match lit_req {
			LitMeaning::Eq(0) | LitMeaning::Less(1) | LitMeaning::NotEq(1) => {
				self.set_bool_val(BoolView(BoolViewInner::Lit(lit)), false, reason)
			}
			LitMeaning::Eq(1) | LitMeaning::GreaterEq(1) | LitMeaning::NotEq(0) => {
				self.set_bool_val(BoolView(BoolViewInner::Lit(lit)), true, reason)
			}
			LitMeaning::Eq(_) => Err(Conflict::new(None, reason, self.current_prop)),
			LitMeaning::GreaterEq(i) if i > 1 => {
				Err(Conflict::new(None, reason, self.current_prop))
			}
			LitMeaning::Less(i) if i < 0 => Err(Conflict::new(None, reason, self.current_prop)),
			LitMeaning::NotEq(_) | LitMeaning::GreaterEq(_) | LitMeaning::Less(_) => Ok(()),
		}
	}
}

impl ExplanationActions for PropagationContext<'_> {
	delegate! {
		to self.state {
			fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
			fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
			fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
		}
	}

	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: LitMeaning) -> BoolView {
		let var = &mut self.state.int_vars[iv];
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = self.slv.new_var();
			trace_new_lit!(iv, def, v);
			self.slv.add_observed_var(v);
			self.state
				.bool_to_int
				.insert_lazy(v, iv, def.meaning.clone());
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				self.state.changes.add_clause(cl);
			}
			v
		};
		var.bool_lit(meaning, new_var)
	}
}

impl InspectionActions for PropagationContext<'_> {
	delegate! {
		to self.state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl<'a> PropagationActions for PropagationContext<'a> {
	fn set_bool_val(
		&mut self,
		bv: BoolView,
		val: bool,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match bv.0 {
			BoolViewInner::Lit(lit) => match self.state.trail.get_sat_value(lit) {
				Some(b) if b == val => Ok(()),
				Some(_) => Err(Conflict::new(
					Some(if val { lit } else { !lit }),
					reason,
					self.current_prop,
				)),
				None => {
					let propagated_lit = if val { lit } else { !lit };
					trace!(lit = i32::from(propagated_lit), reason = ?reason, "propagate bool");
					self.state
						.register_reason(propagated_lit, reason, self.current_prop);
					self.state.changes.propagate(propagated_lit);
					let prev = self.state.trail.assign_sat(propagated_lit);
					debug_assert!(prev.is_none());
					Ok(())
				}
			},
			BoolViewInner::Const(b) => {
				if b != val {
					Err(Conflict::new(None, reason, self.current_prop))
				} else {
					Ok(())
				}
			}
		}
	}

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::GreaterEq(val);
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
					Err(Conflict::new(None, reason, self.current_prop))
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
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::Less(val + 1);
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
					Err(Conflict::new(None, reason, self.current_prop))
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
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::Eq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			if let Some(lit) = transformer.rev_transform_lit(lit_req) {
				lit_req = lit;
			} else {
				return Err(Conflict::new(None, reason, self.current_prop));
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i != val {
					Err(Conflict::new(None, reason, self.current_prop))
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
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::NotEq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			if let Some(lit) = transformer.rev_transform_lit(lit_req) {
				lit_req = lit;
			} else {
				return Ok(());
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i == val {
					Err(Conflict::new(None, reason, self.current_prop))
				} else {
					Ok(())
				}
			}
		}
	}
}

impl TrailingActions for PropagationContext<'_> {
	delegate! {
		to self.state {
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}
