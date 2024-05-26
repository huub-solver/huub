use delegate::delegate;
use pindakaas::Lit as RawLit;
use tracing::trace;

use crate::{
	actions::{
		explanation::ExplanationActions, inspection::InspectionActions,
		propagation::PropagationActions, trailing::TrailingActions,
	},
	propagator::{conflict::Conflict, reason::ReasonBuilder},
	solver::{
		engine::{int_var::IntVarRef, trail::TrailedInt, PropRef, State},
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, Conjunction, IntVal, IntView, LitMeaning,
};

pub(crate) struct PropagationContext<'a> {
	pub(crate) prop: PropRef,
	pub(crate) prop_queue: Conjunction,
	pub(crate) state: &'a mut State,
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
					self.prop,
				)),
				None => {
					let propagated_lit = if val { lit } else { !lit };
					trace!(lit = i32::from(propagated_lit), "propagate bool");
					let change = self.state.trail.assign_sat(propagated_lit);
					debug_assert_eq!(change, None);
					self.state
						.register_reason(propagated_lit, reason, self.prop);
					self.prop_queue.push(propagated_lit);
					Ok(())
				}
			},
			BoolViewInner::Const(b) => {
				if b != val {
					Err(Conflict::new(None, reason, self.prop))
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
					Err(Conflict::new(None, reason, self.prop))
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
					Err(Conflict::new(None, reason, self.prop))
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
				return Err(Conflict::new(None, reason, self.prop));
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i != val {
					Err(Conflict::new(None, reason, self.prop))
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
					Err(Conflict::new(None, reason, self.prop))
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
impl ExplanationActions for PropagationContext<'_> {
	delegate! {
		to self.state {
			fn get_int_lit(&self, var: IntView, meaning: LitMeaning) -> BoolView;
			fn get_int_val_lit(&self, var: IntView) -> Option<BoolView>;
			fn get_int_lower_bound_lit(&self, var: IntView) -> BoolView;
			fn get_int_upper_bound_lit(&self, var: IntView) -> BoolView;
		}
	}
}

impl PropagationContext<'_> {
	#[inline]
	pub(crate) fn check_satisfied(&self, var: IntVarRef, lit: &LitMeaning) -> bool {
		match lit {
			LitMeaning::Eq(i) => {
				let lb = self.get_trailed_int(self.state.int_vars[var].lower_bound);
				let ub = self.get_trailed_int(self.state.int_vars[var].upper_bound);
				lb == *i && ub == *i
			}
			LitMeaning::NotEq(i) => {
				let lb = self.get_trailed_int(self.state.int_vars[var].lower_bound);
				let ub = self.get_trailed_int(self.state.int_vars[var].upper_bound);
				if *i < lb || *i > ub {
					true
				} else {
					let eq_lit = self.state.int_vars[var].get_bool_lit(LitMeaning::NotEq(*i));
					self.get_bool_val(eq_lit).unwrap_or(false)
				}
			}
			LitMeaning::GreaterEq(i) => {
				let lb = self.get_trailed_int(self.state.int_vars[var].lower_bound);
				lb >= *i
			}
			LitMeaning::Less(i) => {
				let ub = self.get_trailed_int(self.state.int_vars[var].upper_bound);
				ub < *i
			}
		}
	}

	#[inline]
	pub(crate) fn propagate_int(
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
		let bv = self.state.int_vars[iv].get_bool_lit(lit_req);
		self.set_bool_val(bv, true, reason)
	}

	pub(crate) fn propagate_bool_lin(
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
			LitMeaning::Eq(_) => Err(Conflict::new(None, reason, self.prop)),
			LitMeaning::GreaterEq(i) if i > 1 => Err(Conflict::new(None, reason, self.prop)),
			LitMeaning::Less(i) if i < 0 => Err(Conflict::new(None, reason, self.prop)),
			LitMeaning::NotEq(_) | LitMeaning::GreaterEq(_) | LitMeaning::Less(_) => Ok(()),
		}
	}
}
