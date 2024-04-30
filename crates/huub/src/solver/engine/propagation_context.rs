use super::{PropRef, State};
use crate::{
	propagator::{conflict::Conflict, reason::ReasonBuilder, PropagationActions},
	solver::{
		engine::trail::HasChanged,
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
	fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		match bv.0 {
			BoolViewInner::Lit(lit) => self.state.sat_trail.get(lit),
			BoolViewInner::Const(b) => Some(b),
		}
	}

	fn set_bool_val(
		&mut self,
		bv: BoolView,
		val: bool,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match bv.0 {
			BoolViewInner::Lit(lit) => match self.state.sat_trail.get(lit) {
				Some(b) if b == val => Ok(()),
				Some(_) => Err(Conflict::new(reason, self.prop)),
				None => {
					let change = self
						.state
						.sat_trail
						.assign(lit.var(), if lit.is_negated() { !val } else { val });
					debug_assert_eq!(change, HasChanged::Changed);
					self.prop_queue.push(if val { lit } else { !lit });
					Ok(())
				}
			},
			BoolViewInner::Const(b) => {
				if b != val {
					Err(Conflict::new(reason, self.prop))
				} else {
					Ok(())
				}
			}
		}
	}

	fn get_int_lit(&mut self, var: IntView, bv: LitMeaning) -> BoolView {
		match var.0 {
			IntViewInner::VarRef(iv) => self.state.int_vars[iv].get_bool_lit(bv),
			IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match bv {
				LitMeaning::Eq(i) => c == i,
				LitMeaning::NotEq(i) => c != i,
				LitMeaning::GreaterEq(i) => c >= i,
				LitMeaning::Less(i) => c < i,
			})),
		}
	}
	fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.state.int_trail[self.state.int_vars[iv].lower_bound],
			IntViewInner::Const(i) => i,
		}
	}
	fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.state.int_trail[self.state.int_vars[iv].upper_bound],
			IntViewInner::Const(i) => i,
		}
	}
	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		let lb = self.get_int_lower_bound(var);
		let ub = self.get_int_upper_bound(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				match self.state.int_vars[iv].get_bool_lit(LitMeaning::Eq(val)).0 {
					BoolViewInner::Lit(lit) => self.state.sat_trail.get(lit).unwrap_or(true),
					BoolViewInner::Const(b) => b,
				}
			}
			IntViewInner::Const(i) => i == val,
		}
	}

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_lower_bound(var) >= val {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.state.int_vars[iv].get_bool_lit(LitMeaning::GreaterEq(val))
				else {
					unreachable!()
				};
				self.state.register_reason(lit, reason, self.prop);
				self.prop_queue.push(lit);
			}
			IntViewInner::Const(i) => {
				if i < val {
					todo!()
				}
			}
		}
		Ok(())
	}
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_upper_bound(var) <= val {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.state.int_vars[iv].get_bool_lit(LitMeaning::Less(val + 1))
				else {
					unreachable!()
				};
				self.state.register_reason(lit, reason, self.prop);
				self.prop_queue.push(lit);
			}
			IntViewInner::Const(i) => {
				if i > val {
					todo!()
				}
			}
		}
		Ok(())
	}
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_val(var) == Some(val) {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.state.int_vars[iv].get_bool_lit(LitMeaning::Eq(val))
				else {
					unreachable!()
				};
				self.state.register_reason(lit, reason, self.prop);
				self.prop_queue.push(lit);
				// TODO: Should this trigger notify?
				// TODO: Check conflict
			}
			IntViewInner::Const(i) => {
				if i != val {
					todo!()
				}
			}
		};
		Ok(())
	}
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: &ReasonBuilder,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if !self.check_int_in_domain(var, val) {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.state.int_vars[iv].get_bool_lit(LitMeaning::NotEq(val))
				else {
					unreachable!()
				};
				self.state.register_reason(lit, reason, self.prop);
				self.prop_queue.push(lit);
				// TODO: Should this trigger notify?
				// TODO: Check conflict
			}
			IntViewInner::Const(i) => {
				if i == val {
					todo!()
				}
			}
		};
		Ok(())
	}
}
