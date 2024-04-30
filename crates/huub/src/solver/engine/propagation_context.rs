use delegate::delegate;

use super::{PropRef, State};
use crate::{
	propagator::{conflict::Conflict, reason::ReasonBuilder, ExplainActions, PropagationActions},
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
					return Err(Conflict::new(reason, self.prop));
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
					return Err(Conflict::new(reason, self.prop));
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
					return Err(Conflict::new(reason, self.prop));
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
					return Err(Conflict::new(reason, self.prop));
				}
			}
		};
		Ok(())
	}
}

impl ExplainActions for PropagationContext<'_> {
	delegate! {
		to self.state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_lit(&self, var: IntView, meaning: LitMeaning) -> BoolView;
		}
	}
}
