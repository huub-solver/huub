use delegate::delegate;

use super::{int_var::IntVarRef, PropRef, State};
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
				Some(_) | None => {
					let change = self
						.state
						.sat_trail
						.assign(lit.var(), if lit.is_negated() { !val } else { val });
					debug_assert_eq!(change, HasChanged::Changed);
					let propagated_lit = if val { lit } else { !lit };
					self.state
						.register_reason(propagated_lit, reason, self.prop);
					self.prop_queue.push(propagated_lit);
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
		let mut lit_req = LitMeaning::GreaterEq(val);
		if let IntViewInner::Linear { transformer, .. } = var.0 {
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				if self.check_satisfied(iv, &lit_req) {
					return Ok(());
				}
				let lit = match self.state.int_vars[iv].get_bool_lit(lit_req) {
					BoolView(BoolViewInner::Lit(lit)) => lit,
					BoolView(BoolViewInner::Const(false)) => {
						return Err(Conflict::new(reason, self.prop));
					}
					_ => unreachable!(),
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
		let mut lit_req = LitMeaning::Less(val + 1);
		if let IntViewInner::Linear { transformer, .. } = var.0 {
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				if self.check_satisfied(iv, &lit_req) {
					return Ok(());
				}
				let lit = match self.state.int_vars[iv].get_bool_lit(lit_req) {
					BoolView(BoolViewInner::Lit(lit)) => lit,
					BoolView(BoolViewInner::Const(false)) => {
						return Err(Conflict::new(reason, self.prop));
					}
					_ => unreachable!(),
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
		let mut lit_req = LitMeaning::Eq(val);
		if let IntViewInner::Linear { transformer, .. } = var.0 {
			if let Some(lit) = transformer.rev_transform_lit(lit_req) {
				lit_req = lit;
			} else {
				return Err(Conflict::new(reason, self.prop));
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				if self.check_satisfied(iv, &lit_req) {
					return Ok(());
				}
				let lit = match self.state.int_vars[iv].get_bool_lit(lit_req) {
					BoolView(BoolViewInner::Lit(lit)) => lit,
					BoolView(BoolViewInner::Const(false)) => {
						return Err(Conflict::new(reason, self.prop));
					}
					_ => unreachable!(),
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
		let mut lit_req = LitMeaning::NotEq(val);
		if let IntViewInner::Linear { transformer, .. } = var.0 {
			if let Some(lit) = transformer.rev_transform_lit(lit_req) {
				lit_req = lit;
			} else {
				return Ok(());
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				if self.check_satisfied(iv, &lit_req) {
					return Ok(());
				}
				let lit = match self.state.int_vars[iv].get_bool_lit(lit_req) {
					BoolView(BoolViewInner::Lit(lit)) => lit,
					BoolView(BoolViewInner::Const(false)) => {
						return Err(Conflict::new(reason, self.prop));
					}
					_ => unreachable!(),
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

impl PropagationContext<'_> {
	#[inline]
	pub(crate) fn check_satisfied(&self, var: IntVarRef, lit: &LitMeaning) -> bool {
		match lit {
			LitMeaning::Eq(i) => {
				let lb = self.state.int_trail[self.state.int_vars[var].lower_bound];
				let ub = self.state.int_trail[self.state.int_vars[var].upper_bound];
				lb == *i && ub == *i
			}
			LitMeaning::NotEq(i) => {
				let lb = self.state.int_trail[self.state.int_vars[var].lower_bound];
				let ub = self.state.int_trail[self.state.int_vars[var].upper_bound];
				if *i < lb || *i > ub {
					true
				} else {
					let eq_lit = self.state.int_vars[var].get_bool_lit(LitMeaning::NotEq(*i));
					self.get_bool_val(eq_lit).unwrap_or(false)
				}
			}
			LitMeaning::GreaterEq(i) => {
				let lb = self.state.int_trail[self.state.int_vars[var].lower_bound];
				lb >= *i
			}
			LitMeaning::Less(i) => {
				let ub = self.state.int_trail[self.state.int_vars[var].upper_bound];
				ub < *i
			}
		}
	}
}
