use std::collections::HashMap;

use index_vec::IndexVec;
use pindakaas::{solver::SolvingActions, Lit as RawLit};

use super::reason::ReasonBuilder;
use crate::{
	propagator::{conflict::Conflict, reason::Reason},
	solver::{
		engine::{
			int_var::{IntVal, IntVar, IntVarRef, LitMeaning},
			trail::{SatTrail, Trail},
			PropRef, TrailedInt,
		},
		view::{BoolViewInner, IntViewInner},
		IntView,
	},
	BoolView,
};

pub struct PropagationActions<'a> {
	pub(crate) prop: PropRef,
	pub(crate) lit_queue: Vec<RawLit>,
	#[allow(dead_code)] // TODO
	pub(crate) sat: &'a mut dyn SolvingActions,
	pub(crate) int_vars: &'a mut IndexVec<IntVarRef, IntVar>,
	pub(crate) reason_map: &'a mut HashMap<RawLit, Reason>,
	pub(crate) int_trail: &'a mut Trail<TrailedInt, IntVal>,
	pub(crate) sat_trail: &'a mut SatTrail,
}

impl PropagationActions<'_> {
	#[allow(dead_code)] // TODO
	pub fn get_bool_val(&self, bv: BoolView) -> Option<bool> {
		match bv.0 {
			BoolViewInner::Lit(lit) => self.sat_trail.get(lit),
			BoolViewInner::Const(b) => Some(b),
		}
	}

	pub fn get_int_lit(&mut self, var: IntView, bv: LitMeaning) -> BoolView {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_vars[iv].get_bool_lit(bv),
			IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match bv {
				LitMeaning::Eq(i) => c == i,
				LitMeaning::NotEq(i) => c != i,
				LitMeaning::GreaterEq(i) => c >= i,
				LitMeaning::Less(i) => c < i,
			})),
		}
	}

	pub fn get_int_lower_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_trail[self.int_vars[iv].lower_bound],
			IntViewInner::Const(i) => i,
		}
	}

	pub fn get_int_upper_bound(&self, var: IntView) -> IntVal {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_trail[self.int_vars[iv].upper_bound],
			IntViewInner::Const(i) => i,
		}
	}

	pub fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		let lb = self.get_int_lower_bound(var);
		let ub = self.get_int_upper_bound(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}

	pub fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				match self.int_vars[iv].get_bool_lit(LitMeaning::Eq(val)).0 {
					BoolViewInner::Lit(lit) => self.sat_trail.get(lit).unwrap_or(true),
					BoolViewInner::Const(b) => b,
				}
			}
			IntViewInner::Const(i) => i == val,
		}
	}

	#[allow(dead_code)]
	pub fn set_int_lower_bound<R: TryInto<Reason, Error = bool>>(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: R,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_lower_bound(var) >= val {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.int_vars[iv].get_bool_lit(LitMeaning::GreaterEq(val))
				else {
					unreachable!()
				};
				match reason.try_into() {
					Ok(reason) => {
						self.reason_map.insert(lit, reason);
					}
					Err(false) => return Ok(()),
					Err(true) => (),
				}
				self.lit_queue.push(lit);
			}
			IntViewInner::Const(i) => {
				if i < val {
					todo!()
				}
			}
		}
		Ok(())
	}

	#[allow(dead_code)]
	pub fn set_int_upper_bound<R: TryInto<Reason, Error = bool>>(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: R,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_upper_bound(var) <= val {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.int_vars[iv].get_bool_lit(LitMeaning::Less(val + 1))
				else {
					unreachable!()
				};
				match reason.try_into() {
					Ok(reason) => {
						self.reason_map.insert(lit, reason);
					}
					Err(false) => return Ok(()),
					Err(true) => (),
				}
				self.lit_queue.push(lit);
			}
			IntViewInner::Const(i) => {
				if i > val {
					todo!()
				}
			}
		}
		Ok(())
	}

	#[allow(dead_code)]
	pub fn set_int_val<R: TryInto<Reason, Error = bool>>(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: R,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_val(var) == Some(val) {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.int_vars[iv].get_bool_lit(LitMeaning::Eq(val))
				else {
					unreachable!()
				};
				match reason.try_into() {
					Ok(reason) => {
						self.reason_map.insert(lit, reason);
					}
					Err(false) => return Ok(()),
					Err(true) => (),
				}
				self.lit_queue.push(lit);
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

	pub fn set_int_not_eq<R: TryInto<Reason, Error = bool>>(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: R,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if !self.check_int_in_domain(var, val) {
					return Ok(());
				}
				let BoolView(BoolViewInner::Lit(lit)) =
					self.int_vars[iv].get_bool_lit(LitMeaning::NotEq(val))
				else {
					unreachable!()
				};
				match reason.try_into() {
					Ok(reason) => {
						self.reason_map.insert(lit, reason);
					}
					Err(false) => return Ok(()),
					Err(true) => (),
				}
				self.lit_queue.push(lit);
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

	#[allow(dead_code)] // TODO
	pub fn lazy_reason(&self, data: u64) -> ReasonBuilder {
		ReasonBuilder::Lazy(self.prop, data)
	}
}
