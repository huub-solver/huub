use std::collections::HashMap;

use index_vec::IndexVec;
use pindakaas::{solver::SolvingActions, Lit as RawLit};

use crate::{
	propagator::{conflict::Conflict, reason::Reason},
	solver::{
		engine::{
			int_var::{IntVal, IntVar, IntVarRef, LitMeaning},
			trail::{SatTrail, Trail},
			PropRef, TrailedInt,
		},
		view::IntViewInner,
		IntView,
	},
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
	pub fn get_bool_val(&self, lit: RawLit) -> Option<bool> {
		self.sat_trail.get(lit)
	}

	pub fn get_int_lit(&mut self, var: IntView, bv: LitMeaning) -> Option<RawLit> {
		match var.0 {
			IntViewInner::VarRef(iv) => Some(self.int_vars[iv].get_bool_var(bv)),
			IntViewInner::Const(_) => None,
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
				let lb = self.get_int_lower_bound(var);
				let ub = self.get_int_upper_bound(var);
				if (lb..=ub).contains(&val) {
					let lit = self.int_vars[iv].get_bool_var(LitMeaning::Eq(val));
					self.sat_trail.get(lit).unwrap_or(true)
				} else {
					false
				}
			}
			IntViewInner::Const(i) => i == val,
		}
	}

	#[allow(dead_code)]
	pub fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		r: Option<Reason>,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_lower_bound(var) >= val {
					return Ok(());
				}
				let lit = self.int_vars[iv].get_bool_var(LitMeaning::GreaterEq(val));
				if let Some(r) = r {
					self.reason_map.insert(lit, r);
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
	pub fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		r: Option<Reason>,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_upper_bound(var) <= val {
					return Ok(());
				}
				let lit = self.int_vars[iv].get_bool_var(LitMeaning::Less(val + 1));
				if let Some(r) = r {
					self.reason_map.insert(lit, r);
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
	pub fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		r: Option<Reason>,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if self.get_int_val(var) == Some(val) {
					return Ok(());
				}
				let lit = self.int_vars[iv].get_bool_var(LitMeaning::Eq(val));
				if let Some(r) = r {
					self.reason_map.insert(lit, r);
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

	pub fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		r: Option<Reason>,
	) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				if !self.check_int_in_domain(var, val) {
					return Ok(());
				}
				let lit = self.int_vars[iv].get_bool_var(LitMeaning::NotEq(val));
				if let Some(r) = r {
					self.reason_map.insert(lit, r);
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
	pub fn lazy_reason(&self, data: u64) -> Reason {
		Reason::Lazy(self.prop, data)
	}
}
