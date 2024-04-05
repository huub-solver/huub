use std::collections::HashMap;

use index_vec::IndexVec;
use pindakaas::{solver::SolvingActions, Lit as RawLit};

use crate::{
	propagator::{conflict::Conflict, reason::Reason},
	solver::{
		engine::{
			int_var::{IntVar, IntVarRef, LitMeaning},
			PropRef,
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
}

impl PropagationActions<'_> {
	pub fn int_get_bool_lit(&mut self, var: IntView, bv: LitMeaning) -> RawLit {
		match var.0 {
			IntViewInner::VarRef(iv) => self.int_vars[iv].get_bool_var(bv),
		}
	}

	pub fn int_get_val(&mut self, var: IntView) -> Option<i64> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				let dom = &self.int_vars[iv].domain;
				if dom.lower_bound().unwrap() == dom.upper_bound().unwrap() {
					Some(*dom.lower_bound().unwrap())
				} else {
					None
				}
			}
		}
	}

	pub fn int_neq_val(&mut self, var: IntView, val: i64, r: Reason) -> Result<(), Conflict> {
		match var.0 {
			IntViewInner::VarRef(iv) => {
				let lit = self.int_vars[iv].get_bool_var(LitMeaning::Eq(val));
				self.reason_map.insert(!lit, r);
				self.lit_queue.push(!lit);
				// TODO: Should this trigger notify?
				// TODO: Check conflict
			}
		};
		Ok(())
	}

	#[allow(dead_code)] // TODO
	pub fn lazy_reason(&self, data: u64) -> Reason {
		Reason::Lazy(self.prop, data)
	}
}
