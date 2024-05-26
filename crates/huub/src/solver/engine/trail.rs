use std::{
	collections::HashMap,
	mem::{self, transmute},
};

use index_vec::IndexVec;
use pindakaas::{Lit as RawLit, Var as RawVar};

use crate::{actions::trailing::TrailingActions, IntVal};

index_vec::define_index_type! {
	/// Identifies an trailed integer tracked within [`Solver`]
	pub struct TrailedInt = u32;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Trail {
	trail: Vec<u32>,
	prev_len: Vec<usize>,

	int_value: IndexVec<TrailedInt, IntVal>,
	sat_value: HashMap<RawVar, bool>,
}

impl Default for Trail {
	fn default() -> Self {
		Self {
			trail: Vec::new(),
			prev_len: Vec::new(),
			int_value: IndexVec::new(),
			sat_value: HashMap::new(),
		}
	}
}

impl Trail {
	fn push_trail(&mut self, event: TrailEvent) {
		match event {
			TrailEvent::SatAssignment(r) => {
				let r = i32::from(r);
				self.trail.push(r as u32)
			}
			TrailEvent::IntAssignment(i, v) => {
				let (low, high) = (v as i32, (v >> 32) as i32);
				self.trail.push(low as u32);
				self.trail.push(high as u32);
				let i = -(usize::from(i) as i32);
				self.trail.push(i as u32)
			}
		}
	}
	fn pop_trail(&mut self) -> Option<TrailEvent> {
		if self.trail.is_empty() {
			return None;
		}
		let i = self.trail.pop().unwrap() as i32;
		Some(if i.is_positive() {
			// SAFETY: This is safe because RawVar uses the same representation as i32
			TrailEvent::SatAssignment(unsafe { transmute(i) })
		} else {
			let i = -i as usize;
			let high = self.trail.pop().unwrap() as u64;
			let low = self.trail.pop().unwrap() as u64;
			TrailEvent::IntAssignment(i.into(), ((high << 32) | low) as i64)
		})
	}
	fn undo_event(&mut self, event: TrailEvent) {
		match event {
			TrailEvent::SatAssignment(r) => {
				let _ = self.sat_value.remove(&r);
			}
			TrailEvent::IntAssignment(i, v) => {
				self.int_value[i] = v;
			}
		}
	}

	pub(crate) fn undo_until_found_lit(&mut self, lit: RawLit) {
		let var = lit.var();
		while let Some(event) = self.pop_trail() {
			let found = matches!(event, TrailEvent::SatAssignment(r) if r == var);
			self.undo_event(event);
			if found {
				return;
			}
		}
		panic!("literal {:?} was never assigned", lit)
	}

	pub(crate) fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len());
	}
	pub(crate) fn notify_backtrack(&mut self, level: usize) {
		self.prev_len.truncate(level + 1);
		let len = self.prev_len.pop().unwrap_or(0);
		debug_assert!(
			len <= self.trail.len(),
			"backtracking to level {level} length {len}, but trail is already at length {}",
			self.trail.len()
		);
		while self.trail.len() > len {
			let event = self.pop_trail().unwrap();
			self.undo_event(event);
		}
		debug_assert_eq!(self.trail.len(), len);
	}
	pub(crate) fn decision_level(&self) -> usize {
		self.prev_len.len()
	}

	pub(crate) fn track_int(&mut self, val: IntVal) -> TrailedInt {
		self.int_value.push(val)
	}

	pub(crate) fn get_sat_value(&self, lit: impl Into<RawLit>) -> Option<bool> {
		let lit = lit.into();
		self.sat_value
			.get(&lit.var())
			.copied()
			.map(|x| if lit.is_negated() { !x } else { x })
	}
	pub(crate) fn assign_sat(&mut self, lit: RawLit) -> Option<bool> {
		let var = lit.var();
		let val = !lit.is_negated();

		let x = self.sat_value.insert(var, val);
		if x.is_none() && !self.prev_len.is_empty() {
			self.push_trail(TrailEvent::SatAssignment(var));
		}
		x
	}
}

impl TrailingActions for Trail {
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal {
		self.int_value[i]
	}
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal {
		if self.int_value[i] == v {
			return v;
		}
		let old = mem::replace(&mut self.int_value[i], v);
		if !self.prev_len.is_empty() {
			self.push_trail(TrailEvent::IntAssignment(i, old));
		}
		old
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TrailEvent {
	SatAssignment(RawVar),
	IntAssignment(TrailedInt, IntVal),
}

#[cfg(test)]
mod tests {
	use pindakaas::solver::{cadical::Cadical, NextVarRange};

	use crate::{
		solver::engine::trail::{Trail, TrailEvent, TrailedInt},
		IntVal,
	};

	#[test]
	fn test_trail_event() {
		let mut slv = Cadical::default();
		let lits = slv.next_var_range(10).unwrap();
		let int_events: [(u32, IntVal); 10] = [
			(0, 0),
			(1, 1),
			(2, -1),
			(i32::MAX as u32, IntVal::MAX),
			(9474, IntVal::MIN),
			(6966, 4084),
			(4099, -9967),
			(1977, 9076),
			(2729, -4312),
			(941, 1718),
		];

		let mut trail = Trail::default();
		for (l, (i, v)) in lits.clone().zip(int_events.iter()) {
			trail.push_trail(TrailEvent::SatAssignment(l));
			trail.push_trail(TrailEvent::IntAssignment(TrailedInt::from_raw(*i), *v));
		}
		for (l, (i, v)) in lits.rev().zip(int_events.iter().rev()) {
			assert_eq!(
				trail.pop_trail().unwrap(),
				TrailEvent::IntAssignment(TrailedInt::from_raw(*i), *v)
			);
			assert_eq!(trail.pop_trail().unwrap(), TrailEvent::SatAssignment(l))
		}
	}
}
