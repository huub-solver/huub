use std::{
	collections::HashMap,
	mem::{self, transmute},
};

use index_vec::IndexVec;
use pindakaas::{Lit as RawLit, Var as RawVar};
use tracing::{debug, trace};

use crate::{actions::trailing::TrailingActions, IntVal};

index_vec::define_index_type! {
	/// Identifies an trailed integer tracked within [`Solver`]
	pub struct TrailedInt = u32;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Trail {
	trail: Vec<u32>,
	pos: usize,
	prev_len: Vec<usize>,

	int_value: IndexVec<TrailedInt, IntVal>,
	sat_value: HashMap<RawVar, bool>,
	sat_restore_value: HashMap<RawVar, bool>,
}

impl Default for Trail {
	fn default() -> Self {
		Self {
			trail: Vec::new(),
			pos: 0,
			prev_len: Vec::new(),
			int_value: IndexVec::new(),
			sat_value: HashMap::new(),
			sat_restore_value: HashMap::new(),
		}
	}
}

impl Trail {
	fn push_trail(&mut self, event: TrailEvent) {
		debug_assert_eq!(self.pos, self.trail.len());
		match event {
			TrailEvent::SatAssignment(_) => self.trail.push(0),
			TrailEvent::IntAssignment(_, _) => self.trail.extend([0; 3]),
		}
		event.write_trail(&mut self.trail[self.pos..]);
		self.pos = self.trail.len();
	}
	fn undo<const RESTORE: bool>(&mut self) -> Option<TrailEvent> {
		debug_assert!(self.pos <= self.trail.len());
		if self.pos == 0 {
			return None;
		}
		// Find event before current position
		let event = if (self.trail[self.pos - 1] as i32).is_positive() {
			self.pos -= 1;
			TrailEvent::sat_from_raw(self.trail[self.pos])
		} else {
			self.pos -= 3;
			TrailEvent::int_from_trail(self.trail[self.pos..=self.pos + 2].try_into().unwrap())
		};

		match event {
			TrailEvent::SatAssignment(r) => {
				let b = self.sat_value.remove(&r).unwrap();
				if RESTORE {
					let x = self.sat_restore_value.insert(r, b);
					debug_assert!(x.is_none());
				}
			}
			TrailEvent::IntAssignment(i, v) => {
				if RESTORE {
					let x = self.int_value[i];
					TrailEvent::IntAssignment(i, x)
						.write_rev_trail(&mut self.trail[self.pos..=self.pos + 2]);
				}
				self.int_value[i] = v;
			}
		}
		Some(event)
	}

	fn redo(&mut self) -> Option<TrailEvent> {
		debug_assert!(self.pos <= self.trail.len());

		if self.pos == self.trail.len() {
			return None;
		}
		// Find event at current position
		let event = if (self.trail[self.pos] as i32).is_positive() {
			self.pos += 1;
			TrailEvent::sat_from_raw(self.trail[self.pos - 1])
		} else {
			self.pos += 3;
			TrailEvent::int_from_rev_trail(self.trail[self.pos - 3..self.pos].try_into().unwrap())
		};

		match event {
			TrailEvent::SatAssignment(r) => {
				let b = self.sat_restore_value.remove(&r).unwrap();
				let x = self.sat_value.insert(r, b);
				debug_assert!(x.is_none());
			}
			TrailEvent::IntAssignment(i, v) => {
				let x = self.int_value[i];
				TrailEvent::IntAssignment(i, x)
					.write_trail(&mut self.trail[self.pos - 3..self.pos]);

				self.int_value[i] = v;
			}
		}
		Some(event)
	}

	pub(crate) fn undo_until_found_lit(&mut self, lit: RawLit) {
		let var = lit.var();
		if !self.sat_value.contains_key(&var) {
			if !self.sat_restore_value.contains_key(&var) {
				panic!("literal is not present in the trail")
			}
			debug!(
				lit = i32::from(lit),
				"literal is already unset, restoring to point of setting literal"
			);
			while let Some(event) = self.redo() {
				let found = matches!(event, TrailEvent::SatAssignment(r) if r == var);
				if found {
					trace!(
						len = self.pos,
						lit = i32::from(lit),
						"reversed the trail to find literal"
					);
					return;
				}
			}
			unreachable!("literal not on trail")
		}
		while let Some(event) = self.undo::<true>() {
			let found = matches!(event, TrailEvent::SatAssignment(r) if r == var);
			if found {
				let e = self.redo();
				debug_assert_eq!(e, Some(TrailEvent::SatAssignment(var)));
				trace!(
					len = self.pos,
					lit = i32::from(lit),
					"reversed the trail to find literal"
				);
				return;
			}
		}
		// return to the root level, lit is a persistent literal
	}

	pub(crate) fn is_backtracking(&self) -> bool {
		self.pos != self.trail.len()
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
		if len <= self.pos {
			while self.pos > len {
				let _ = self.undo::<false>();
			}
		} else {
			while self.pos < len {
				let _ = self.redo();
			}
		}
		debug_assert_eq!(self.pos, len);
		self.trail.truncate(len);
		self.sat_restore_value.clear();
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

impl TrailEvent {
	#[inline]
	fn sat_from_raw(raw: u32) -> Self {
		// SAFETY: This is safe because RawVar uses the same representation as i32
		TrailEvent::SatAssignment(unsafe { transmute(raw) })
	}

	#[inline]
	fn int_from_trail(raw: [u32; 3]) -> Self {
		let i = -(raw[2] as i32) as usize;
		let high = raw[1] as u64;
		let low = raw[0] as u64;
		TrailEvent::IntAssignment(i.into(), ((high << 32) | low) as i64)
	}

	#[inline]
	fn int_from_rev_trail(raw: [u32; 3]) -> Self {
		let i = -(raw[0] as i32) as usize;
		let high = raw[1] as u64;
		let low = raw[2] as u64;
		TrailEvent::IntAssignment(i.into(), ((high << 32) | low) as i64)
	}

	#[inline]
	fn write_trail(&self, trail: &mut [u32]) {
		match self {
			TrailEvent::SatAssignment(var) => trail[0] = i32::from(*var) as u32,
			TrailEvent::IntAssignment(i, val) => {
				let val = *val as u64;
				let high = (val >> 32) as u32;
				let low = val as u32;
				trail[0] = low;
				trail[1] = high;
				trail[2] = -(usize::from(*i) as i32) as u32;
			}
		}
	}

	#[inline]
	fn write_rev_trail(&self, trail: &mut [u32]) {
		match self {
			TrailEvent::SatAssignment(var) => trail[0] = i32::from(*var) as u32,
			TrailEvent::IntAssignment(i, val) => {
				let val = *val as u64;
				let high = (val >> 32) as u32;
				let low = val as u32;
				trail[0] = -(usize::from(*i) as i32) as u32;
				trail[1] = high;
				trail[2] = low
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::solver::{cadical::Cadical, NextVarRange};

	use crate::{
		solver::engine::trail::{Trail, TrailEvent},
		IntVal,
	};

	#[test]
	fn test_trail_event() {
		let mut slv = Cadical::default();
		let mut trail = Trail::default();
		let lits = slv.next_var_range(10).unwrap();
		let int_events: Vec<_> = [
			0,
			1,
			-1,
			IntVal::MAX,
			IntVal::MIN,
			4084,
			-9967,
			9076,
			-4312,
			1718,
		]
		.into_iter()
		.map(|i| (trail.track_int(0), i))
		.collect();

		for (l, (i, v)) in lits.clone().zip(int_events.iter()) {
			trail.push_trail(TrailEvent::SatAssignment(l));
			let _ = trail.assign_sat(if usize::from(*i) % 2 == 0 {
				l.into()
			} else {
				!l
			});
			trail.push_trail(TrailEvent::IntAssignment(*i, *v));
		}
		for (l, (i, v)) in lits.rev().zip(int_events.iter().rev()) {
			let e = trail.undo::<true>().unwrap();
			assert_eq!(e, TrailEvent::IntAssignment(*i, *v));
			let e = trail.undo::<true>().unwrap();
			assert_eq!(e, TrailEvent::SatAssignment(l));
		}
	}
}
