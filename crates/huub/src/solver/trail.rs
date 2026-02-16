//! This module contains the data structures used to trail values during the
//! search process. Changes made to trailed values are recorded in the central
//! [`Trail`] structure, if the search process needs to backtrack, then these
//! values can be restored to their previous state.

use std::{marker::PhantomData, mem, num::NonZeroI32};

use pindakaas::{Lit as RawLit, Var as RawVar};
use tracing::trace;

use crate::{
	actions::{Trailed, TrailingActions},
	helpers::bytes::Bytes,
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
/// A structure that stores the currently assigned value of a Boolean variable
/// and the value it had while undoing the last assignment.
struct BoolStore {
	/// The current value of the variable, if it is assigned.
	value: Option<bool>,
	/// The value of the variable, when it was untrailed.
	restore: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Storage structure that allows restoring tracked values to an earlier state.
pub(crate) struct Trail {
	/// The storage of event that have been trailed.
	///
	/// Note that the trail is contains a sequence of integers, but 1 or 3 of
	/// these integers are intended to be read as a [`TrailEvent`].
	trail: Vec<u32>,
	/// The current position in the trail.
	///
	/// This is used when undoing changes from the trail, any events after `pos`
	/// have been transformed so they can be redone if required.
	pos: usize,
	/// The length of the trail when previous decisions were made.
	prev_len: Vec<usize>,

	/// Stores the current value of trailed integer values.
	int_value: Vec<[u8; 8]>,
	/// Stores the current assigned values of Boolean variables, and "redo"
	/// values when untrailing.
	sat_store: Vec<BoolStore>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// An event that is recorded such that it can be undone.
pub(crate) enum TrailEvent {
	/// The assignment of a Boolean variable.
	SatAssignment(RawVar),
	/// The assignment of a trailed integer value, and the previous value it
	/// had.
	IntAssignment {
		/// The index of the trailed value in the trail storage.
		index: u32,
		/// The previous value encoded as bytes.
		value: [u8; 8],
	},
}

impl Trail {
	/// A trailed integer that is used to track the currently active brancher.
	pub(crate) const CURRENT_BRANCHER: Trailed<usize> = Trailed {
		index: 0,
		ty: PhantomData,
	};

	/// Record the assignment of a literal in the Trail
	///
	/// # Warning
	/// This method expects that `self.sat_store` has already been extended to
	/// the correct length (using [`Self::grow_to_boolvar`]).
	pub(crate) fn assign_lit(&mut self, lit: RawLit) -> Option<bool> {
		let var = lit.var();
		let store = &mut self.sat_store[Self::sat_index(var)].value;
		if let Some(val) = *store {
			Some(if lit.is_negated() { !val } else { val })
		} else {
			*store = Some(!lit.is_negated());
			self.push_trail(TrailEvent::SatAssignment(var));
			None
		}
	}

	/// Return the current decision level
	pub(crate) fn decision_level(&self) -> u32 {
		self.prev_len.len() as u32
	}

	/// Method used to restore the state of all value to the point at which a
	/// literal was assigned.
	///
	/// This method is used when creating lazy explanations, as the SAT solver
	/// does not allow the usage of literals that are not
	pub(crate) fn goto_assign_lit(&mut self, lit: RawLit) {
		let var = lit.var();
		if self.sat_store[Self::sat_index(var)].value.is_none() {
			while let Some(event) = self.redo() {
				if matches!(event, TrailEvent::SatAssignment(r) if r == var) {
					let e: Option<TrailEvent> = self.undo::<true>();
					debug_assert_eq!(e, Some(TrailEvent::SatAssignment(var)));
					trace!(
						len = self.pos,
						lit = i32::from(lit),
						"redo to when literal was set"
					);
					return;
				}
			}
			trace!(
				len = self.pos,
				lit = i32::from(lit),
				"trail reset for unknown literal"
			);
			return;
		}
		while let Some(event) = self.undo::<true>() {
			if matches!(event, TrailEvent::SatAssignment(r) if r == var) {
				trace!(
					len = self.pos,
					lit = i32::from(lit),
					"undo to when literal was set"
				);
				return;
			}
		}
		// return to the root level, lit is a persistent literal
	}

	/// Grow the storage for the state of Boolean variables to include enough
	/// space for `var`.
	pub(crate) fn grow_to_boolvar(&mut self, var: RawVar) {
		let idx = Self::sat_index(var);
		if idx >= self.sat_store.len() {
			self.sat_store.resize(idx + 1, Default::default());
		}
	}

	/// Notify the Trail of a backtracking operation.
	///
	/// The state of the trailed values is restored to the requested level.
	pub(crate) fn notify_backtrack(&mut self, level: usize) {
		// TODO: this is a fix for an issue in the CaDiCaL implementation of the IPASIR UP interface: https://github.com/arminbiere/cadical/issues/92
		if level >= self.prev_len.len() {
			return;
		}

		let len = self.prev_len[level];
		self.prev_len.truncate(level);
		debug_assert!(
			len <= self.trail.len(),
			"backtracking to level {level} length {len}, but trail is already at length {}",
			self.trail.len()
		);
		if len <= self.pos {
			while self.pos > len {
				self.undo::<false>();
			}
		} else {
			while self.pos < len {
				self.redo();
			}
		}
		debug_assert_eq!(self.pos, len);
		self.trail.truncate(len);
	}

	/// Notify the Trail of a new decision level to which the trail can be
	/// restored.
	pub(crate) fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len());
	}

	/// Internal method to push a change to the trail
	fn push_trail(&mut self, event: TrailEvent) {
		debug_assert_eq!(self.pos, self.trail.len());
		match event {
			TrailEvent::SatAssignment(_) => self.trail.push(0),
			TrailEvent::IntAssignment { .. } => self.trail.extend([0; 3]),
		}
		event.write_trail(&mut self.trail[self.pos..]);
		self.pos = self.trail.len();
	}

	/// Internal method to redo the last undone change on the trail
	///
	/// Note that this method will return `None` if no change has been undone
	/// since the last `backtrack` or the creation of the trail.
	///
	/// This method is required because:
	/// - The solver might not ask for explanations in order (and we restore the
	///   trail to the point of propagation for correctness).
	/// - The solver might decide to perform chronological backtracking (and not
	///   backtrack to the decision level of earliest explained change).
	fn redo(&mut self) -> Option<TrailEvent> {
		debug_assert!(self.pos <= self.trail.len());

		if self.pos == self.trail.len() {
			return None;
		}
		// Find event at current position
		let event = if (self.trail[self.pos] as i32).is_positive() {
			self.pos += 1;
			TrailEvent::SatAssignment(
				RawLit::from_raw(NonZeroI32::new(self.trail[self.pos - 1] as i32).unwrap()).var(),
			)
		} else {
			self.pos += 3;
			TrailEvent::int_from_rev_trail(self.trail[self.pos - 3..self.pos].try_into().unwrap())
		};

		match event {
			TrailEvent::SatAssignment(r) => {
				let store = &mut self.sat_store[Self::sat_index(r)];
				debug_assert!(store.restore.is_some());
				debug_assert!(store.value.is_none());
				mem::swap(&mut store.restore, &mut store.value);
			}
			TrailEvent::IntAssignment { index, value } => {
				let x = self.int_value[index as usize];
				TrailEvent::IntAssignment { index, value: x }
					.write_trail(&mut self.trail[self.pos - 3..self.pos]);

				self.int_value[index as usize] = value;
			}
		}
		Some(event)
	}

	/// Ensure that the trail is in a position where it can record new changes.
	pub(crate) fn reset_to_trail_head(&mut self) {
		while self.redo().is_some() {}
	}

	#[inline]
	/// Return the index for `sat_store` based on a [`RawVar`].
	fn sat_index(var: RawVar) -> usize {
		// TODO: Consider grounding (either always deduct 1 because there is no var
		// 0, or at the least observed var)
		i32::from(var) as usize
	}

	/// Get the current assigned value for a literal (if any).
	pub(crate) fn sat_value(&self, lit: impl Into<RawLit>) -> Option<bool> {
		let lit = lit.into();
		// Note that this doesn't use direct indexing as some operations might check
		// the value of the variable before it is observed by the solver
		self.sat_store
			.get(Self::sat_index(lit.var()))
			.and_then(|store| store.value)
			.map(|x| if lit.is_negated() { !x } else { x })
	}

	/// Create a new trailed integer with initial value `val`
	pub(crate) fn track<T: Bytes>(&mut self, val: T) -> Trailed<T> {
		self.int_value.push(val.to_bytes());
		Trailed {
			index: (self.int_value.len() - 1) as u32,
			ty: PhantomData,
		}
	}

	/// Internal method to undo the last change on the trail.
	///
	/// Note that his method will return `None` if the trail is empty.
	///
	/// When the generic `RESTORE` is set to true, then the changes that have
	/// been undone can be redone. See [`Self::redo`] for more details.
	fn undo<const RESTORE: bool>(&mut self) -> Option<TrailEvent> {
		debug_assert!(self.pos <= self.trail.len());
		if self.pos == 0 {
			return None;
		}
		// Find event before current position
		let event = if (self.trail[self.pos - 1] as i32).is_positive() {
			self.pos -= 1;
			TrailEvent::SatAssignment(
				RawLit::from_raw(NonZeroI32::new(self.trail[self.pos] as i32).unwrap()).var(),
			)
		} else {
			self.pos -= 3;
			TrailEvent::int_from_trail(self.trail[self.pos..=self.pos + 2].try_into().unwrap())
		};

		match event {
			TrailEvent::SatAssignment(r) => {
				let store = &mut self.sat_store[Self::sat_index(r)];
				let b = mem::take(&mut store.value);
				if RESTORE {
					// Note that `store.restore` might (before assignment)
					// contain a previous value to be restored.
					store.restore = b;
				}
			}
			TrailEvent::IntAssignment { index, value } => {
				if RESTORE {
					let x = self.int_value[index as usize];
					TrailEvent::IntAssignment { index, value: x }
						.write_rev_trail(&mut self.trail[self.pos..=self.pos + 2]);
				}
				self.int_value[index as usize] = value;
			}
		}
		Some(event)
	}
}

impl Default for Trail {
	fn default() -> Self {
		Self {
			trail: Vec::new(),
			pos: 0,
			prev_len: Vec::new(),
			int_value: vec![0_u64.to_bytes()],
			sat_store: Vec::new(),
		}
	}
}

impl TrailingActions for Trail {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		let bytes = v.to_bytes();
		if self.int_value[i.index as usize] == bytes {
			return T::from_bytes(bytes);
		}
		let old = mem::replace(&mut self.int_value[i.index as usize], bytes);
		self.push_trail(TrailEvent::IntAssignment {
			index: i.index,
			value: old,
		});
		T::from_bytes(old)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		T::from_bytes(self.int_value[i.index as usize])
	}
}

impl TrailEvent {
	#[inline]
	/// Internal method used to transform a slice of the trail to a
	/// [`TrailEvent::IntAssignment`] object for the [`Trail::redo`] method.
	fn int_from_rev_trail(raw: [u32; 3]) -> Self {
		let index = -(raw[0] as i32) as u32;
		let high = raw[1] as u64;
		let low = raw[2] as u64;
		let value = ((high << 32) | low).to_ne_bytes();
		TrailEvent::IntAssignment { index, value }
	}

	#[inline]
	/// Internal method used to transform a slice of the trail to a
	/// [`TrailEvent::IntAssignment`] object for the [`Trail::undo`] method.
	fn int_from_trail(raw: [u32; 3]) -> Self {
		let index = -(raw[2] as i32) as u32;
		let high = raw[1] as u64;
		let low = raw[0] as u64;
		let value = ((high << 32) | low).to_ne_bytes();
		TrailEvent::IntAssignment { index, value }
	}

	#[inline]
	/// Internal method to write a [`TailEvent`] in reverse order to `trail` so
	/// it can be redone later.
	fn write_rev_trail(&self, trail: &mut [u32]) {
		match self {
			TrailEvent::SatAssignment(var) => trail[0] = i32::from(*var) as u32,
			TrailEvent::IntAssignment { index, value } => {
				let val = u64::from_ne_bytes(*value);
				let high = (val >> 32) as u32;
				let low = val as u32;
				trail[0] = -(*index as i32) as u32;
				trail[1] = high;
				trail[2] = low;
			}
		}
	}

	#[inline]
	/// Internal method to write a [`TailEvent`] to the slice `trail` using an
	/// efficient format.
	fn write_trail(&self, trail: &mut [u32]) {
		match self {
			TrailEvent::SatAssignment(var) => trail[0] = i32::from(*var) as u32,
			TrailEvent::IntAssignment { index, value } => {
				let val = u64::from_ne_bytes(*value);
				let high = (val >> 32) as u32;
				let low = val as u32;
				trail[0] = low;
				trail[1] = high;
				trail[2] = -(*index as i32) as u32;
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::{ClauseDatabase, solver::cadical::Cadical};

	use crate::{
		IntVal,
		actions::TrailingActions,
		helpers::bytes::Bytes,
		solver::trail::{Trail, TrailEvent},
	};

	#[test]
	fn test_trail_event() {
		let mut slv = Cadical::default();
		let mut trail = Trail::default();
		let lits = slv.new_var_range(10);
		trail.grow_to_boolvar(lits.end());
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
		.map(|i| (trail.track(0), i))
		.collect();

		for (l, &(i, v)) in lits.zip(int_events.iter()) {
			trail.assign_lit(if i.index % 2 == 0 { l.into() } else { !l });
			trail.set_trailed(i, v);
		}

		for (l, &(i, v)) in lits.rev().zip(int_events.iter().rev()) {
			assert_eq!(trail.trailed(i), v);
			if v != 0 {
				let e = trail.undo::<true>().unwrap();
				let TrailEvent::IntAssignment { index, value } = e else {
					panic!("unexpected trail event type {e:?}");
				};
				assert_eq!(i.index, index);
				assert_eq!(trail.trailed(i), i64::from_bytes(value));
			}

			assert_eq!(trail.sat_value(l), Some(i.index % 2 == 0));
			let e = trail.undo::<true>().unwrap();
			assert_eq!(e, TrailEvent::SatAssignment(l));
			assert_eq!(trail.sat_value(l), None);
		}
	}
}
