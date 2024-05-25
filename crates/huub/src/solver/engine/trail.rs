use std::{collections::HashMap, mem, ops::Index};

use index_vec::{Idx, IndexVec};
use pindakaas::{Lit as RawLit, Var as RawVar};

use crate::{actions::trailing::TrailingActions, solver::engine::TrailedInt, IntVal};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Trail<I: Idx, E> {
	value: IndexVec<I, E>,
	trail: Vec<(I, E)>,
	prev_len: Vec<usize>,
}

impl<I: Idx, E> Default for Trail<I, E> {
	fn default() -> Self {
		Self {
			value: IndexVec::new(),
			trail: Vec::new(),
			prev_len: Vec::new(),
		}
	}
}

impl<I: Idx, E> Trail<I, E> {
	pub(crate) fn track(&mut self, val: E) -> I {
		self.value.push(val)
	}

	pub(crate) fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len())
	}

	pub(crate) fn notify_backtrack(&mut self, level: usize) {
		self.prev_len.truncate(level + 1);
		let len = self.prev_len.pop().unwrap_or(0);
		for (i, val) in self.trail.drain(len..).rev() {
			self.value[i] = val;
		}
	}

	pub(crate) fn decision_level(&self) -> usize {
		self.prev_len.len()
	}
}

impl<I: Idx, E: PartialEq> Trail<I, E> {
	pub(crate) fn assign(&mut self, i: I, val: E) -> HasChanged {
		if self.value[i] == val {
			return HasChanged::NoChange;
		}
		let old = mem::replace(&mut self.value[i], val);
		if !self.prev_len.is_empty() {
			self.trail.push((i, old));
		}
		HasChanged::Changed
	}
}

impl<I: Idx, E> Index<I> for Trail<I, E> {
	type Output = E;

	fn index(&self, index: I) -> &Self::Output {
		self.value.index(index)
	}
}

impl TrailingActions for Trail<TrailedInt, IntVal> {
	fn get_trailed_int(&self, x: TrailedInt) -> IntVal {
		self[x]
	}
	fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) {
		let _ = self.assign(x, v);
	}
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct SatTrail {
	value: HashMap<RawVar, bool>,
	trail: Vec<RawVar>,
	prev_len: Vec<usize>,
}

impl SatTrail {
	pub(crate) fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len())
	}

	pub(crate) fn notify_backtrack(&mut self, level: usize) {
		self.prev_len.truncate(level + 1);
		let len = self.prev_len.pop().unwrap_or(0);
		for v in self.trail.drain(len..).rev() {
			let _ = self.value.remove(&v);
		}
	}

	pub(crate) fn assign(&mut self, var: RawVar, val: bool) -> HasChanged {
		if self.value.insert(var, val).is_some() {
			// Variable was updated with a new value
			// This might be a new (inconsistent) value if the SAT solver is still propagating given
			// literals.
			return HasChanged::NoChange;
		}
		if !self.prev_len.is_empty() {
			self.trail.push(var);
		}
		HasChanged::Changed
	}

	pub(crate) fn get<L: Into<RawLit>>(&self, lit: L) -> Option<bool> {
		let lit = lit.into();
		self.value
			.get(&lit.var())
			.copied()
			.map(|x| if lit.is_negated() { !x } else { x })
	}

	pub(crate) fn decision_level(&self) -> usize {
		self.prev_len.len()
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HasChanged {
	Changed,
	NoChange,
}
