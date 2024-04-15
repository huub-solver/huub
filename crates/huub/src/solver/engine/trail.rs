use std::{collections::HashMap, mem, ops::Index};

use index_vec::{Idx, IndexVec};
use pindakaas::Var as RawVar;

#[derive(Debug)]
pub struct Trail<I: Idx, E> {
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
	pub fn track(&mut self, val: E) -> I {
		self.value.push(val)
	}

	pub fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len())
	}

	pub fn notify_backtrack(&mut self, level: usize) {
		self.prev_len.truncate(level);
		let len = self.prev_len.pop().unwrap_or(0);
		for (i, val) in self.trail.drain(len..).rev() {
			self.value[i] = val;
		}
	}
}

impl<I: Idx, E: PartialEq> Trail<I, E> {
	pub fn assign(&mut self, i: I, val: E) {
		if self.value[i] == val {
			return;
		}
		let old = mem::replace(&mut self.value[i], val);
		if !self.prev_len.is_empty() {
			self.trail.push((i, old));
		}
	}
}

impl<I: Idx, E> Index<I> for Trail<I, E> {
	type Output = E;

	fn index(&self, index: I) -> &Self::Output {
		self.value.index(index)
	}
}

#[derive(Debug, Default)]
pub struct SatTrail {
	value: HashMap<RawVar, bool>,
	trail: Vec<RawVar>,
	prev_len: Vec<usize>,
}

impl SatTrail {
	pub fn notify_new_decision_level(&mut self) {
		self.prev_len.push(self.trail.len())
	}

	pub fn notify_backtrack(&mut self, level: usize) {
		self.prev_len.truncate(level);
		let len = self.prev_len.pop().unwrap_or(0);
		for v in self.trail.drain(len..).rev() {
			self.value.remove(&v);
		}
	}

	pub fn assign(&mut self, var: RawVar, val: bool) {
		if self.value.get(&var) == Some(&val) {
			return;
		}
		self.value.insert(var, val);
		if !self.prev_len.is_empty() {
			self.trail.push(var);
		}
	}

	pub fn get(&self, var: RawVar) -> Option<bool> {
		self.value.get(&var).copied()
	}
}
