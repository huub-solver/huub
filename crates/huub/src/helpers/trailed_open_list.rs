//! Append-only list that allows to iterate open elements and trails their open status.

use std::ops::Range;

use crate::{
	actions::{ConstructionActions, TrailingActions},
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list which allows iterating only open elements with
/// backtracking of the open state.
pub(crate) struct TrailedOpenList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the closed part of the list.
	closed: TrailedInt,
}

impl<T: Clone> TrailedOpenList<T> {
	/// Create a new empty list.
	pub(crate) fn new<A: ConstructionActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			list: Vec::new(),
			closed: actions.new_trailed_int(0),
		}
	}

	/// Return the first open element.
	pub(crate) fn peek<A: TrailingActions>(&self, actions: &A) -> Option<&T> {
		let cur = actions.trailed_int(self.closed) as usize;
		if cur >= self.list.len() {
			return None;
		}
		Some(&self.list[cur])
	}

	/// Return the first open element and close it.
	pub(crate) fn pop<A: TrailingActions>(&mut self, actions: &mut A) -> Option<&T> {
		let cur = actions.trailed_int(self.closed) as usize;
		if cur >= self.list.len() {
			return None;
		}
		let _ = self.close(actions, cur, |_, _| {});
		Some(&self.list[cur])
	}

	/// Return the element at the given index, fail if it is in the closed
	/// section.
	pub(crate) fn index<A: TrailingActions + ?Sized>(&self, actions: &A, index: usize) -> &T {
		let closed = actions.trailed_int(self.closed) as usize;
		assert!(index >= closed, "index out of bounds");
		&self.list[index]
	}

	/// Return the element at the given index, or None if already closed.
	pub(crate) fn index_opt<A: TrailingActions>(&self, actions: &A, index: usize) -> Option<&T> {
		let closed = actions.trailed_int(self.closed) as usize;
		if index >= closed {
			Some(&self.list[index])
		} else {
			None
		}
	}

	/// Close an element. This moves the closed elements to the start of the
	/// list to allow further addition of elements at the end. Note that the
	/// order of elements is not preserved.
	pub(crate) fn close<A, F>(&mut self, actions: &mut A, index: usize, mut idx_update: F) -> bool
	where
		A: TrailingActions,
		F: FnMut(&T, usize),
	{
		let cur = actions.trailed_int(self.closed) as usize;
		if index < cur {
			return false;
		}
		if index > cur {
			self.list.swap(index, cur);
			idx_update(&self.list[cur], cur);
			idx_update(&self.list[index], index);
		}
		let _ = actions.set_trailed_int(self.closed, cur as IntVal + 1);
		true
	}

	/// Return the total length of the list (including elements closed in
	/// trailing state).
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}

	/// Return the number of open elements in the list.
	pub(crate) fn num_open<A: TrailingActions>(&self, actions: &A) -> usize {
		self.list.len() - actions.trailed_int(self.closed) as usize
	}

	/// Return the number of open elements in the list.
	pub(crate) fn open_iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Range<usize> {
		actions.trailed_int(self.closed) as usize..self.len()
	}

	/// Add a new element to the list.
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}
