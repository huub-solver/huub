//! To-do list that allows to iterate open elements and trails their open
//! status.

use std::ops::Range;

use crate::actions::{ConstructionActions, TrailAccessActions, Trailed, TrailingActions};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// A list which allows iterating only open elements with backtracking of the
/// open state. New elements can be added to the end of the list in open status.
pub(crate) struct TrailedOpenList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the closed part of the list.
	closed: Trailed<usize>,
}

impl<T: Clone> TrailedOpenList<T> {
	/// Create a new empty list.
	pub(crate) fn new<A: ConstructionActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			list: Vec::new(),
			closed: actions.new_trailed(0),
		}
	}

	/// Return the element at the given index, fail if it is in the closed
	/// section.
	pub(crate) fn index<A: TrailAccessActions + ?Sized>(&self, actions: &A, index: usize) -> &T {
		let closed = actions.trailed(self.closed);
		assert!(index >= closed, "index out of bounds");
		&self.list[index]
	}

	/// Return the element at the given index, or None if already closed.
	pub(crate) fn index_opt<A: TrailAccessActions>(&self, actions: &A, index: usize) -> Option<&T> {
		let closed = actions.trailed(self.closed);
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
		let cur = actions.trailed(self.closed);
		if index < cur {
			return false;
		}
		if index > cur {
			self.list.swap(index, cur);
			idx_update(&self.list[cur], cur);
			idx_update(&self.list[index], index);
		}
		let _ = actions.set_trailed(self.closed, cur + 1);
		true
	}

	/// Close all elements in the list.
	pub(crate) fn clear<A: TrailingActions>(&mut self, actions: &mut A) {
		let _ = actions.set_trailed(self.closed, self.len());
	}

	/// Return the total length of the list (including elements closed in
	/// trailing state).
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}

	/// Return the number of open elements in the list.
	pub(crate) fn num_open<A: TrailAccessActions>(&self, actions: &A) -> usize {
		self.list.len() - actions.trailed(self.closed)
	}

	/// Check if the list is empty (contains no open elements).
	pub(crate) fn is_empty<A: TrailAccessActions>(&self, actions: &A) -> bool {
		self.list.len() == actions.trailed(self.closed)
	}

	/// Return the number of open elements in the list.
	pub(crate) fn open_iter<A: TrailAccessActions + ?Sized>(&self, actions: &A) -> Range<usize> {
		actions.trailed(self.closed)..self.len()
	}

	/// Add a new open element to the list.
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}
