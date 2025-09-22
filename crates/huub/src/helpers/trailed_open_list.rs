use crate::helpers::initial_trail::InitialTrail;
use crate::{
	actions::TrailingActions,
	solver::trail::TrailedInt,
	IntVal,
};
use std::ops::Range;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list which allows iterating only open elements with backtracking of the open 
/// state.
pub(crate) struct TrailedOpenList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the closed part of the list.
	closed: TrailedInt,
	/// Whether the list is already trailed or not.
	is_trailed: bool,
}

impl<T> TrailedOpenList<T> {
	
	pub(crate) fn new(initial_trail: &mut InitialTrail) -> Self {
		Self {
			list: Vec::new(),
			closed: initial_trail.new_trailed_int(0),
			is_trailed: false,
		}
	}

	/// Initialize the trailed infrastructure for this list.
	pub(crate) fn init_trail(&mut self, initial_trail: &mut InitialTrail) {  // TODO removed closed elements from list here, needs write access to the trail at this stage!
		self.closed = initial_trail.map_to_trail(self.closed);
		self.is_trailed = true;
	}

	/// Remove the trailed infrastructure for this list, only possible if not initialized.
	pub(crate) fn remove_trail(&mut self, initial_trail: &mut InitialTrail) {
		assert!(!self.is_trailed, "removal is only allowed before trailing");
		initial_trail.remove(self.closed);
	}

	/// Return the first open element.
	pub(crate) fn peek<A: TrailingActions + ?Sized>(&self, actions: &A) -> Option<&T> {
		let cur = actions.get_trailed_int(self.closed) as usize;
		if cur >= self.list.len() {
			return None;
		}
		Some(&self.list[cur])
	}

	/// Return the first open element and close it.
	pub(crate) fn pop<A: TrailingActions + ?Sized>(&mut self, actions: &mut A) -> Option<&T> {
		let cur = actions.get_trailed_int(self.closed) as usize;
		if cur >= self.list.len() {
			return None;
		}
		let _ = self.close(actions, cur, |_, _| {});
		Some(&self.list[cur])
	}

	/// Return the element at the given index, fail if it is in the closed section.
	pub(crate) fn index<A: TrailingActions + ?Sized>(&self, actions: &A, index: usize) -> &T {
		let closed = actions.get_trailed_int(self.closed) as usize;
		assert!(index >= closed, "index out of bounds");
		&self.list[index]
	}

	/// Return the element at the given index, or None if already closed.
	pub(crate) fn index_opt<A: TrailingActions + ?Sized>(&self, actions: &A, index: usize) -> Option<&T> {
		let closed = actions.get_trailed_int(self.closed) as usize;
		if index >= closed {
			Some(&self.list[index])
		} else {
			None
		}
	}

	/// Close an element. This moves the closed elements to the start of the list to
	/// allow further addition of elements at the end. Note that the order of elements is not
	/// preserved.
	pub(crate) fn close<A, F>(&mut self, actions: &mut A, index: usize, mut idx_update: F) -> bool
	where A: TrailingActions + ?Sized, F: FnMut(&T, usize) {
		let cur = actions.get_trailed_int(self.closed) as usize;
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
	
	/// Return the total length of the list (including elements closed in trailing state).
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}

	/// Return the number of open elements in the list.
	pub(crate) fn num_open<A: TrailingActions + ?Sized>(&self, actions: &A) -> usize {
		self.list.len() - actions.get_trailed_int(self.closed) as usize
	}

	/// Return the number of open elements in the list.
	pub(crate) fn open_iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Range<usize> {
		actions.get_trailed_int(self.closed) as usize..self.len()
	}

	/// Add a new element to the list.
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}
