use crate::{
	actions::TrailingActions,
	solver::trail::TrailedInt,
	IntVal,
};
use crate::helpers::initial_trail::InitialTrail;

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
	pub(crate) fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		self.closed = initial_trail.map_to_trail(self.closed);
		self.is_trailed = true;
	}
	
	/// Return an iterator over the open elements of the list.
	pub(crate) fn iter<A: TrailingActions + ?Sized>(&mut self, actions: &A) -> TrailedOpenListIterator<T> {
		let start = if self.is_trailed {
			actions.get_trailed_int(self.closed) as usize
		} else {0};
		TrailedOpenListIterator {
			list: self,
			index: start,
		}
	}

	/// Close an element. Before trailing is initialized, this actually removes the element from the 
	/// list. Once trailing is enabled, it moves the closed elements to the start of the list to 
	/// allow further addition of elements at the end. Note that the order of elements is never 
	/// preserved.
	pub(crate) fn close<A, F>(&mut self, actions: &mut A, index: usize, mut idx_update: F) -> bool
	where A: TrailingActions + ?Sized, F: FnMut(&T, usize) {
		if self.is_trailed {
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
		} else {
			let cur = self.list.len() - 1;
			if index > cur {
				return false;
			}
			if index < cur {
				self.list.swap(index, cur);
				idx_update(&self.list[cur], cur);
				idx_update(&self.list[index], index);
			}
			let _ = self.list.remove(cur);
			true
		}
	}
	
	/// Return the total length of the list (including elements closed in trailing state).
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}
	
	/// Return the length of the open list.
	pub(crate) fn open_len<A: TrailingActions + ?Sized>(&self, actions: &A) -> usize {
		if self.is_trailed {
			self.list.len() - actions.get_trailed_int(self.closed) as usize
		} else {
			self.list.len()
		}
	}

	/// Add a new element to the list.
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}

/// An iterator over the open part of the [TrailedOpenList] which allows to close elements while 
/// iterating.
pub(crate) struct TrailedOpenListIterator<'a, T> {
	list: &'a mut TrailedOpenList<T>,
	index: usize,
}

impl<T> TrailedOpenListIterator<'_, T> {  // TODO implement actual Iterator trait (lifetimes...)

	pub(crate) fn next(&mut self) -> Option<&T> {
		if self.index >= self.list.len() {
			return None;
		}
		self.index += 1;
		Some(&self.list.list[self.index - 1])
	}

	/// Close the element returned by the last call to [TrailedOpenListIterator::next].
	pub(crate) fn close<A, F>(&mut self, actions: &mut A, idx_update: F) -> bool
	where A: TrailingActions + ?Sized, F: FnMut(&T, usize) {
		self.list.close(actions, self.index - 1, idx_update)
	}

}