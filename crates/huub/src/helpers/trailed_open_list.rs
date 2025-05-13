use crate::{
	actions::{PropagatorInitActions, TrailingActions},
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list which allows iterating only open elements with backtracking of the open 
/// state.
pub(crate) struct TrailedOpenList<T> {
	list: Vec<T>,
	closed: TrailedInt,
}

impl<T> TrailedOpenList<T> {
	pub(crate) fn iter<A: TrailingActions>(&mut self, actions: &A) -> TrailedOpenListIterator<T> {
		let start = actions.get_trailed_int(self.closed) as usize;
		TrailedOpenListIterator {
			list: self,
			index: start,
		}
	}

	pub(crate) fn close<A, F>(&mut self, actions: &mut A, index: usize, mut idx_update: F) -> bool
	where A: TrailingActions, F: FnMut(&T, usize) {
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
	
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}
	
	pub(crate) fn open_len<A: TrailingActions>(&self, actions: &A) -> usize {
		self.len() - actions.get_trailed_int(self.closed) as usize
	}

	pub(crate) fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			list: Vec::new(),
			closed: actions.new_trailed_int(0),
		}
	}

	pub(crate) fn from<A: PropagatorInitActions + ?Sized>(actions: &mut A, list: Vec<T>) -> Self {
		Self {
			list,
			closed: actions.new_trailed_int(0),
		}
	}

	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}

pub(crate) struct TrailedOpenListIterator<'a, T> {
	list: &'a mut TrailedOpenList<T>,
	index: usize,
}

impl<T> TrailedOpenListIterator<'_, T> {

	pub(crate) fn next(&mut self) -> Option<&T> {
		if self.index >= self.list.len() {
			return None;
		}
		self.index += 1;
		Some(&self.list.list[self.index - 1])
	}

	pub(crate) fn close<A, F>(&mut self, actions: &mut A, idx_update: F) -> bool
	where A: TrailingActions, F: FnMut(&T, usize) {
		self.list.close(actions, self.index - 1, idx_update)
	}

}