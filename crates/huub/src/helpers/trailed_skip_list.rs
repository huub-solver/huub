use crate::{
	actions::{PropagatorInitActions, TrailingActions},
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A list of fixed length where elements are skipped when handled and restored when
/// the solver backtracks.
pub(crate) struct TrailedSkipList<T> {
	list: Vec<T>,
	next: Vec<TrailedInt>,
}

impl<T> TrailedSkipList<T> {

	pub(crate) fn iter<A: TrailingActions>(&self) -> TrailedSkipListIterator<T> {
		TrailedSkipListIterator {
			list: self,
			index: 0,
			list_index: -1,
		}
	}

	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}

	pub(crate) fn from<A: PropagatorInitActions + ?Sized>(elements: Vec<T>, actions: &mut A) -> Self {
		let next = (0..=elements.len()).into_iter().map(|i| actions.new_trailed_int(i as IntVal)).collect();
		Self {
			list: elements,
			next,
		}
	}

}

pub(crate) struct TrailedSkipListIterator<'a,T> {
	list: &'a TrailedSkipList<T>,
	index: usize,
	list_index: IntVal,
}

impl<'a,T> TrailedSkipListIterator<'a,T> {

	pub(crate) fn next<A: TrailingActions>(&mut self, actions: &A) -> Option<&T> {
		self.index = (self.list_index + 1) as usize;
		self.list_index = actions.get_trailed_int(self.list.next[self.index]);
		if self.list_index as usize >= self.list.len() {
			return None;
		}
		Some(&self.list.list[self.list_index as usize])
	}
	
	pub(crate) fn remove<A: TrailingActions>(&self, actions: &mut A) {
		let _ = actions.set_trailed_int(self.list.next[self.index], actions.get_trailed_int(self.list.next[(self.list_index + 1) as usize]));
	}
	
}
