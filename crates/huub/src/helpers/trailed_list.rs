use std::slice::Iter;

use crate::{
	actions::TrailingActions,
	helpers::initial_trail::InitialTrail,
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list from which elements are automatically removed when
/// the solver backtracks.
pub(crate) struct TrailedList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the active part of the list.
	size: TrailedInt,
}

impl<T> TrailedList<T> {

	pub(crate) fn new(initial_trail: &mut InitialTrail) -> Self {
		Self {
			list: Vec::new(),
			size: initial_trail.new_trailed_int(0),
		}
	}

	/// Initialize the trailed infrastructure for this list.
	pub(crate) fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		self.list.truncate(initial_trail.get_trailed_int(self.size) as usize);
		self.size = initial_trail.map_to_trail(self.size);
	}

	/// Return an iterator over the active elements of the list.
	pub(crate) fn iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Iter<'_, T> {
		let len = self.len(actions);
		self.list[..len].iter()
	}

	/// Return the length of the active elements in the list.
	pub(crate) fn len<A: TrailingActions + ?Sized>(&self, actions: &A) -> usize {
		actions.get_trailed_int(self.size) as usize
	}

	/// Add an element to the active list.
	pub(crate) fn push<A: TrailingActions + ?Sized>(&mut self, actions: &mut A, value: T) {
		let len = self.len(actions);
		if len < self.list.len() {
			self.list[len] = value;
		} else {
			self.list.push(value);
		}
		let prev = actions.set_trailed_int(self.size, len as IntVal + 1);
		debug_assert_eq!(prev, len as IntVal);
	}

}
