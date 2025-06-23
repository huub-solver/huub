use std::slice::Iter;

use crate::{
	actions::TrailingActions,
	helpers::initial_trail::InitialTrail,
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list from which elements are automatically removed when
/// the solver backtracks. Removals are only possible before trailing is initialized.
pub(crate) struct TrailedList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the active part of the list.
	size: TrailedInt,
	/// Whether the list is already trailed or not.
	is_trailed: bool,
}

impl<T> TrailedList<T> {

	pub(crate) fn new(initial_trail: &mut InitialTrail) -> Self {
		Self {
			list: Vec::new(),
			size: initial_trail.new_trailed_int(0),
			is_trailed: false,
		}
	}

	/// Initialize the trailed infrastructure for this list.
	pub(crate) fn init_trail(&mut self, initial_trail: &mut InitialTrail) {
		self.list.truncate(initial_trail.get_trailed_int(self.size) as usize);
		self.size = initial_trail.map_to_trail(self.size);
		self.is_trailed = true;
	}

	/// Remove the trailed infrastructure for this list, only possible if not initialized.
	pub(crate) fn remove_trail(&mut self, initial_trail: &mut InitialTrail) {
		assert!(!self.is_trailed, "removal is only allowed before trailing");
		initial_trail.remove(self.size);
	}

	/// Return an iterator over the active elements of the list.
	pub(crate) fn iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Iter<'_, T> {
		let len = self.len(actions);
		self.list[..len].iter()
	}
	
	/// Return the index at the given position.
	pub(crate) fn index<A: TrailingActions + ?Sized>(&self, actions: &A, index: usize) -> &T {
		let len = self.len(actions);
		assert!(index < len, "index out of bounds");
		&self.list[index]
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
	
	/// Remove the element at the given index by swapping it out of the active range. 
	/// Can only be called before trailing is initialized.
	pub(crate) fn swap_remove<A: TrailingActions + ?Sized>(&mut self, actions: &mut A, index: usize) -> &T {
		assert!(!self.is_trailed, "removal is only allowed before trailing");
		let len = self.len(actions);
		assert!(index < len, "index {index} out of bounds {len}");
		self.list.swap(index, len - 1);
		let _ = actions.set_trailed_int(self.size, len as IntVal - 1);
		&self.list[len - 1]
	}

}
