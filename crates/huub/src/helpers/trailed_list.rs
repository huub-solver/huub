//! Append-only list that trails element additions.

use std::slice::Iter;

use crate::actions::{ConstructionActions, TrailAccessActions, Trailed, TrailingActions};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// An **append only** list from which newly added elements are automatically
/// removed when the solver backtracks. Other removals can't be reverted.
pub(crate) struct TrailedList<T> {
	/// Underlying list.
	list: Vec<T>,
	/// Length of the active part of the list.
	size: Trailed<usize>,
	/// Whether removals are allowed (these can't be reverted).
	allow_removal: bool,
}

impl<T: PartialEq + Clone> TrailedList<T> {
	/// Create a new empty list.
	pub(crate) fn new<A: ConstructionActions + ?Sized>(
		actions: &mut A,
		allow_removal: bool,
	) -> Self {
		Self {
			list: Vec::new(),
			size: actions.new_trailed(0),
			allow_removal,
		}
	}

	/// Return an iterator over the active elements of the list.
	pub(crate) fn iter<A: TrailAccessActions + ?Sized>(&self, actions: &A) -> Iter<'_, T> {
		let len = self.len(actions);
		self.list[..len].iter()
	}

	/// Return the index at the given position.
	pub(crate) fn index<A: TrailAccessActions>(&self, actions: &A, index: usize) -> &T {
		let len = self.len(actions);
		assert!(index < len, "index out of bounds");
		&self.list[index]
	}

	/// Return the length of the active elements in the list.
	pub(crate) fn len<A: TrailAccessActions + ?Sized>(&self, actions: &A) -> usize {
		actions.trailed(self.size)
	}

	/// Check if the list is empty (contains no active elements).
	pub(crate) fn is_empty<A: TrailAccessActions + ?Sized>(&self, actions: &A) -> bool {
		actions.trailed(self.size) == 0
	}

	/// Add an element to the active list.
	pub(crate) fn push<A: TrailingActions + ?Sized>(&mut self, actions: &mut A, value: T) {
		let len = self.len(actions);
		if len < self.list.len() {
			self.list[len] = value;
		} else {
			self.list.push(value);
		}
		let prev = actions.set_trailed(self.size, len + 1);
		debug_assert_eq!(prev, len);
	}

	/// Remove all elements from the list (can't be reverted, only if removal is
	/// allowed).
	pub(crate) fn clear<A: TrailingActions + ?Sized>(&self, actions: &mut A) {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let _ = actions.set_trailed(self.size, 0);
	}

	/// Remove the given element by swapping it out of the active range (can't
	/// be reverted, only if removal is allowed).
	pub(crate) fn swap_remove_element<A: TrailingActions>(
		&mut self,
		actions: &mut A,
		element: &T,
	) -> &T {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let len = self.len(actions);
		let index = self
			.list
			.iter()
			.take(len)
			.position(|x| *x == *element)
			.unwrap();
		self.swap_remove(actions, index)
	}

	/// Remove the element at the given index by swapping it out of the active
	/// range (can't be reverted, only if removal is allowed).
	pub(crate) fn swap_remove<A: TrailingActions>(&mut self, actions: &mut A, index: usize) -> &T {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let len = self.len(actions);
		assert!(index < len, "index {index} out of bounds {len}");
		self.list.swap(index, len - 1);
		let _ = actions.set_trailed(self.size, len - 1);
		&self.list[len - 1]
	}
}
