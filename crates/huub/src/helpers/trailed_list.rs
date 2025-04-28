use std::slice::Iter;

use crate::{
	actions::{PropagatorInitActions, TrailingActions},
	solver::trail::TrailedInt,
	IntVal,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// A **append only** list from which elements are automatically removed when
/// the solver backtracks.
pub(crate) struct TrailedList<T> {
	list: Vec<T>,
	size: TrailedInt,
}

impl<T> TrailedList<T> {
	pub(crate) fn as_slice<A: TrailingActions>(&self, actions: &A) -> &[T] {
		let len = self.len(actions);
		&self.list[..len]
	}

	pub(crate) fn iter<A: TrailingActions>(&self, actions: &A) -> Iter<'_, T> {
		let len = self.len(actions);
		self.list[..len].iter()
	}

	pub(crate) fn len<A: TrailingActions>(&self, actions: &A) -> usize {
		actions.get_trailed_int(self.size) as usize
	}

	pub(crate) fn new<A: PropagatorInitActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			list: Vec::new(),
			size: actions.new_trailed_int(0),
		}
	}

	pub(crate) fn push<A: TrailingActions>(&mut self, actions: &mut A, value: T) {
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
