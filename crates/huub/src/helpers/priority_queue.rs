//! Priority queue allowing lazy priority changes.

use std::{collections::BinaryHeap, hash::Hash};

use rustc_hash::FxHashMap;

/// A priority queue that allows overwriting priority. Stale entries are kept in
/// the queue and silently dropped during pop operations only.
pub(crate) struct LazyPriorityQueue<I, P> {
	/// Heap storing (priority, item) pairs.
	heap: BinaryHeap<(P, I)>,
	/// Map storing the current priority for each item.
	current: FxHashMap<I, P>,
}

impl<I, P> LazyPriorityQueue<I, P>
where
	I: Ord + Hash + Clone,
	P: Ord + Clone,
{
	/// Create a new empty queue.
	pub(crate) fn new() -> Self {
		Self {
			heap: BinaryHeap::new(),
			current: FxHashMap::default(),
		}
	}

	/// Insert the given item with the given priority, causing previous entries
	/// for the same item to become stale. The previous priority is returned if
	/// it exists.
	pub(crate) fn push(&mut self, item: I, priority: P) -> Option<P> {
		self.heap.push((priority.clone(), item.clone()));
		self.current.insert(item, priority)
	}

	/// Insert the given item with the new priority if not present or currently
	/// present with a lower priority, causing previous entries for the same
	/// item to become stale. The previous priority is returned if the item is
	/// new or the priority was updated, otherwise the new priority argument is
	/// returned.
	pub(crate) fn push_increase(&mut self, item: I, priority: P) -> Option<P> {
		if self
			.current
			.get(&item)
			.is_none_or(|old_prio| priority > *old_prio)
		{
			return self.push(item, priority);
		}
		Some(priority)
	}

	/// Pop the next item that is not stale (if any exist), dropping all stale
	/// items with lower order.
	pub(crate) fn pop(&mut self) -> Option<(I, P)> {
		while let Some((priority, item)) = self.heap.pop() {
			// Only return entry if the queue priority matches the current one
			if self.current.get(&item) == Some(&priority) {
				self.current.remove(&item);
				return Some((item, priority));
			}
		}
		None
	}

	/// Return true if the queue is empty.
	pub(crate) fn is_empty(&self) -> bool {
		self.current.is_empty()
	}

	/// Return the priority of the given item (if it exists).
	pub(crate) fn get_priority(&self, item: &I) -> Option<P> {
		self.current.get(item).cloned()
	}
}
