//! Minimum priority queue whose priorities can be lowered after insertion.

use std::{cmp::Reverse, collections::BinaryHeap, hash::Hash};

use rustc_hash::FxHashMap;

use crate::DeepClone;

/// A minimum priority queue that supports lowering the priority of an item that
/// is already queued.
///
/// Lowering a priority pushes a second entry for the same item rather than
/// repairing the heap in place. The superseded entry is left behind as *stale*
/// and is recognised and dropped when it surfaces in [`Self::pop`], by
/// comparing it against the item's current priority. Shortest-path search
/// lowers priorities far more often than it pops, so paying an extra heap push
/// to avoid a decrease-key implementation is the cheaper trade in practice (see
/// §"Difference Logic Representation" of the difference logic paper).
///
/// Because stale entries are only discarded on [`Self::pop`], the heap can hold
/// more entries than there are queued items; [`Self::contains`] therefore
/// answers from the priority map, never the heap.
#[derive(Clone, Debug, DeepClone)]
#[deepclone(bound = "I: DeepClone + Eq + Hash + Ord, P: DeepClone + Ord")]
pub(crate) struct LazyPriorityQueue<I, P> {
	/// Heap of `(priority, item)` pairs, ordered so the *lowest* priority is
	/// popped first. Contains at least one entry per queued item, plus any
	/// stale entries superseded by [`Self::push_decrease`].
	heap: BinaryHeap<Reverse<(P, I)>>,
	/// The current priority of each queued item. An entry in `heap` whose
	/// priority differs from the one recorded here is stale.
	current: FxHashMap<I, P>,
}

impl<I, P> LazyPriorityQueue<I, P>
where
	I: Clone + Eq + Hash + Ord,
	P: Clone + Ord,
{
	/// Remove all items, keeping the allocated capacity so the queue can be
	/// reused for the next search without reallocating.
	pub(crate) fn clear(&mut self) {
		self.heap.clear();
		self.current.clear();
	}

	/// Whether the given item is currently queued.
	pub(crate) fn contains(&self, item: &I) -> bool {
		self.current.contains_key(item)
	}

	/// Remove the queued item with the lowest priority, dropping any stale
	/// entries encountered on the way.
	pub(crate) fn pop(&mut self) -> Option<(I, P)> {
		while let Some(Reverse((priority, item))) = self.heap.pop() {
			// Any entry that does not match the item's current priority was
			// superseded by `push`/`push_decrease` and must be skipped.
			if self.current.get(&item) == Some(&priority) {
				let _ = self.current.remove(&item);
				return Some((item, priority));
			}
		}
		None
	}

	/// Queue the item at the given priority, superseding its current priority
	/// if it is already queued. Returns the priority it replaced, if any.
	pub(crate) fn push(&mut self, item: I, priority: P) -> Option<P> {
		self.heap.push(Reverse((priority.clone(), item.clone())));
		self.current.insert(item, priority)
	}

	/// Queue the item at the given priority if it is not queued yet, or lower
	/// its priority to the given one if that is an improvement. Returns whether
	/// the queue was changed.
	pub(crate) fn push_decrease(&mut self, item: I, priority: P) -> bool {
		if self
			.current
			.get(&item)
			.is_none_or(|current| priority < *current)
		{
			let _ = self.push(item, priority);
			true
		} else {
			false
		}
	}
}

impl<I, P> Default for LazyPriorityQueue<I, P> {
	fn default() -> Self {
		Self {
			heap: BinaryHeap::new(),
			current: FxHashMap::default(),
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::priority_queue::LazyPriorityQueue;

	#[test]
	fn test_priority_queue_clear_keeps_reusable() {
		let mut queue = LazyPriorityQueue::default();
		let _ = queue.push('a', 1);
		let _ = queue.push_decrease('a', 0);
		queue.clear();

		assert!(!queue.contains(&'a'));
		assert_eq!(queue.pop(), None);

		// The stale entry left by the superseded priority must not resurface.
		let _ = queue.push('b', 5);
		assert_eq!(queue.pop(), Some(('b', 5)));
		assert_eq!(queue.pop(), None);
	}

	#[test]
	fn test_priority_queue_pop_order() {
		let mut queue = LazyPriorityQueue::default();
		for (item, priority) in [('a', 3), ('b', 1), ('c', 2)] {
			assert_eq!(queue.push(item, priority), None);
		}

		assert_eq!(queue.pop(), Some(('b', 1)));
		assert_eq!(queue.pop(), Some(('c', 2)));
		assert_eq!(queue.pop(), Some(('a', 3)));
		assert_eq!(queue.pop(), None);
	}

	#[test]
	fn test_priority_queue_pop_removes_item() {
		let mut queue = LazyPriorityQueue::default();
		let _ = queue.push('a', 1);
		assert!(queue.contains(&'a'));

		assert_eq!(queue.pop(), Some(('a', 1)));
		// A popped item is no longer queued, even though it was never
		// explicitly removed.
		assert!(!queue.contains(&'a'));
	}

	#[test]
	fn test_priority_queue_push_decrease() {
		let mut queue = LazyPriorityQueue::default();

		assert!(queue.push_decrease('a', 5));
		// An equal priority is not an improvement, so nothing changes.
		assert!(!queue.push_decrease('a', 5));
		assert!(!queue.push_decrease('a', 7));
		assert!(queue.push_decrease('a', 2));

		assert_eq!(queue.pop(), Some(('a', 2)));
		// The three superseded entries for `a` are stale and dropped.
		assert_eq!(queue.pop(), None);
	}

	#[test]
	fn test_priority_queue_push_replaces_priority() {
		let mut queue = LazyPriorityQueue::default();
		assert_eq!(queue.push('a', 1), None);
		// Unlike `push_decrease`, `push` also accepts a worse priority.
		assert_eq!(queue.push('a', 4), Some(1));
		let _ = queue.push('b', 2);

		assert_eq!(queue.pop(), Some(('b', 2)));
		assert_eq!(queue.pop(), Some(('a', 4)));
		assert_eq!(queue.pop(), None);
	}
}
