//! A priority queue that supports lazy priority changes.
//!
//! The implementation keeps stale entries in the underlying binary heap and
//! silently drops them during `pop`. This trades some extra memory for an
//! amortised O(log n) `push`/`push_increase`, which is the right shape for
//! shortest-path-style algorithms where the same item is repeatedly updated
//! with tighter priorities before it is eventually popped.

use std::{collections::BinaryHeap, hash::Hash};

use rustc_hash::FxHashMap;

/// A priority queue that allows overwriting an item's priority.
///
/// Stale entries are kept in the queue and silently dropped during `pop`
/// operations only. Use [`LazyPriorityQueue::push`] to unconditionally set a
/// new priority, or [`LazyPriorityQueue::push_increase`] to set it only when
/// the new priority is strictly greater than the current one.
pub(crate) struct LazyPriorityQueue<I, P> {
	/// Map storing the current priority for each item; used to recognise stale
	/// heap entries during `pop`.
	current: FxHashMap<I, P>,
	/// Heap storing (priority, item) pairs, possibly with multiple stale
	/// entries per item.
	heap: BinaryHeap<(P, I)>,
}

impl<I, P> LazyPriorityQueue<I, P>
where
	I: Ord + Hash + Clone,
	P: Ord + Clone,
{
	/// Return the current priority of the given item, if any.
	pub(crate) fn get_priority(&self, item: &I) -> Option<P> {
		self.current.get(item).cloned()
	}

	/// Return `true` if the queue is empty.
	pub(crate) fn is_empty(&self) -> bool {
		self.current.is_empty()
	}

	/// Create a new empty queue.
	pub(crate) fn new() -> Self {
		Self {
			heap: BinaryHeap::new(),
			current: FxHashMap::default(),
		}
	}

	/// Pop the next item that is not stale (if any exist), dropping all stale
	/// items with lower order along the way.
	pub(crate) fn pop(&mut self) -> Option<(I, P)> {
		while let Some((priority, item)) = self.heap.pop() {
			// Only return entry if the queue priority matches the current one,
			// otherwise the entry is stale and must be discarded.
			if self.current.get(&item) == Some(&priority) {
				let _ = self.current.remove(&item);
				return Some((item, priority));
			}
		}
		None
	}

	/// Insert the given item with the given priority, marking any previous
	/// entry for the same item as stale. The previous priority is returned if
	/// one existed.
	pub(crate) fn push(&mut self, item: I, priority: P) -> Option<P> {
		self.heap.push((priority.clone(), item.clone()));
		self.current.insert(item, priority)
	}

	/// Insert the given item with the new priority only if the item is new or
	/// the new priority is strictly greater than the current priority.
	///
	/// Returns `None` when the priority was updated (or the item was new), and
	/// `Some(priority)` (the unchanged argument) when no update took place.
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
}

#[cfg(test)]
mod tests {
	use crate::helpers::priority_queue::LazyPriorityQueue;

	#[test]
	fn churn_with_random_updates_drains_consistently() {
		// Deterministic pseudo-random sequence chosen to exercise many stale
		// entries without bringing in a PRNG dependency.
		let updates: &[(i32, i32)] = &[
			(0, 5),
			(1, 9),
			(0, 3),
			(2, 7),
			(0, 11),
			(1, 1),
			(2, 7),
			(3, 4),
			(2, 12),
			(3, 4),
			(1, 8),
		];
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		for &(item, priority) in updates {
			let _ = q.push(item, priority);
		}

		// The final priorities are the last value seen per item: 0→11, 1→8,
		// 2→12, 3→4. Pop must surface them in strictly decreasing priority.
		let mut popped = Vec::new();
		while let Some((item, priority)) = q.pop() {
			popped.push((item, priority));
		}
		assert_eq!(popped, vec![(2, 12), (0, 11), (1, 8), (3, 4)]);
		assert!(q.is_empty());
	}

	#[test]
	fn empty_pop_returns_none() {
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		assert!(q.is_empty());
		assert_eq!(q.pop(), None);
	}

	#[test]
	fn get_priority_reflects_latest_push() {
		let mut q: LazyPriorityQueue<&'static str, i32> = LazyPriorityQueue::new();
		assert_eq!(q.get_priority(&"x"), None);

		let _ = q.push("x", 1);
		assert_eq!(q.get_priority(&"x"), Some(1));

		let prev = q.push("x", 5);
		assert_eq!(prev, Some(1));
		assert_eq!(q.get_priority(&"x"), Some(5));

		// After pop, the item is no longer tracked.
		let _ = q.pop();
		assert_eq!(q.get_priority(&"x"), None);
	}

	#[test]
	fn interleaved_pushes_and_pops_preserve_order() {
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		let _ = q.push(1, 30);
		let _ = q.push(2, 10);

		assert_eq!(q.pop(), Some((1, 30)));

		// Push a new highest-priority item after a pop.
		let _ = q.push(3, 50);
		assert_eq!(q.pop(), Some((3, 50)));
		assert_eq!(q.pop(), Some((2, 10)));
		assert_eq!(q.pop(), None);
	}

	#[test]
	fn is_empty_tracks_current_only() {
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		let _ = q.push(7, 1);
		let _ = q.push(7, 2); // makes the (1, 7) entry stale.
		assert!(!q.is_empty());

		let _ = q.pop();
		// One stale entry is still in the underlying heap, but `current` is
		// empty: `is_empty` returns the user-visible truth.
		assert!(q.is_empty());
		assert_eq!(q.pop(), None);
	}

	#[test]
	fn pop_drops_stale_entries_for_same_item() {
		let mut q: LazyPriorityQueue<&'static str, i32> = LazyPriorityQueue::new();
		let _ = q.push("a", 1);
		let _ = q.push("a", 2);
		let _ = q.push("a", 3);

		// Only the most recent priority is observable; the older heap entries
		// at priorities 1 and 2 are stale and must be dropped silently.
		assert_eq!(q.pop(), Some(("a", 3)));
		assert!(q.is_empty());
		assert_eq!(q.pop(), None);
	}

	#[test]
	fn pop_returns_highest_priority_first() {
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		let _ = q.push(1, 10);
		let _ = q.push(2, 30);
		let _ = q.push(3, 20);

		assert_eq!(q.pop(), Some((2, 30)));
		assert_eq!(q.pop(), Some((3, 20)));
		assert_eq!(q.pop(), Some((1, 10)));
		assert_eq!(q.pop(), None);
	}

	#[test]
	fn push_after_pop_reinserts_cleanly() {
		let mut q: LazyPriorityQueue<i32, i32> = LazyPriorityQueue::new();
		let _ = q.push(1, 100);
		let _ = q.pop();
		assert!(q.is_empty());

		// Reinserting must behave as a fresh insert (no stale residue).
		assert_eq!(q.push(1, 50), None);
		assert_eq!(q.get_priority(&1), Some(50));
		assert_eq!(q.pop(), Some((1, 50)));
	}

	#[test]
	fn push_increase_only_raises_priority() {
		let mut q: LazyPriorityQueue<&'static str, i32> = LazyPriorityQueue::new();

		// First insert: there is no current priority, so the item is added.
		assert_eq!(q.push_increase("a", 5), None);
		assert_eq!(q.get_priority(&"a"), Some(5));

		// Smaller priority is ignored; the argument flows back to the caller.
		assert_eq!(q.push_increase("a", 3), Some(3));
		assert_eq!(q.get_priority(&"a"), Some(5));

		// Equal priority is also ignored (strict greater-than).
		assert_eq!(q.push_increase("a", 5), Some(5));
		assert_eq!(q.get_priority(&"a"), Some(5));

		// Larger priority replaces the existing one and the previous value is
		// returned.
		assert_eq!(q.push_increase("a", 9), Some(5));
		assert_eq!(q.get_priority(&"a"), Some(9));
	}

	#[test]
	fn stale_entries_do_not_starve_other_items() {
		let mut q: LazyPriorityQueue<&'static str, i32> = LazyPriorityQueue::new();
		let _ = q.push("a", 10);
		let _ = q.push("b", 5);
		// Lower "a" below "b". The heap still has a stale (10, "a") at the top.
		let _ = q.push("a", 1);

		// `pop` must skip the stale (10, "a") and surface the highest fresh
		// priority, which is "b" at 5.
		assert_eq!(q.pop(), Some(("b", 5)));
		assert_eq!(q.pop(), Some(("a", 1)));
		assert_eq!(q.pop(), None);
	}
}
