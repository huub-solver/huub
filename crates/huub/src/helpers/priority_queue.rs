//! Minimum priority queue whose priorities can be changed after insertion.

use crate::DeepClone;

/// A minimum priority queue over dense `usize` items that supports changing
/// the priority of an item that is already queued.
///
/// The queue is a binary heap together with the heap position of each item, so
/// that a changed priority is repaired in place rather than pushed as a second
/// entry. The heap therefore holds each queued item exactly once, and an item
/// costs only its position when it is not queued.
#[derive(Clone, Debug, DeepClone)]
#[deepclone(bound = "P: DeepClone")]
pub(crate) struct IndexedPriorityQueue<P> {
	/// Binary min-heap of `(priority, item)` pairs.
	heap: Vec<(P, usize)>,
	/// The position of each item in [`Self::heap`], indexed by item, or
	/// [`Self::NOT_QUEUED`] when it is not queued.
	position: Vec<u32>,
}

impl<P: Ord> IndexedPriorityQueue<P> {
	/// The position of an item that is not queued.
	const NOT_QUEUED: u32 = u32::MAX;

	/// Remove all items, keeping the allocated capacity so the queue can be
	/// reused for the next search without reallocating.
	pub(crate) fn clear(&mut self) {
		for &(_, item) in &self.heap {
			self.position[item] = Self::NOT_QUEUED;
		}
		self.heap.clear();
	}

	/// Whether the given item is currently queued.
	pub(crate) fn contains(&self, item: usize) -> bool {
		self.position
			.get(item)
			.is_some_and(|&pos| pos != Self::NOT_QUEUED)
	}

	/// Move the entry at `pos` towards the leaves until the heap is restored.
	fn move_down(&mut self, mut pos: usize) {
		loop {
			let left = 2 * pos + 1;
			if left >= self.heap.len() {
				break;
			}
			let right = left + 1;
			let child = if right < self.heap.len() && self.heap[right].0 < self.heap[left].0 {
				right
			} else {
				left
			};
			if self.heap[child].0 >= self.heap[pos].0 {
				break;
			}
			self.swap(pos, child);
			pos = child;
		}
	}

	/// Move the entry at `pos` towards the root until the heap is restored.
	fn move_up(&mut self, mut pos: usize) {
		while pos > 0 {
			let parent = (pos - 1) / 2;
			if self.heap[parent].0 <= self.heap[pos].0 {
				break;
			}
			self.swap(pos, parent);
			pos = parent;
		}
	}

	/// Remove the queued item with the lowest priority.
	pub(crate) fn pop(&mut self) -> Option<(usize, P)> {
		if self.heap.is_empty() {
			return None;
		}
		let (priority, item) = self.heap.swap_remove(0);
		self.position[item] = Self::NOT_QUEUED;
		if let Some(&(_, moved)) = self.heap.first() {
			self.position[moved] = 0;
			self.move_down(0);
		}
		Some((item, priority))
	}

	/// Queue the item at the given priority, replacing its current priority if
	/// it is already queued.
	pub(crate) fn push(&mut self, item: usize, priority: P) {
		if item >= self.position.len() {
			self.position.resize(item + 1, Self::NOT_QUEUED);
		}
		let pos = self.position[item];
		if pos == Self::NOT_QUEUED {
			let pos = self.heap.len();
			self.position[item] =
				u32::try_from(pos).expect("the queue holds fewer than `u32::MAX` items");
			self.heap.push((priority, item));
			self.move_up(pos);
			return;
		}
		let pos = pos as usize;
		let decreased = priority < self.heap[pos].0;
		self.heap[pos].0 = priority;
		if decreased {
			self.move_up(pos);
		} else {
			self.move_down(pos);
		}
	}

	/// Queue the item at the given priority if it is not queued yet, or lower
	/// its priority to the given one if that is an improvement. Returns whether
	/// the queue was changed.
	pub(crate) fn push_decrease(&mut self, item: usize, priority: P) -> bool {
		if self.contains(item) && priority >= self.heap[self.position[item] as usize].0 {
			return false;
		}
		self.push(item, priority);
		true
	}

	/// Swap two heap entries, keeping [`Self::position`] in step.
	fn swap(&mut self, a: usize, b: usize) {
		self.heap.swap(a, b);
		self.position[self.heap[a].1] = a as u32;
		self.position[self.heap[b].1] = b as u32;
	}
}

impl<P> Default for IndexedPriorityQueue<P> {
	fn default() -> Self {
		Self {
			heap: Vec::new(),
			position: Vec::new(),
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::BTreeMap;

	use crate::helpers::priority_queue::IndexedPriorityQueue;

	#[test]
	fn test_priority_queue_clear_keeps_reusable() {
		let mut queue = IndexedPriorityQueue::default();
		queue.push(0, 1);
		let _ = queue.push_decrease(0, 0);
		queue.clear();

		assert!(!queue.contains(0));
		assert_eq!(queue.pop(), None);

		queue.push(1, 5);
		assert_eq!(queue.pop(), Some((1, 5)));
		assert_eq!(queue.pop(), None);
	}

	/// Pops must come out in priority order whatever mix of insertions,
	/// decreases, and increases produced the queue. Checked against a simple
	/// map over a long pseudo-random sequence.
	#[test]
	fn test_priority_queue_matches_reference() {
		let mut queue = IndexedPriorityQueue::default();
		let mut reference = BTreeMap::new();
		let mut state: u64 = 0x2545_f491_4f6c_dd1d;
		let mut next = |bound: u64| {
			state = state
				.wrapping_mul(6_364_136_223_846_793_005)
				.wrapping_add(1_442_695_040_888_963_407);
			(state >> 33) % bound
		};
		for _ in 0..10_000 {
			match next(4) {
				0 => {
					let expected = reference
						.iter()
						.map(|(&item, &priority)| (priority, item))
						.min();
					let popped = queue.pop().map(|(item, priority)| (priority, item));
					assert_eq!(
						popped.map(|(p, _)| p),
						expected.map(|(p, _)| p),
						"popped priority"
					);
					if let Some((_, item)) = popped {
						assert_eq!(reference.remove(&item), popped.map(|(p, _)| p));
					}
				}
				1 => {
					let (item, priority) = (next(50) as usize, next(100));
					let changed = queue.push_decrease(item, priority);
					let improves = reference.get(&item).is_none_or(|&cur| priority < cur);
					assert_eq!(changed, improves);
					if improves {
						let _ = reference.insert(item, priority);
					}
				}
				_ => {
					let (item, priority) = (next(50) as usize, next(100));
					queue.push(item, priority);
					let _ = reference.insert(item, priority);
				}
			}
			for item in 0..50 {
				assert_eq!(queue.contains(item), reference.contains_key(&item));
			}
		}
	}

	#[test]
	fn test_priority_queue_pop_order() {
		let mut queue = IndexedPriorityQueue::default();
		for (item, priority) in [(0, 3), (1, 1), (2, 2)] {
			queue.push(item, priority);
		}

		assert_eq!(queue.pop(), Some((1, 1)));
		assert_eq!(queue.pop(), Some((2, 2)));
		assert_eq!(queue.pop(), Some((0, 3)));
		assert_eq!(queue.pop(), None);
	}

	#[test]
	fn test_priority_queue_pop_removes_item() {
		let mut queue = IndexedPriorityQueue::default();
		queue.push(0, 1);
		assert!(queue.contains(0));

		assert_eq!(queue.pop(), Some((0, 1)));
		assert!(!queue.contains(0));
	}

	#[test]
	fn test_priority_queue_push_decrease() {
		let mut queue = IndexedPriorityQueue::default();

		assert!(queue.push_decrease(0, 5));
		// An equal priority is not an improvement, so nothing changes.
		assert!(!queue.push_decrease(0, 5));
		assert!(!queue.push_decrease(0, 7));
		assert!(queue.push_decrease(0, 2));

		assert_eq!(queue.pop(), Some((0, 2)));
		assert_eq!(queue.pop(), None);
	}

	#[test]
	fn test_priority_queue_push_replaces_priority() {
		let mut queue = IndexedPriorityQueue::default();
		queue.push(0, 1);
		// Unlike `push_decrease`, `push` also accepts a worse priority.
		queue.push(0, 4);
		queue.push(1, 2);

		assert_eq!(queue.pop(), Some((1, 2)));
		assert_eq!(queue.pop(), Some((0, 4)));
		assert_eq!(queue.pop(), None);
	}
}
