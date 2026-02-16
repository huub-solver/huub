//! This module contains the definitions for the priority queue used by
//! [`Engine`] to schedule propagators.

use std::collections::VecDeque;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
/// The priority levels at which propagators can be scheduled.
pub enum PriorityLevel {
	/// The lowest priority level, all other priority levels are more important
	Lowest,
	/// A low level of priority, all apart from one priority level are more
	/// important
	Low,
	/// A medium level of priority, there are just as many normal priority
	/// levels more as less important than this one.
	Medium,
	/// A high level of priority, all apart from one normal priority level are
	/// less important.
	High,
	/// The highest normal priority level, this priority level is the most
	/// important normal level of priority.
	Highest,
	/// An extraordinarily high level of priority, generally used to ensure
	/// something will happen next.
	Immediate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A priority queue with for element with a given [`PriorityLevel`].
pub(crate) struct PriorityQueue<E> {
	/// Internal storage of the queues for each priority level.
	storage: [VecDeque<E>; 6],
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Information about a propagator in the propagation engine.
pub(crate) struct PropagatorInfo {
	/// Whether the propagator is currently enqueued.
	pub(crate) enqueued: bool,
	/// The priority level of the propagator.
	pub(crate) priority: PriorityLevel,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// A priority queue for propagators.
pub(crate) struct PropagatorQueue {
	/// Priority queue of the propagators.
	queue: PriorityQueue<u32>,
	/// General information about the propagators in the solver.
	pub(crate) info: Vec<PropagatorInfo>,
}

impl<E> PriorityQueue<E> {
	/// Inserts an element into the queue at the end of the given priority
	/// level.
	pub(crate) fn insert(&mut self, priority: PriorityLevel, elem: E) {
		let i = priority as usize;
		debug_assert!((0..=5).contains(&i));
		self.storage[i].push_back(elem);
	}

	/// Pops the highest priority element from the queue.
	pub(crate) fn pop(&mut self) -> Option<E> {
		for queue in self.storage.iter_mut().rev() {
			if !queue.is_empty() {
				return queue.pop_front();
			}
		}
		None
	}
}

impl<E> Default for PriorityQueue<E> {
	fn default() -> Self {
		Self {
			storage: Default::default(),
		}
	}
}

impl PropagatorQueue {
	/// Enqueue a given propagator when it is not already enqueued.
	pub(crate) fn enqueue_propagator(&mut self, prop: u32) {
		if !self.info[prop as usize].enqueued {
			self.info[prop as usize].enqueued = true;
			self.queue.insert(self.info[prop as usize].priority, prop);
		}
	}

	/// Pop a propagator from the queue if there are any.
	pub(crate) fn pop(&mut self) -> Option<u32> {
		self.queue
			.pop()
			.inspect(|p| self.info[*p as usize].enqueued = false)
	}
}

#[cfg(test)]
mod test {
	#[test]
	fn priority_order() {
		use crate::solver::queue::PriorityLevel::*;
		assert!(Immediate > Highest);
		assert!(Highest > High);
		assert!(High > Medium);
		assert!(Medium > Low);
		assert!(Low > Lowest);
	}
}
