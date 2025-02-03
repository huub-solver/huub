//! This module contains the defitions for the priority queue used by [`Engine`]
//! to schedule propagators.

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
/// The priority levels at which propagators can be scheduled.
pub enum PriorityLevel {
	#[allow(
		dead_code,
		reason = "TODO: no current propagators are this priority level"
	)]
	/// The lowest priority level, all other priority levels are more important
	Lowest,
	/// A low level of priority, all apart from one priority level are more
	/// important
	Low,
	#[allow(
		dead_code,
		reason = "TODO: no current propagators are this priority level"
	)]
	/// A medium level of priority, there are just as many normal priority levels
	/// more as less important than this one.
	Medium,
	#[allow(
		dead_code,
		reason = "TODO: no current propagators are this priority level"
	)]
	/// A high level of priority, all apart from one normal priority level are
	/// less important.
	High,
	/// The highest normal priority level, this priority level is the most
	/// important normal level of priority.
	Highest,
	#[allow(
		dead_code,
		reason = "TODO: no current propagators are this priority level"
	)]
	/// An extraordinarily high level of priority, generally used to ensure
	/// something will happen next.
	Immediate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A priority queue for propagators.
pub(crate) struct PriorityQueue<E> {
	/// Internal storage of the queues for each priority level.
	storage: [Vec<E>; 6],
}

impl<E> PriorityQueue<E> {
	/// Inserts a propagator into the queue at the end of the given priority
	/// level.
	pub(crate) fn insert(&mut self, priority: PriorityLevel, elem: E) {
		let i = priority as usize;
		debug_assert!((0..=5).contains(&i));
		self.storage[i].push(elem);
	}

	/// Pops the highest priority propagator from the queue.
	pub(crate) fn pop(&mut self) -> Option<E> {
		for queue in self.storage.iter_mut().rev() {
			if !queue.is_empty() {
				return queue.pop();
			}
		}
		None
	}
}

impl<E> Default for PriorityQueue<E> {
	fn default() -> Self {
		Self {
			storage: [
				Vec::new(),
				Vec::new(),
				Vec::new(),
				Vec::new(),
				Vec::new(),
				Vec::new(),
			],
		}
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
