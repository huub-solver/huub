//! This module contains the defitions for the priority queue used by [`Engine`]
//! to schedule propagators.

use index_vec::IndexVec;

use crate::solver::engine::PropRef;

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
/// A priority queue with for element with a given [`PriorityLevel`].
pub(crate) struct PriorityQueue<E> {
	/// Internal storage of the queues for each priority level.
	storage: [Vec<E>; 6],
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
	queue: PriorityQueue<PropRef>,
	/// General information about the propagators in the solver.
	pub(crate) info: IndexVec<PropRef, PropagatorInfo>,
}

impl<E> PriorityQueue<E> {
	/// Inserts an element into the queue at the end of the given priority level.
	pub(crate) fn insert(&mut self, priority: PriorityLevel, elem: E) {
		let i = priority as usize;
		debug_assert!((0..=5).contains(&i));
		self.storage[i].push(elem);
	}

	/// Pops the highest priority element from the queue.
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

impl PropagatorQueue {
	#[cfg(debug_assertions)]
	/// (TARGET DEBUG) Method used to create a dummy queue for temporary
	/// replacement of the propagator queue.
	///
	/// Used in [`Engine::debug_check_reasons`].
	pub(crate) fn dummy_queue(num_prop: usize) -> Self {
		use index_vec::index_vec;

		Self {
			queue: PriorityQueue::default(),
			info: index_vec![PropagatorInfo { enqueued: true, priority: PriorityLevel::Lowest }; num_prop],
		}
	}

	/// Enqueue a given propagator when it is not already enqueued.
	pub(crate) fn enqueue_propagator(&mut self, prop: PropRef) {
		if !self.info[prop].enqueued {
			self.queue.insert(self.info[prop].priority, prop);
			self.info[prop].enqueued = true;
		}
	}

	/// Enqueue all propagators from a given iterator.
	pub(crate) fn enqueue_propagators(&mut self, props: impl IntoIterator<Item = PropRef>) {
		for prop in props.into_iter() {
			self.enqueue_propagator(prop);
		}
	}

	/// Pop a propagator from the queue if there are any.
	pub(crate) fn pop(&mut self) -> Option<PropRef> {
		self.queue.pop().inspect(|&p| self.info[p].enqueued = false)
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
