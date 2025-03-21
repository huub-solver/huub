//! This module contains the defitions for the priority queue used by [`Engine`]
//! to schedule propagators.

use std::collections::VecDeque;

use index_vec::IndexVec;
use tracing::trace;

use crate::solver::engine::PropRef;

const ACTIVITY_THRESHOLD: f64 = 1e-7;
const ACTIVITY_ADDITIVE_FACTOR: f64 = 1.0;
const ACTIVITY_INIT_MULTIPLICATIVE_FACTOR: f64 = 0.5;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
/// The priority levels at which propagators can be scheduled.
pub enum PriorityLevel {
	/// The inactive priority level, only wake up in check solution
	Inactive,
	#[allow(
		dead_code,
		reason = "TODO: no current propagators are this priority level"
	)]
	/// The lowest priority level, all other priority levels are more important
	Lowest,
	/// A low level of priority, all apart from one priority level are more
	/// important
	Low,
	/// A medium level of priority, there are just as many normal priority levels
	/// more as less important than this one.
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

#[derive(Debug, Clone, PartialEq)]
/// A priority queue with for element with a given [`PriorityLevel`].
pub(crate) struct PriorityQueue<E> {
	/// Internal storage of the queues for each priority level.
	storage: [VecDeque<E>; 7],
	multitiplier: f64,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PropagatorInfo {
	/// Whether the propagator is currently enqueued.
	pub(crate) enqueued: bool,
	/// The priority level of the propagator.
	pub(crate) priority: PriorityLevel,
	/// Activity scores for propagators to determine whether they are active or not
	pub(crate) activity: f64,
}

#[derive(Clone, Debug, Default, PartialEq)]
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
		debug_assert!((0..6).contains(&i));
		self.storage[i].push_back(elem);
	}

	/// Pops the highest priority element from the queue.
	pub(crate) fn pop(&mut self, skip_inactive: bool) -> Option<E> {
		for queue in self.storage.iter_mut().skip(skip_inactive as usize).rev() {
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
			multitiplier: ACTIVITY_INIT_MULTIPLICATIVE_FACTOR,
		}
	}
}

impl PropagatorQueue {
	/// Enqueue a given propagator when it is not already enqueued.
	pub(crate) fn enqueue_propagator(&mut self, prop: PropRef) {
		if !self.info[prop].enqueued {
			let priority = if self.info[prop].activity > ACTIVITY_THRESHOLD {
				self.info[prop].priority
			} else {
				trace!(
					"Skip inactive propagator {:?} activity: {}",
					prop,
					self.info[prop].activity
				);
				PriorityLevel::Inactive
			};
			self.queue.insert(priority, prop);
			self.info[prop].enqueued = true;
		}
	}

	/// Enqueue all propagators from a given iterator.
	pub(crate) fn enqueue_propagators(&mut self, props: impl IntoIterator<Item = PropRef>) {
		for prop in props.into_iter() {
			self.enqueue_propagator(prop);
		}
	}

	pub(crate) fn pop(&mut self, skip_inactive: bool) -> Option<PropRef> {
		self.queue
			.pop(skip_inactive)
			.inspect(|&p| self.info[p].enqueued = false)
	}

	/// Increase the activity of a propagator.
	pub(crate) fn increase_activity(&mut self, prop: PropRef) {
		self.info[prop].activity =
			self.info[prop].activity * (1.0 - self.queue.multitiplier) + ACTIVITY_ADDITIVE_FACTOR;
	}

	/// Decrease the activity of a propagator.
	pub(crate) fn decrease_activity(&mut self, prop: PropRef) {
		self.info[prop].activity *= 1.0 - self.queue.multitiplier;
	}

	/// Update multiplier for the priority queue.
	pub(crate) fn update_multiplier(&mut self) {
		self.queue.multitiplier = self.queue.multitiplier * self.queue.multitiplier;
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
