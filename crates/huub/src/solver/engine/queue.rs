#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PriorityQueue<E> {
	storage: [Vec<E>; 6],
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

impl<E> PriorityQueue<E> {
	pub(crate) fn insert(&mut self, priority: PriorityLevel, elem: E) {
		let i = priority as usize;
		debug_assert!((0..=5).contains(&i));
		self.storage[i].push(elem)
	}

	pub(crate) fn pop(&mut self) -> Option<E> {
		for queue in self.storage.iter_mut().rev() {
			if !queue.is_empty() {
				return queue.pop();
			}
		}
		None
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub(crate) enum PriorityLevel {
	/// The lowest priority level, all other priority levels are more important
	#[allow(dead_code)] // TODO
	Lowest,
	/// A low level of priority, all apart from one priority level are more
	/// important
	Low,
	/// A medium level of priority, there are just as many normal priority levels
	/// more as less important than this one.
	#[allow(dead_code)] // TODO
	Medium,
	/// A high level of priority, all apart from one normal priority level are
	/// less important.
	#[allow(dead_code)] // TODO
	High,
	/// The highest normal priority level, this priority level is the most
	/// important normal level of priority.
	Highest,
	/// An extraordinarily high level of priority, generally used to ensure
	/// something will happen next.
	#[allow(dead_code)] // TODO
	Immediate,
}

#[cfg(test)]
mod test {
	#[test]
	fn priority_order() {
		use crate::solver::engine::queue::PriorityLevel::*;
		assert!(Immediate > Highest);
		assert!(Highest > High);
		assert!(High > Medium);
		assert!(Medium > Low);
		assert!(Low > Lowest);
	}
}
