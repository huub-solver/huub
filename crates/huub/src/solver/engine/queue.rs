const PRIORITY_LEVEL_COUNT: usize = PriorityLevel::Immediate as usize + 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PriorityQueue<E> {
	storage: [Vec<E>; PRIORITY_LEVEL_COUNT],
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
				Vec::new(),
			],
		}
	}
}

impl<E> PriorityQueue<E> {
	pub(crate) fn insert(&mut self, priority: PriorityLevel, elem: E) {
		let i = priority as usize;
		debug_assert!((0..=PRIORITY_LEVEL_COUNT - 1).contains(&i));
		self.storage[i].push(elem);
	}

	pub(crate) fn pop<const SKIP_INACTIVE: bool>(&mut self) -> Option<E> {
		for queue in self.storage.iter_mut().skip(SKIP_INACTIVE as usize).rev() {
			if !queue.is_empty() {
				return queue.pop();
			}
		}
		None
	}

	pub(crate) fn is_empty(&self) -> bool {
		self.storage.iter().all(Vec::is_empty)
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub(crate) enum PriorityLevel {
	/// The inactive priority level, only triggered in check model
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
