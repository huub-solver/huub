use std::mem;

use crate::{propagator::int_event::IntEvent, solver::engine::PropRef};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// A data structure that store a list of propagators to be enqueued based on
/// different propagation conditions.
///
/// The list is sorted in the following order of propagation condition:
/// Fixed, LowerBound, UpperBound, Bound, Domain.
///
/// Unless the condition is LowerBound, enqueueing can start from the index
/// of the most specific condition and enqueue all propagators untill the end
/// of the list. If the condition is LowerBound, enqueueing can start from the
/// index of the LowerBound condition, enqueue all propagators untill the
/// beginning of the UpperBound condition, and then continue from the beginning
/// of the Bound condition to the end of the list.
pub(crate) struct ActivationList {
	activations: Vec<PropRef>,
	lower_bound_idx: u16,
	upper_bound_idx: u16,
	bounds_idx: u16,
	domain_idx: u16,
}

impl ActivationList {
	/// Add a propagator to the list of propagators to be enqueued based on the
	/// given condition.
	pub(crate) fn add(&mut self, mut prop: PropRef, condition: IntEvent) {
		assert!(self.activations.len() < u16::MAX as usize, "Unable to add more than u16::MAX propagators to the activation list of a single variable.");
		// TODO: Optimize insertion using swapping
		let mut cond_swap = |idx: u16| {
			let idx = idx as usize;
			if idx < self.activations.len() {
				mem::swap(&mut prop, &mut self.activations[idx]);
			}
		};
		match condition {
			IntEvent::Fixed => {
				cond_swap(self.lower_bound_idx);
				if self.lower_bound_idx < self.upper_bound_idx {
					cond_swap(self.upper_bound_idx);
				}
				if self.upper_bound_idx < self.bounds_idx {
					cond_swap(self.bounds_idx);
				}
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.lower_bound_idx += 1;
				self.upper_bound_idx += 1;
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntEvent::LowerBound => {
				cond_swap(self.upper_bound_idx);
				if self.upper_bound_idx < self.bounds_idx {
					cond_swap(self.bounds_idx);
				}
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.upper_bound_idx += 1;
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntEvent::UpperBound => {
				cond_swap(self.bounds_idx);
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntEvent::Bounds => {
				cond_swap(self.domain_idx);
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntEvent::Domain => self.activations.push(prop),
		};
	}

	/// Get an iterator over the list of propagators to be enqueued.
	pub(crate) fn activated_by(&self, event: IntEvent) -> impl Iterator<Item = PropRef> + '_ {
		let r1 = if event == IntEvent::LowerBound {
			self.lower_bound_idx as usize..self.upper_bound_idx as usize
		} else {
			0..0
		};
		let r2 = match event {
			IntEvent::Fixed => 0..,
			IntEvent::UpperBound => self.upper_bound_idx as usize..,
			IntEvent::Bounds | IntEvent::LowerBound => self.bounds_idx as usize..,
			IntEvent::Domain => self.domain_idx as usize..,
		};
		self.activations[r1]
			.iter()
			.copied()
			.chain(self.activations[r2].iter().copied())
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashSet;

	use itertools::Itertools;

	use crate::{
		propagator::int_event::IntEvent,
		solver::engine::{activation_list::ActivationList, PropRef},
	};

	#[test]
	fn test_activation_list() {
		let props = [
			(PropRef::from(0), IntEvent::Fixed),
			(PropRef::from(1), IntEvent::LowerBound),
			(PropRef::from(2), IntEvent::UpperBound),
			(PropRef::from(3), IntEvent::Bounds),
			(PropRef::from(4), IntEvent::Domain),
		];

		for list in props.iter().permutations(5) {
			let mut activation_list = ActivationList::default();
			for (prop, cond) in list.iter() {
				activation_list.add(*prop, cond.clone());
			}
			let fixed: HashSet<_> = activation_list.activated_by(IntEvent::Fixed).collect();
			assert_eq!(
				fixed,
				HashSet::from_iter([
					PropRef::from(0),
					PropRef::from(1),
					PropRef::from(2),
					PropRef::from(3),
					PropRef::from(4)
				])
			);
			let lower_bound: HashSet<_> =
				activation_list.activated_by(IntEvent::LowerBound).collect();
			assert_eq!(
				lower_bound,
				HashSet::from_iter([PropRef::from(1), PropRef::from(3), PropRef::from(4)])
			);
			let upper_bound: HashSet<_> =
				activation_list.activated_by(IntEvent::UpperBound).collect();
			assert_eq!(
				upper_bound,
				HashSet::from_iter([PropRef::from(2), PropRef::from(3), PropRef::from(4)])
			);
			let bounds: HashSet<_> = activation_list.activated_by(IntEvent::Bounds).collect();
			assert_eq!(
				bounds,
				HashSet::from_iter([PropRef::from(3), PropRef::from(4)])
			);
			let domain: HashSet<_> = activation_list.activated_by(IntEvent::Domain).collect();
			assert_eq!(domain, HashSet::from_iter([PropRef::from(4)]));
		}
	}
}
