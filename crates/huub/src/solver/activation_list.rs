//! Module containing data structures for the activation of propagators based on
//! changes to decision variables.

use std::{mem, ops::Add};

use crate::solver::engine::PropRef;

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
	/// The list of propagators that are to be enqueue based on different
	/// propagation conditions.
	activations: Vec<PropRef>,
	/// The index for the first propagator to be activated when an event triggers
	/// [`IntPropCond::LowerBound`].
	lower_bound_idx: u32,
	/// The index for the first propagator to be activated when an event triggers
	/// [`IntPropCond::UpperBound`].
	upper_bound_idx: u32,
	/// The first index for the propagators to be activated when an event triggers
	/// [`IntPropCond::Bounds`].
	bounds_idx: u32,
	/// The index for the first propagator to be activated when an event triggers
	/// [`IntPropCond::Domain`].
	domain_idx: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Change that has occurred in the domain of an integer variable.
pub(crate) enum IntEvent {
	/// The variable has been fixed to a single value.
	Fixed,
	/// Both of the bounds of the variable has changed.
	Bounds,
	/// The lower bound of the variable has changed.
	LowerBound,
	/// The upper bound of the variable has changed.
	UpperBound,
	/// One or more values (exluding the bounds) have been removed from the domain
	/// of the variable.
	Domain,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// The conditions of an integer variable domain change that can trigger a
/// propagator to be enqueued.
pub enum IntPropCond {
	/// Condition that triggers when the variable is fixed.
	Fixed,
	/// Condition that triggers when the lower bound of the variable changes.
	///
	/// This includes the case where the variable is fixed.
	LowerBound,
	/// Condition that triggers when the upper bound of the variable changes.
	///
	/// This includes the case where the variable is fixed.
	UpperBound,
	/// Condition that triggers when either of the bounds of the variable change.
	///
	/// This includes the case where the variable is fixed.
	Bounds,
	/// Condition that triggers for any change in the domain of the variable.
	Domain,
}

impl ActivationList {
	/// Get an iterator over the list of propagators to be enqueued.
	pub(crate) fn activated_by(&self, event: IntEvent) -> impl Iterator<Item = PropRef> + '_ {
		let r1 = if event == IntEvent::LowerBound {
			self.lower_bound_idx as usize..self.upper_bound_idx as usize
		} else {
			0..0
		};
		let r2 = match event {
			IntEvent::Fixed => 0..,
			// NOTE: Bounds (Event) should trigger both LowerBound and UpperBound conditions
			IntEvent::Bounds => self.lower_bound_idx as usize..,
			IntEvent::UpperBound => self.upper_bound_idx as usize..,
			IntEvent::LowerBound => self.bounds_idx as usize..,
			IntEvent::Domain => self.domain_idx as usize..,
		};
		self.activations[r1]
			.iter()
			.copied()
			.chain(self.activations[r2].iter().copied())
	}
	/// Add a propagator to the list of propagators to be enqueued based on the
	/// given condition.
	pub(crate) fn add(&mut self, mut prop: PropRef, condition: IntPropCond) {
		assert!(self.activations.len() < u32::MAX as usize, "Unable to add more than u32::MAX propagators to the activation list of a single variable.");
		let mut cond_swap = |idx: u32| {
			let idx = idx as usize;
			if idx < self.activations.len() {
				mem::swap(&mut prop, &mut self.activations[idx]);
			}
		};
		match condition {
			IntPropCond::Fixed => {
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
			IntPropCond::LowerBound => {
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
			IntPropCond::UpperBound => {
				cond_swap(self.bounds_idx);
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntPropCond::Bounds => {
				cond_swap(self.domain_idx);
				self.domain_idx += 1;
				self.activations.push(prop);
			}
			IntPropCond::Domain => self.activations.push(prop),
		};
	}
}

impl Add<IntEvent> for IntEvent {
	type Output = IntEvent;

	fn add(self, rhs: IntEvent) -> Self::Output {
		use IntEvent::*;
		match (self, rhs) {
			(Fixed, _) | (_, Fixed) => Fixed,
			(Bounds, _) | (_, Bounds) => Bounds,
			(LowerBound, UpperBound) | (UpperBound, LowerBound) => Bounds,
			(LowerBound, _) | (_, LowerBound) => LowerBound,
			(UpperBound, _) | (_, UpperBound) => UpperBound,
			(Domain, Domain) => Domain,
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashSet;

	use itertools::Itertools;

	use crate::solver::{
		activation_list::{ActivationList, IntEvent, IntPropCond},
		engine::PropRef,
	};

	#[test]
	fn test_activation_list() {
		let props = [
			(PropRef::from(0), IntPropCond::Fixed),
			(PropRef::from(1), IntPropCond::LowerBound),
			(PropRef::from(2), IntPropCond::UpperBound),
			(PropRef::from(3), IntPropCond::Bounds),
			(PropRef::from(4), IntPropCond::Domain),
		];

		for list in props.iter().permutations(5) {
			let mut activation_list = ActivationList::default();
			for (prop, cond) in list.iter() {
				activation_list.add(*prop, *cond);
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
			let bounds: HashSet<_> = activation_list.activated_by(IntEvent::Bounds).collect();
			assert_eq!(
				bounds,
				HashSet::from_iter([
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
			let domain: HashSet<_> = activation_list.activated_by(IntEvent::Domain).collect();
			assert_eq!(domain, HashSet::from_iter([PropRef::from(4)]));
		}
	}
}
