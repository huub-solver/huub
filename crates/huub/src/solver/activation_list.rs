//! Module containing data structures for the activation of propagators based on
//! changes to decision variables.

use std::{
	mem,
	ops::{Add, AddAssign},
};

use itertools::Itertools;

use crate::{
	solver::engine::{Advisor, PropRef},
	ConRef,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// A data structure that store a list of propagators to be enqueued based on
/// different propagation conditions.
///
/// The list is sorted in the following order of propagation condition:
/// Fixed, LowerBound, UpperBound, Bound, Domain.
///
/// Unless the condition is LowerBound, enqueueing can start from the index
/// of the most specific condition and enqueue all propagators until the end
/// of the list. If the condition is LowerBound, enqueueing can start from the
/// index of the LowerBound condition, enqueue all propagators until the
/// beginning of the UpperBound condition, and then continue from the beginning
/// of the Bound condition to the end of the list.
pub(crate) struct ActivationList {
	/// The list of propagators that are to be enqueue based on different
	/// propagation conditions.
	activations: Vec<ActivationActionS>,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::LowerBound`].
	lower_bound_idx: u32,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::UpperBound`].
	upper_bound_idx: u32,
	/// The first index for the propagators to be activated when an event
	/// triggers [`IntPropCond::Bounds`].
	bounds_idx: u32,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::Domain`].
	domain_idx: u32,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Possible actions to be triggered by the activation list.
pub(crate) enum ActivationAction<A, P> {
	/// When activated, advise the propagator with the given [`PropRef`] of the
	/// event that triggered the activation. If the adviser method returns
	/// `true`, then enqueue the propagator if it is not already in the queue.
	Advise(A),
	/// When activated, simply add the propagator with the given [`PropRef`] to
	/// the propagator queue if it is not already in the queue.
	Enqueue(P),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Object used to efficiently store an [`ActivationAction`].
pub(crate) struct ActivationActionS(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Change that has occurred in the domain of an integer variable.
pub enum IntEvent {
	/// The variable has been fixed to a single value.
	Fixed,
	/// Both of the bounds of the variable has changed.
	Bounds,
	/// The lower bound of the variable has changed.
	LowerBound,
	/// The upper bound of the variable has changed.
	UpperBound,
	/// One or more values (excluding the bounds) have been removed from the
	/// domain of the variable.
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
	/// Condition that triggers when either of the bounds of the variable
	/// change.
	///
	/// This includes the case where the variable is fixed.
	Bounds,
	/// Condition that triggers for any change in the domain of the variable.
	Domain,
}

impl From<ActivationActionS> for ActivationAction<Advisor, PropRef> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(Advisor::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(PropRef::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationAction<Advisor, PropRef>> for ActivationActionS {
	fn from(value: ActivationAction<Advisor, PropRef>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl From<ActivationActionS> for ActivationAction<Advisor, ConRef> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(Advisor::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(ConRef::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationAction<Advisor, ConRef>> for ActivationActionS {
	fn from(value: ActivationAction<Advisor, ConRef>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl ActivationList {
	/// Get an iterator over the list of propagators to be enqueued.
	pub(crate) fn activated_by<'a, A, P>(
		&'a self,
		event: IntEvent,
	) -> impl Iterator<Item = ActivationAction<A, P>> + 'a
	where
		ActivationAction<A, P>: From<ActivationActionS>,
		A: 'a,
		P: 'a,
	{
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
			.chain(self.activations[r2].iter())
			.copied()
			.map_into()
	}
	/// Add a propagator to the list of propagators to be enqueued based on the
	/// given condition.
	pub(crate) fn add<A, P>(&mut self, action: ActivationAction<A, P>, condition: IntPropCond)
	where
		ActivationAction<A, P>: Into<ActivationActionS>,
	{
		assert!(self.activations.len() < u32::MAX as usize, "Unable to add more than u32::MAX propagators to the activation list of a single variable.");
		let mut action = action.into();
		let mut cond_swap = |idx: u32| {
			let idx = idx as usize;
			if idx < self.activations.len() {
				mem::swap(&mut action, &mut self.activations[idx]);
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
				self.activations.push(action);
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
				self.activations.push(action);
			}
			IntPropCond::UpperBound => {
				cond_swap(self.bounds_idx);
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::Bounds => {
				cond_swap(self.domain_idx);
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::Domain => self.activations.push(action),
		};
	}

	pub(crate) fn extend(&mut self, other: Self) {
		for (i, act) in other.activations.into_iter().enumerate() {
			let i = i as u32;
			let act: ActivationAction<Advisor, PropRef> = act.into();
			self.add(
				act,
				if i < other.lower_bound_idx {
					IntPropCond::Fixed
				} else if i < other.upper_bound_idx {
					IntPropCond::LowerBound
				} else if i < other.bounds_idx {
					IntPropCond::UpperBound
				} else if i < other.domain_idx {
					IntPropCond::Bounds
				} else {
					IntPropCond::Domain
				},
			);
		}
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

impl AddAssign<IntEvent> for IntEvent {
	fn add_assign(&mut self, rhs: IntEvent) {
		*self = *self + rhs;
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use rustc_hash::FxHashSet;

	use crate::solver::{
		activation_list::{ActivationAction, ActivationList, IntEvent, IntPropCond},
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
				activation_list.add(ActivationAction::Enqueue(*prop), *cond);
			}
			let fixed: FxHashSet<_> = activation_list.activated_by(IntEvent::Fixed).collect();
			assert_eq!(
				fixed,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::from(0)),
					ActivationAction::Enqueue(PropRef::from(1)),
					ActivationAction::Enqueue(PropRef::from(2)),
					ActivationAction::Enqueue(PropRef::from(3)),
					ActivationAction::Enqueue(PropRef::from(4))
				])
			);
			let bounds: FxHashSet<_> = activation_list.activated_by(IntEvent::Bounds).collect();
			assert_eq!(
				bounds,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::from(1)),
					ActivationAction::Enqueue(PropRef::from(2)),
					ActivationAction::Enqueue(PropRef::from(3)),
					ActivationAction::Enqueue(PropRef::from(4))
				])
			);
			let lower_bound: FxHashSet<_> =
				activation_list.activated_by(IntEvent::LowerBound).collect();
			assert_eq!(
				lower_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::from(1)),
					ActivationAction::Enqueue(PropRef::from(3)),
					ActivationAction::Enqueue(PropRef::from(4))
				])
			);
			let upper_bound: FxHashSet<_> =
				activation_list.activated_by(IntEvent::UpperBound).collect();
			assert_eq!(
				upper_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::from(2)),
					ActivationAction::Enqueue(PropRef::from(3)),
					ActivationAction::Enqueue(PropRef::from(4))
				])
			);
			let domain: FxHashSet<_> = activation_list.activated_by(IntEvent::Domain).collect();
			assert_eq!(
				domain,
				FxHashSet::from_iter([ActivationAction::Enqueue(PropRef::from(4))])
			);
		}
	}
}
