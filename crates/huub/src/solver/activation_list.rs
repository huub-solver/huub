//! Module containing data structures for the activation of propagators based on
//! changes to decision variables.

use std::{
	mem,
	ops::{Add, AddAssign},
};

use crate::{
	actions::{IntEvent, IntPropCond},
	model::{self, ConstraintId},
	solver::engine::{self, PropagatorId},
};

/// Possible actions to be triggered by the activation list.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ActivationAction<A, P> {
	/// When activated, advise the propagator with the given [`PropagatorId`] of
	/// the event that triggered the activation. If the advisor method returns
	/// `true`, then enqueue the propagator if it is not already in the queue.
	Advise(A),
	/// When activated, simply add the propagator with the given
	/// [`PropagatorId`] to the propagator queue if it is not already in the
	/// queue.
	Enqueue(P),
}

/// Object used to efficiently store an [`ActivationAction`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ActivationActionS(u32);

/// A data structure that stores a list of propagators to be enqueued based on
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
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ActivationList {
	/// The list of propagators that are to be enqueued based on different
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

impl From<ActivationActionS> for ActivationAction<engine::AdvisorId, PropagatorId> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(engine::AdvisorId::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(PropagatorId::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationActionS> for ActivationAction<model::AdvisorId, ConstraintId> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(model::AdvisorId::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(ConstraintId::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationAction<engine::AdvisorId, PropagatorId>> for ActivationActionS {
	fn from(value: ActivationAction<engine::AdvisorId, PropagatorId>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl From<ActivationAction<model::AdvisorId, ConstraintId>> for ActivationActionS {
	fn from(value: ActivationAction<model::AdvisorId, ConstraintId>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl ActivationList {
	/// Add a propagator to the list of propagators to be enqueued based on the
	/// given condition.
	pub(crate) fn add<A, P>(&mut self, action: ActivationAction<A, P>, condition: IntPropCond)
	where
		ActivationAction<A, P>: Into<ActivationActionS>,
	{
		assert!(
			self.activations.len() < u32::MAX as usize,
			"Unable to add more than u32::MAX propagators to the activation list of a single variable."
		);
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

	/// Extend the activation list with another activation list, consuming it.
	pub(crate) fn extend(&mut self, other: Self) {
		for (i, act) in other.activations.into_iter().enumerate() {
			let i = i as u32;
			let act: ActivationAction<engine::AdvisorId, PropagatorId> = act.into();
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

	/// Iterate over the activation actions triggered by the given event and
	/// execute the provided function for each of them.
	///
	/// This method does not enqueue or advise by itself; it simply delegates
	/// handling to the provided function `f`.
	pub(crate) fn for_each_activated_by<A, P, F>(&self, event: IntEvent, mut f: F)
	where
		ActivationAction<A, P>: From<ActivationActionS>,
		F: FnMut(ActivationAction<A, P>),
	{
		if event == IntEvent::LowerBound {
			for &act in
				&self.activations[self.lower_bound_idx as usize..self.upper_bound_idx as usize]
			{
				f(act.into());
			}
			for &act in &self.activations[self.bounds_idx as usize..] {
				f(act.into());
			}
		} else {
			let start = match event {
				IntEvent::Fixed => 0,
				IntEvent::Bounds => self.lower_bound_idx as usize,
				IntEvent::UpperBound => self.upper_bound_idx as usize,
				IntEvent::LowerBound => unreachable!(),
				IntEvent::Domain => self.domain_idx as usize,
			};
			for &act in &self.activations[start..] {
				f(act.into());
			}
		}
	}

	/// Remove the first activation subscribed with the given propagation
	/// condition for which `matches` returns `true`, and return whether such an
	/// activation was found.
	///
	/// An activation must be removed using the same [`IntPropCond`] with which
	/// it was added, since an activation only ever lives in the block of the
	/// condition it subscribed with.
	pub(crate) fn remove(
		&mut self,
		condition: IntPropCond,
		mut matches: impl FnMut(ActivationActionS) -> bool,
	) -> bool {
		// The index just past the last activation of each block, in the order in
		// which the blocks are stored.
		let ends = [
			self.lower_bound_idx,
			self.upper_bound_idx,
			self.bounds_idx,
			self.domain_idx,
			self.activations.len() as u32,
		];
		let block = match condition {
			IntPropCond::Fixed => 0,
			IntPropCond::LowerBound => 1,
			IntPropCond::UpperBound => 2,
			IntPropCond::Bounds => 3,
			IntPropCond::Domain => 4,
		};
		let start = if block == 0 { 0 } else { ends[block - 1] };
		let Some(pos) = (start..ends[block]).find(|&i| matches(self.activations[i as usize]))
		else {
			return false;
		};

		// The activations within a block are unordered, so the activation can be
		// swapped with the last one of its own block. That leaves it at the end
		// of the block, from where the same swap with the next block moves it
		// along, until it reaches the end of the list and can be removed.
		let mut hole = pos as usize;
		for &end in &ends[block..] {
			let last = end as usize - 1;
			self.activations.swap(hole, last);
			hole = last;
		}
		debug_assert_eq!(hole, self.activations.len() - 1);
		let _ = self.activations.pop();

		// Every boundary from the end of the block onwards moves down by one.
		for idx in [
			&mut self.lower_bound_idx,
			&mut self.upper_bound_idx,
			&mut self.bounds_idx,
			&mut self.domain_idx,
		]
		.into_iter()
		.skip(block)
		{
			*idx -= 1;
		}
		true
	}

	/// Return the number of subscriptions to the decision variable.
	pub(crate) fn subscription_count(&self) -> u32 {
		self.activations.len() as u32
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

	use crate::{
		actions::{IntEvent, IntPropCond},
		solver::{
			activation_list::{ActivationAction, ActivationActionS, ActivationList},
			engine::{AdvisorId, PropagatorId},
		},
	};

	/// Assert that `list` reports exactly the propagators of `present` for
	/// every integer event, based on the propagation condition each subscribed
	/// with.
	fn assert_activations(list: &ActivationList, present: &[(PropagatorId, IntPropCond)]) {
		let triggers = |cond: IntPropCond, event: IntEvent| match event {
			IntEvent::Fixed => true,
			IntEvent::Bounds => cond != IntPropCond::Fixed,
			IntEvent::LowerBound => matches!(
				cond,
				IntPropCond::LowerBound | IntPropCond::Bounds | IntPropCond::Domain
			),
			IntEvent::UpperBound => matches!(
				cond,
				IntPropCond::UpperBound | IntPropCond::Bounds | IntPropCond::Domain
			),
			IntEvent::Domain => cond == IntPropCond::Domain,
		};
		assert_eq!(list.subscription_count() as usize, present.len());
		for event in [
			IntEvent::Fixed,
			IntEvent::Bounds,
			IntEvent::LowerBound,
			IntEvent::UpperBound,
			IntEvent::Domain,
		] {
			let mut actual = FxHashSet::default();
			list.for_each_activated_by(event, |a: ActivationAction<AdvisorId, PropagatorId>| {
				let _ = actual.insert(a);
			});
			let expected: FxHashSet<ActivationAction<AdvisorId, PropagatorId>> = present
				.iter()
				.filter(|&&(_, cond)| triggers(cond, event))
				.map(|&(prop, _)| ActivationAction::Enqueue(prop))
				.collect();
			assert_eq!(actual, expected, "activations of {event:?} for {present:?}");
		}
	}

	#[test]
	fn test_activation_list() {
		let props = [
			(PropagatorId::new(0), IntPropCond::Fixed),
			(PropagatorId::new(1), IntPropCond::LowerBound),
			(PropagatorId::new(2), IntPropCond::UpperBound),
			(PropagatorId::new(3), IntPropCond::Bounds),
			(PropagatorId::new(4), IntPropCond::Domain),
		];

		for list in props.iter().permutations(5) {
			let mut activation_list = ActivationList::default();
			for (prop, cond) in list.iter() {
				activation_list.add(ActivationAction::Enqueue(*prop), *cond);
			}
			let mut fixed = FxHashSet::default();
			activation_list.for_each_activated_by(IntEvent::Fixed, |a: ActivationAction<_, _>| {
				fixed.insert(a);
			});
			assert_eq!(
				fixed,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropagatorId::new(0)),
					ActivationAction::Enqueue(PropagatorId::new(1)),
					ActivationAction::Enqueue(PropagatorId::new(2)),
					ActivationAction::Enqueue(PropagatorId::new(3)),
					ActivationAction::Enqueue(PropagatorId::new(4))
				])
			);
			let mut bounds = FxHashSet::default();
			activation_list.for_each_activated_by(IntEvent::Bounds, |a: ActivationAction<_, _>| {
				bounds.insert(a);
			});
			assert_eq!(
				bounds,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropagatorId::new(1)),
					ActivationAction::Enqueue(PropagatorId::new(2)),
					ActivationAction::Enqueue(PropagatorId::new(3)),
					ActivationAction::Enqueue(PropagatorId::new(4))
				])
			);
			let mut lower_bound = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::LowerBound,
				|a: ActivationAction<_, _>| {
					lower_bound.insert(a);
				},
			);
			assert_eq!(
				lower_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropagatorId::new(1)),
					ActivationAction::Enqueue(PropagatorId::new(3)),
					ActivationAction::Enqueue(PropagatorId::new(4))
				])
			);
			let mut upper_bound = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::UpperBound,
				|a: ActivationAction<_, _>| {
					upper_bound.insert(a);
				},
			);
			assert_eq!(
				upper_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropagatorId::new(2)),
					ActivationAction::Enqueue(PropagatorId::new(3)),
					ActivationAction::Enqueue(PropagatorId::new(4))
				])
			);
			let mut domain = FxHashSet::default();
			activation_list.for_each_activated_by(IntEvent::Domain, |a: ActivationAction<_, _>| {
				domain.insert(a);
			});
			assert_eq!(
				domain,
				FxHashSet::from_iter([ActivationAction::Enqueue(PropagatorId::new(4))])
			);
		}
	}

	#[test]
	fn test_activation_list_remove() {
		let props = [
			(PropagatorId::new(0), IntPropCond::Fixed),
			(PropagatorId::new(1), IntPropCond::LowerBound),
			(PropagatorId::new(2), IntPropCond::UpperBound),
			(PropagatorId::new(3), IntPropCond::Bounds),
			(PropagatorId::new(4), IntPropCond::Domain),
		];
		let target =
			|prop| ActivationActionS::from(ActivationAction::<AdvisorId, _>::Enqueue(prop));

		for order in props.iter().permutations(props.len()) {
			let mut full = ActivationList::default();
			for &&(prop, cond) in &order {
				full.add(ActivationAction::<AdvisorId, _>::Enqueue(prop), cond);
			}

			for &&(prop, cond) in &order {
				// An activation is only ever found in the block of the condition
				// it subscribed with.
				for &(_, other) in props.iter().filter(|&&(_, c)| c != cond) {
					assert!(!full.clone().remove(other, |a| a == target(prop)));
				}

				let mut list = full.clone();
				assert!(list.remove(cond, |a| a == target(prop)));
				assert!(
					!list.remove(cond, |a| a == target(prop)),
					"{prop:?} was still subscribed after being removed"
				);
				let present = props
					.iter()
					.filter(|&&(p, _)| p != prop)
					.copied()
					.collect_vec();
				assert_activations(&list, &present);
			}

			// Removing every subscription empties the list.
			for &&(prop, cond) in &order {
				assert!(full.remove(cond, |a| a == target(prop)));
			}
			assert_activations(&full, &[]);
		}
	}
}
