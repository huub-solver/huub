//! Append-only list whose growth is undone on backtrack.
//!
//! [`TrailedList`] stores its active length as a [`Trailed`] value, so any
//! elements appended after a decision level boundary are automatically removed
//! when the solver backtracks past that boundary. Explicit removals
//! (`clear`/`swap_remove`) are *not* trailed and so persist across
//! backtracking; they must therefore only be performed when the caller has
//! decided that the removed elements will never become relevant again. The
//! flag `allow_removal` makes that intent explicit at construction time.

// The minimal difference-logic integration (without the diff-logic brancher and
// reservoir) does not yet exercise the removal and random-access methods of this
// complete, unit-tested API; suppress the resulting `dead_code` outside tests.
#![cfg_attr(
	not(test),
	expect(
		dead_code,
		reason = "complete trailed-list API; some methods are only used once the diff-logic brancher/reservoir are reintroduced"
	)
)]

use std::slice::Iter;

use crate::actions::{ConstructionActions, Trailed, TrailingActions};

/// An append-only list from which newly added elements are automatically
/// removed when the solver backtracks. Explicit removals can't be reverted and
/// are gated behind an `allow_removal` flag set at construction time.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TrailedList<T> {
	/// Whether [`Self::clear`] and the `swap_remove*` methods are permitted.
	allow_removal: bool,
	/// Underlying list. Elements beyond `size` are inactive slots that may be
	/// overwritten on the next [`Self::push`].
	list: Vec<T>,
	/// Length of the active part of the list.
	size: Trailed<usize>,
}

impl<T: PartialEq + Clone> TrailedList<T> {
	/// Remove all elements from the list. The operation is not reverted on
	/// backtrack; this method panics if `allow_removal` is `false`.
	pub(crate) fn clear<A: TrailingActions + ?Sized>(&self, actions: &mut A) {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let _ = actions.set_trailed(self.size, 0);
	}

	/// Return the element at the given (active) index.
	pub(crate) fn index<A: TrailingActions>(&self, actions: &A, index: usize) -> &T {
		let len = self.len(actions);
		assert!(index < len, "index out of bounds");
		&self.list[index]
	}

	/// Return `true` if no elements are currently active.
	pub(crate) fn is_empty<A: TrailingActions + ?Sized>(&self, actions: &A) -> bool {
		actions.trailed(self.size) == 0
	}

	/// Return an iterator over the active elements of the list.
	pub(crate) fn iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Iter<'_, T> {
		let len = self.len(actions);
		self.list[..len].iter()
	}

	/// Return the number of currently active elements in the list.
	pub(crate) fn len<A: TrailingActions + ?Sized>(&self, actions: &A) -> usize {
		actions.trailed(self.size)
	}

	/// Create a new empty list. `allow_removal` gates the `clear` and
	/// `swap_remove*` operations.
	pub(crate) fn new<A: ConstructionActions + ?Sized>(
		actions: &mut A,
		allow_removal: bool,
	) -> Self {
		Self {
			list: Vec::new(),
			size: actions.new_trailed(0),
			allow_removal,
		}
	}

	/// Append an element to the active portion of the list. Backtracking past
	/// the current decision level will undo this push.
	pub(crate) fn push<A: TrailingActions + ?Sized>(&mut self, actions: &mut A, value: T) {
		let len = self.len(actions);
		if len < self.list.len() {
			// The slot exists in the underlying storage from a previous
			// backtrack — reuse it instead of growing the `Vec`.
			self.list[len] = value;
		} else {
			self.list.push(value);
		}
		let prev = actions.set_trailed(self.size, len + 1);
		debug_assert_eq!(prev, len);
	}

	/// Remove the element at the given index by swapping the active tail into
	/// its place. The removal is not reverted on backtrack; this method panics
	/// if `allow_removal` is `false`.
	pub(crate) fn swap_remove<A: TrailingActions>(&mut self, actions: &mut A, index: usize) -> &T {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let len = self.len(actions);
		assert!(index < len, "index {index} out of bounds {len}");
		self.list.swap(index, len - 1);
		let _ = actions.set_trailed(self.size, len - 1);
		&self.list[len - 1]
	}

	/// Remove the first active occurrence of the given element by swapping it
	/// out of the active range. The removal is not reverted on backtrack;
	/// this method panics if `allow_removal` is `false`, or if the element is
	/// not currently in the active range.
	pub(crate) fn swap_remove_element<A: TrailingActions>(
		&mut self,
		actions: &mut A,
		element: &T,
	) -> &T {
		assert!(self.allow_removal, "removal is not allowed for this list");
		let len = self.len(actions);
		let index = self
			.list
			.iter()
			.take(len)
			.position(|x| *x == *element)
			.expect("element not present in the active list");
		self.swap_remove(actions, index)
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		actions::{ConstructionActions, Trailed, TrailingActions},
		helpers::{bytes::Bytes, trailed_list::TrailedList},
		solver::trail::Trail,
	};

	/// Test harness wrapping a [`Trail`] with the three action traits that
	/// `TrailedList` needs. The struct also exposes `push_level` and
	/// `pop_level` so that backtrack-sensitive tests can be written without
	/// dragging in the full solver.
	struct StubCtx {
		trail: Trail,
	}

	#[test]
	#[should_panic(expected = "removal is not allowed")]
	fn clear_panics_when_removal_disallowed() {
		let mut ctx = StubCtx::new();
		let list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.clear(&mut ctx);
	}

	#[test]
	fn clear_truncates_active_range_when_allowed() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, true);
		list.push(&mut ctx, 1);
		list.push(&mut ctx, 2);
		list.push(&mut ctx, 3);
		list.clear(&mut ctx);

		assert!(list.is_empty(&ctx));
		assert_eq!(list.len(&ctx), 0);

		// A subsequent push reuses the existing slot.
		list.push(&mut ctx, 99);
		assert_eq!(list.iter(&ctx).copied().collect::<Vec<_>>(), vec![99]);
	}

	#[test]
	#[should_panic(expected = "index out of bounds")]
	fn index_out_of_bounds_panics() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 1);
		let _ = list.index(&ctx, 1);
	}

	#[test]
	fn nested_backtracks_restore_correct_level() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 1);

		ctx.push_level(); // level 1
		list.push(&mut ctx, 2);

		ctx.push_level(); // level 2
		list.push(&mut ctx, 3);
		list.push(&mut ctx, 4);
		assert_eq!(list.len(&ctx), 4);

		ctx.pop_level(1);
		assert_eq!(list.len(&ctx), 2);
		assert_eq!(list.iter(&ctx).copied().collect::<Vec<_>>(), vec![1, 2]);

		ctx.pop_level(0);
		assert_eq!(list.len(&ctx), 1);
		assert_eq!(list.iter(&ctx).copied().collect::<Vec<_>>(), vec![1]);
	}

	#[test]
	fn new_list_is_empty() {
		let mut ctx = StubCtx::new();
		let list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		assert!(list.is_empty(&ctx));
		assert_eq!(list.len(&ctx), 0);
		assert_eq!(
			list.iter(&ctx).copied().collect::<Vec<_>>(),
			Vec::<i32>::new()
		);
	}

	#[test]
	fn push_then_index_and_iter() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 10);
		list.push(&mut ctx, 20);
		list.push(&mut ctx, 30);

		assert_eq!(list.len(&ctx), 3);
		assert!(!list.is_empty(&ctx));
		assert_eq!(*list.index(&ctx, 0), 10);
		assert_eq!(*list.index(&ctx, 1), 20);
		assert_eq!(*list.index(&ctx, 2), 30);
		assert_eq!(
			list.iter(&ctx).copied().collect::<Vec<_>>(),
			vec![10, 20, 30]
		);
	}

	#[test]
	fn pushes_after_decision_level_undo_on_backtrack() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 1);
		list.push(&mut ctx, 2);

		// Level 1: add more items, then backtrack to level 0.
		ctx.push_level();
		list.push(&mut ctx, 3);
		list.push(&mut ctx, 4);
		assert_eq!(list.len(&ctx), 4);

		ctx.pop_level(0);
		assert_eq!(list.len(&ctx), 2);
		assert_eq!(list.iter(&ctx).copied().collect::<Vec<_>>(), vec![1, 2]);

		// The underlying storage slots should be reused on the next push
		// rather than the vector being regrown.
		list.push(&mut ctx, 5);
		assert_eq!(list.len(&ctx), 3);
		assert_eq!(*list.index(&ctx, 2), 5);
	}

	#[test]
	fn swap_remove_at_decision_level_is_unsafe_to_undo() {
		// Documents the invariant the propagator must respect: `swap_remove`
		// must not be called inside a search node that may later backtrack,
		// because the size is trailed (and would revert) but the swapped
		// list contents are not.
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, true);
		list.push(&mut ctx, 10);
		list.push(&mut ctx, 20);
		list.push(&mut ctx, 30);
		list.push(&mut ctx, 40);

		ctx.push_level();
		let _ = list.swap_remove(&mut ctx, 1);
		assert_eq!(
			list.iter(&ctx).copied().collect::<Vec<_>>(),
			vec![10, 40, 30]
		);

		// On backtrack, the trailed size restores to 4 — but the underlying
		// vector is still in its post-swap order, so 20 has been lost. This
		// behaviour is intentional and is the reason `allow_removal` is gated.
		ctx.pop_level(0);
		assert_eq!(
			list.iter(&ctx).copied().collect::<Vec<_>>(),
			vec![10, 40, 30, 20]
		);
	}

	#[test]
	fn swap_remove_element_finds_first_match() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, true);
		list.push(&mut ctx, 1);
		list.push(&mut ctx, 2);
		list.push(&mut ctx, 3);
		list.push(&mut ctx, 2); // Duplicate value, but only the first match removes.

		let _ = list.swap_remove_element(&mut ctx, &2);
		// After swap_remove(1): list becomes [1, 2 (last), 3], so the
		// duplicate 2 has been promoted from the tail.
		assert_eq!(list.iter(&ctx).copied().collect::<Vec<_>>(), vec![1, 2, 3]);
	}

	#[test]
	#[should_panic(expected = "element not present")]
	fn swap_remove_element_panics_when_absent() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, true);
		list.push(&mut ctx, 1);
		let _ = list.swap_remove_element(&mut ctx, &99);
	}

	#[test]
	#[should_panic(expected = "removal is not allowed")]
	fn swap_remove_element_panics_when_removal_disallowed() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 1);
		let _ = list.swap_remove_element(&mut ctx, &1);
	}

	#[test]
	#[should_panic(expected = "removal is not allowed")]
	fn swap_remove_panics_when_removal_disallowed() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, false);
		list.push(&mut ctx, 1);
		let _ = list.swap_remove(&mut ctx, 0);
	}

	#[test]
	fn swap_remove_when_allowed_returns_removed_element() {
		// `swap_remove` is intended for irreversible reductions performed
		// before any decision levels have been opened (e.g. model-stage graph
		// simplification). It rewrites the active region in place and returns
		// the removed element.
		let mut ctx = StubCtx::new();
		let mut list: TrailedList<i32> = TrailedList::new(&mut ctx, true);
		list.push(&mut ctx, 10);
		list.push(&mut ctx, 20);
		list.push(&mut ctx, 30);
		list.push(&mut ctx, 40);

		// Removes 20 by swapping the tail (40) into its slot. The method
		// returns the removed element, mirroring `Vec::swap_remove`.
		let removed = *list.swap_remove(&mut ctx, 1);
		assert_eq!(removed, 20);
		assert_eq!(
			list.iter(&ctx).copied().collect::<Vec<_>>(),
			vec![10, 40, 30]
		);
	}

	impl StubCtx {
		fn new() -> Self {
			Self {
				trail: Trail::default(),
			}
		}

		fn pop_level(&mut self, level: usize) {
			self.trail.notify_backtrack(level);
		}

		fn push_level(&mut self) {
			self.trail.notify_new_decision_level();
		}
	}

	impl ConstructionActions for StubCtx {
		fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
			self.trail.track(init)
		}
	}

	impl TrailingActions for StubCtx {
		fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
			self.trail.set_trailed(i, v)
		}

		fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
			self.trail.trailed(i)
		}
	}
}
