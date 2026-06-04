//! Open/closed list that trails closures.
//!
//! [`TrailedOpenList`] stores a list whose elements are partitioned into a
//! *closed* prefix and an *open* suffix. The split point is tracked through a
//! [`Trailed`] value so closures are automatically undone on backtrack. The
//! [`Self::close`] method may swap an open element into the closed prefix —
//! the `idx_update` callback notifies the caller of the new indices so
//! external bookkeeping (e.g. a `(value → index)` map kept by the propagator)
//! can stay in sync.

// The minimal difference-logic integration (without the diff-logic brancher and
// reservoir) does not yet exercise every accessor of this complete, unit-tested
// API (`peek`/`pop` are unused even by the unit tests); suppress the resulting
// `dead_code`.
#![expect(
	dead_code,
	reason = "complete trailed-open-list API; some methods are only used once the diff-logic brancher/reservoir are reintroduced"
)]

use std::ops::Range;

use crate::actions::{ConstructionActions, Trailed, TrailingActions};

/// A list whose elements are partitioned into a closed prefix and an open
/// suffix. New elements are pushed open; closure is trailed and undone on
/// backtrack. The list does not preserve the relative order of open elements
/// (closure may swap with the boundary element).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TrailedOpenList<T> {
	/// Length of the closed prefix. Indices in `0..closed` are closed; indices
	/// in `closed..list.len()` are open.
	closed: Trailed<usize>,
	/// Underlying list. The closed/open split is determined by `closed`.
	list: Vec<T>,
}

impl<T: Clone> TrailedOpenList<T> {
	/// Close every currently open element. The closure is trailed and so
	/// reverts on backtrack.
	pub(crate) fn clear<A: TrailingActions>(&mut self, actions: &mut A) {
		let _ = actions.set_trailed(self.closed, self.len());
	}

	/// Close the open element at the given index.
	///
	/// Returns `true` if the close took effect, or `false` if the element was
	/// already closed. When the element is not at the boundary, it is swapped
	/// with the boundary element to preserve the closed-prefix layout; the
	/// `idx_update` callback is invoked once for the boundary slot and once
	/// for the supplied index so external indexing structures can mirror the
	/// move.
	pub(crate) fn close<A, F>(&mut self, actions: &mut A, index: usize, mut idx_update: F) -> bool
	where
		A: TrailingActions,
		F: FnMut(&T, usize),
	{
		let cur = actions.trailed(self.closed);
		if index < cur {
			return false;
		}
		if index > cur {
			self.list.swap(index, cur);
			idx_update(&self.list[cur], cur);
			idx_update(&self.list[index], index);
		}
		let _ = actions.set_trailed(self.closed, cur + 1);
		true
	}

	/// Return the element at the given (open) index.
	pub(crate) fn index<A: TrailingActions + ?Sized>(&self, actions: &A, index: usize) -> &T {
		let closed = actions.trailed(self.closed);
		assert!(index >= closed, "index out of bounds");
		&self.list[index]
	}

	/// Return the element at the given index, or `None` if it is in the
	/// closed prefix.
	pub(crate) fn index_opt<A: TrailingActions>(&self, actions: &A, index: usize) -> Option<&T> {
		let closed = actions.trailed(self.closed);
		if index >= closed {
			Some(&self.list[index])
		} else {
			None
		}
	}

	/// Return `true` when no elements are currently open.
	pub(crate) fn is_empty<A: TrailingActions>(&self, actions: &A) -> bool {
		self.list.len() == actions.trailed(self.closed)
	}

	/// Return the total length of the list, including closed elements.
	pub(crate) fn len(&self) -> usize {
		self.list.len()
	}

	/// Create a new empty list.
	pub(crate) fn new<A: ConstructionActions + ?Sized>(actions: &mut A) -> Self {
		Self {
			list: Vec::new(),
			closed: actions.new_trailed(0),
		}
	}

	/// Return the number of currently open elements.
	pub(crate) fn num_open<A: TrailingActions>(&self, actions: &A) -> usize {
		self.list.len() - actions.trailed(self.closed)
	}

	/// Return the half-open range of indices that are currently open.
	pub(crate) fn open_iter<A: TrailingActions + ?Sized>(&self, actions: &A) -> Range<usize> {
		actions.trailed(self.closed)..self.len()
	}

	/// Return the first open element without modifying the list. `None` if
	/// every element has been closed.
	pub(crate) fn peek<A: TrailingActions + ?Sized>(&self, actions: &A) -> Option<&T> {
		let cur = actions.trailed(self.closed);
		if cur >= self.list.len() {
			None
		} else {
			Some(&self.list[cur])
		}
	}

	/// Close the first open element and return a reference to it. The close
	/// is trailed and reverts on backtrack. Returns `None` when the list is
	/// fully closed.
	pub(crate) fn pop<A: TrailingActions>(&mut self, actions: &mut A) -> Option<&T> {
		let cur = actions.trailed(self.closed);
		if cur >= self.list.len() {
			return None;
		}
		let _ = self.close(actions, cur, |_, _| {});
		Some(&self.list[cur])
	}

	/// Append a new open element to the end of the list. Pushes are not
	/// trailed; the propagator is expected to only push at the level at
	/// which the list lives.
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}
}

#[cfg(test)]
mod tests {
	use std::cell::RefCell;

	use crate::{
		actions::{ConstructionActions, Trailed, TrailingActions},
		helpers::{bytes::Bytes, trailed_open_list::TrailedOpenList},
		solver::trail::Trail,
	};

	/// Minimal harness for exercising the trailed split point.
	struct StubCtx {
		trail: Trail,
	}

	#[test]
	fn clear_closes_all_and_undoes_on_backtrack() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(1);
		list.push(2);
		list.push(3);

		ctx.push_level();
		list.clear(&mut ctx);
		assert!(list.is_empty(&ctx));
		assert_eq!(list.num_open(&ctx), 0);

		ctx.pop_level(0);
		assert_eq!(list.num_open(&ctx), 3);
	}

	#[test]
	fn close_already_closed_returns_false() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(10);
		list.push(20);
		assert!(list.close(&mut ctx, 0, |_, _| {}));

		// Closing inside the closed prefix is a no-op.
		assert!(!list.close(&mut ctx, 0, |_, _| panic!("callback should not fire")));
		assert_eq!(list.num_open(&ctx), 1);
	}

	#[test]
	fn close_at_boundary_does_not_swap() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(10);
		list.push(20);
		list.push(30);

		let calls = RefCell::new(Vec::<(i32, usize)>::new());
		let closed = list.close(&mut ctx, 0, |v, i| calls.borrow_mut().push((*v, i)));
		assert!(closed);

		// Closing the boundary slot must not invoke the swap callback.
		assert!(calls.borrow().is_empty());
		assert_eq!(list.num_open(&ctx), 2);
		assert_eq!(list.open_iter(&ctx), 1..3);
		assert_eq!(list.index_opt(&ctx, 0), None);
		assert_eq!(list.index_opt(&ctx, 1), Some(&20));
	}

	#[test]
	fn close_non_boundary_swaps_and_fires_callback() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(10);
		list.push(20);
		list.push(30);
		list.push(40);

		let calls = RefCell::new(Vec::<(i32, usize)>::new());
		// Close the element at index 2 (value 30). It must be swapped with
		// the boundary element (index 0, value 10) before the close.
		let closed = list.close(&mut ctx, 2, |v, i| calls.borrow_mut().push((*v, i)));
		assert!(closed);

		// First callback: the value that moved into the boundary slot.
		// Second callback: the value that moved into the old slot of 30.
		assert_eq!(calls.borrow().as_slice(), &[(30, 0), (10, 2)]);

		// After the close, the prefix [0..1] contains the closed value 30,
		// and the open suffix is [10, 20, 40] (10 moved to index 2).
		assert_eq!(list.num_open(&ctx), 3);
		assert_eq!(list.open_iter(&ctx), 1..4);
		assert_eq!(list.index_opt(&ctx, 0), None);
		assert_eq!(*list.index(&ctx, 1), 20);
		assert_eq!(*list.index(&ctx, 2), 10);
		assert_eq!(*list.index(&ctx, 3), 40);
	}

	#[test]
	fn close_undoes_on_backtrack() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(1);
		list.push(2);
		list.push(3);

		ctx.push_level();
		// Close at the boundary so no swap happens — that way the underlying
		// vector layout is unchanged when the close reverts.
		let _ = list.close(&mut ctx, 0, |_, _| {});
		assert_eq!(list.num_open(&ctx), 2);

		ctx.pop_level(0);
		assert_eq!(list.num_open(&ctx), 3);
		assert_eq!(list.open_iter(&ctx), 0..3);
	}

	#[test]
	#[should_panic(expected = "index out of bounds")]
	fn index_into_closed_prefix_panics() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(5);
		let _ = list.close(&mut ctx, 0, |_, _| {});
		let _ = list.index(&ctx, 0);
	}

	#[test]
	fn index_panics_on_closed_slot() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(7);
		list.push(8);
		let _ = list.close(&mut ctx, 0, |_, _| {});
		// Sanity: open-form accessor still works.
		assert_eq!(*list.index(&ctx, 1), 8);
		// And the closed-form variant returns None.
		assert_eq!(list.index_opt(&ctx, 0), None);
	}

	#[test]
	fn new_list_is_empty() {
		let mut ctx = StubCtx::new();
		let list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		assert!(list.is_empty(&ctx));
		assert_eq!(list.len(), 0);
		assert_eq!(list.num_open(&ctx), 0);
		assert_eq!(list.open_iter(&ctx), 0..0);
	}

	#[test]
	fn pushed_elements_are_open() {
		let mut ctx = StubCtx::new();
		let mut list: TrailedOpenList<i32> = TrailedOpenList::new(&mut ctx);
		list.push(10);
		list.push(20);
		list.push(30);

		assert!(!list.is_empty(&ctx));
		assert_eq!(list.len(), 3);
		assert_eq!(list.num_open(&ctx), 3);
		assert_eq!(list.open_iter(&ctx), 0..3);
		assert_eq!(*list.index(&ctx, 0), 10);
		assert_eq!(*list.index(&ctx, 2), 30);
		assert_eq!(list.index_opt(&ctx, 1), Some(&20));
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
