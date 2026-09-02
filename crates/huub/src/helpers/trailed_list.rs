//! Append-only list whose additions are undone when the solver backtracks.

use std::slice::Iter;

use crate::{
	DeepClone,
	actions::{ConstructionActions, Trailed, TrailingActions},
};

/// A list whose *active* prefix is delimited by a trailed length, so that
/// elements appended during search disappear again when the solver backtracks
/// to before the append.
///
/// Elements beyond the active prefix are not dropped, only ignored: a later
/// [`push`](Self::push) overwrites them.
///
/// # Removal is permanent
///
/// [`clear`](Self::clear), [`swap_remove`](Self::swap_remove), and
/// [`swap_remove_element`](Self::swap_remove_element) shrink the active prefix
/// and leave the removed element where a later push will overwrite it. Growing
/// the prefix back on backtracking would therefore resurrect whichever element
/// happens to occupy the slot, so these methods may only be used at the root,
/// i.e. while simplifying a [`Model`](crate::model::Model), never during
/// search.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub(crate) struct TrailedList<T> {
	/// The elements, of which only `list[..len]` is active.
	list: Vec<T>,
	/// The trailed length of the active prefix.
	len: Trailed<usize>,
}

impl<T> TrailedList<T> {
	/// Shorten the active prefix to nothing.
	///
	/// This removal is permanent; see the note on [`TrailedList`].
	pub(crate) fn clear(&self, ctx: &mut (impl TrailingActions + ?Sized)) {
		let _ = ctx.set_trailed(self.len, 0);
	}

	/// Create a list whose elements are all active.
	///
	/// The trailed length starts at the full length, so building a list this
	/// way needs no trail *writes* at all — useful where there is nothing to
	/// backtrack over yet, as when lowering a model into a solver.
	pub(crate) fn from_active(ctx: &mut (impl ConstructionActions + ?Sized), list: Vec<T>) -> Self {
		Self {
			len: ctx.new_trailed(list.len()),
			list,
		}
	}

	/// The element at the given position in the active prefix.
	pub(crate) fn index(&self, ctx: &(impl TrailingActions + ?Sized), index: usize) -> &T {
		let len = self.len(ctx);
		assert!(index < len, "index {index} out of bounds {len}");
		&self.list[index]
	}

	/// Whether the active prefix is empty.
	pub(crate) fn is_empty(&self, ctx: &(impl TrailingActions + ?Sized)) -> bool {
		self.len(ctx) == 0
	}

	/// Iterate over the active prefix.
	pub(crate) fn iter(&self, ctx: &(impl TrailingActions + ?Sized)) -> Iter<'_, T> {
		self.iter_upto(self.len(ctx))
	}

	/// Iterate over the first `len` elements.
	///
	/// This is [`iter`](Self::iter) for callers that cannot read the list's own
	/// trail, such as
	/// [`to_solver`](crate::constraints::Constraint::to_solver), which must
	/// read a length off the [`Model`](crate::model::Model) trail through
	/// [`LoweringContext::model_trailed`](crate::lower::LoweringContext::model_trailed)
	/// while writing the solver's. Pass a length read from
	/// [`len_slot`](Self::len_slot).
	pub(crate) fn iter_upto(&self, len: usize) -> Iter<'_, T> {
		self.list[..len].iter()
	}

	/// The length of the active prefix.
	pub(crate) fn len(&self, ctx: &(impl TrailingActions + ?Sized)) -> usize {
		ctx.trailed(self.len)
	}

	/// The trailed slot holding the length of the active prefix, for callers
	/// that must read it off a trail other than the one they write. See
	/// [`iter_upto`](Self::iter_upto).
	pub(crate) fn len_slot(&self) -> Trailed<usize> {
		self.len
	}

	/// Create an empty list.
	pub(crate) fn new(ctx: &mut (impl ConstructionActions + ?Sized)) -> Self {
		Self::from_active(ctx, Vec::new())
	}

	/// Append an element to the active prefix, overwriting any inactive
	/// element in its slot.
	pub(crate) fn push(&mut self, ctx: &mut (impl TrailingActions + ?Sized), value: T) {
		let len = self.len(ctx);
		if len < self.list.len() {
			self.list[len] = value;
		} else {
			self.list.push(value);
		}
		let prev = ctx.set_trailed(self.len, len + 1);
		debug_assert_eq!(prev, len);
	}

	/// Remove the element at the given position by swapping the last active
	/// element into its place.
	///
	/// This removal is permanent; see the note on [`TrailedList`].
	pub(crate) fn swap_remove(&mut self, ctx: &mut (impl TrailingActions + ?Sized), index: usize) {
		let len = self.len(ctx);
		assert!(index < len, "index {index} out of bounds {len}");
		self.list.swap(index, len - 1);
		let _ = ctx.set_trailed(self.len, len - 1);
	}
}

impl<T: PartialEq> TrailedList<T> {
	/// Remove the given element by swapping the last active element into its
	/// place. Panics if the element is not active.
	///
	/// The active prefix carries no reverse index, so this scans it. Callers
	/// that already know the position should use
	/// [`swap_remove`](Self::swap_remove) instead.
	///
	/// This removal is permanent; see the note on [`TrailedList`].
	pub(crate) fn swap_remove_element(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		element: &T,
	) {
		let len = self.len(ctx);
		let index = self.list[..len]
			.iter()
			.position(|x| x == element)
			.expect("element to remove is not in the active prefix");
		self.swap_remove(ctx, index);
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;

	use crate::{
		actions::TrailingActions,
		helpers::trailed_list::TrailedList,
		model::Model,
		solver::{Solver, trail::Trail},
	};

	#[test]
	fn test_trailed_list_backtracking() {
		let mut slv: Solver = Solver::default();
		let mut list = TrailedList::new(&mut slv);
		list.push(&mut slv, 1);

		let mut handle = slv.engine.borrow_mut();
		let trail: &mut Trail = &mut handle.state.trail;
		trail.notify_new_decision_level();
		list.push(trail, 2);
		list.push(trail, 3);
		assert_eq!(list.iter(trail).copied().collect_vec(), vec![1, 2, 3]);

		// Backtracking restores the length, dropping the elements appended at
		// the deeper level.
		trail.notify_backtrack(0);
		assert_eq!(list.iter(trail).copied().collect_vec(), vec![1]);

		// The slots the dropped elements occupied are reused, not appended to.
		list.push(trail, 4);
		assert_eq!(list.iter(trail).copied().collect_vec(), vec![1, 4]);
	}

	#[test]
	fn test_trailed_list_iter_upto_matches_iter() {
		let mut prb = Model::default();
		let mut list = TrailedList::new(&mut prb);
		for i in 0..4 {
			list.push(&mut prb, i);
		}
		list.swap_remove(&mut prb, 1);

		let len = prb.trailed(list.len_slot());
		assert_eq!(
			list.iter_upto(len).copied().collect_vec(),
			list.iter(&prb).copied().collect_vec()
		);
	}

	#[test]
	fn test_trailed_list_push_and_index() {
		let mut prb = Model::default();
		let mut list = TrailedList::new(&mut prb);
		assert!(list.is_empty(&prb));

		for i in 0..3 {
			list.push(&mut prb, i * 10);
		}
		assert_eq!(list.len(&prb), 3);
		assert!(!list.is_empty(&prb));
		assert_eq!(*list.index(&prb, 1), 10);
		assert_eq!(list.iter(&prb).copied().collect_vec(), vec![0, 10, 20]);

		list.clear(&mut prb);
		assert!(list.is_empty(&prb));
		assert_eq!(list.iter(&prb).next(), None);
	}

	#[test]
	fn test_trailed_list_swap_remove() {
		let mut prb = Model::default();
		let mut list = TrailedList::new(&mut prb);
		for i in 0..4 {
			list.push(&mut prb, i);
		}

		// The last active element takes the removed element's place, so the
		// order of the remaining elements is not preserved.
		list.swap_remove(&mut prb, 1);
		assert_eq!(list.iter(&prb).copied().collect_vec(), vec![0, 3, 2]);

		list.swap_remove_element(&mut prb, &0);
		assert_eq!(list.iter(&prb).copied().collect_vec(), vec![2, 3]);
	}

	#[test]
	#[should_panic(expected = "element to remove is not in the active prefix")]
	fn test_trailed_list_swap_remove_inactive_element() {
		let mut prb = Model::default();
		let mut list = TrailedList::new(&mut prb);
		list.push(&mut prb, 0);
		list.push(&mut prb, 1);
		list.swap_remove(&mut prb, 1);

		// `1` is still in the backing storage, but no longer active.
		list.swap_remove_element(&mut prb, &1);
	}
}
