//! List of pending elements whose "closed" status is undone when the solver
//! backtracks.

use std::ops::Range;

use crate::{
	DeepClone,
	actions::{ConstructionActions, Trailed, TrailingActions},
};

/// A list that partitions its elements into a *closed* prefix and an *open*
/// remainder, with the boundary trailed so that closing an element is undone
/// when the solver backtracks to before the close.
///
/// [`close`](Self::close) swaps the element being closed with the first open
/// element, so the operation is constant time but the order of elements is not
/// preserved. An element's position therefore changes over time, which is why
/// `close` reports every move through its `moved` callback: a caller that keeps
/// a reverse index into this list (as the difference logic graph does, where
/// each edge is a member of three of these lists) can keep it up to date.
///
/// Iterating [`open_indices`](Self::open_indices) while closing elements from
/// the same loop is sound: closing moves the element at the boundary — which
/// the loop has already passed — up to the position being closed, so no open
/// element is skipped or visited twice.
///
/// # Additions are permanent
///
/// [`push`](Self::push) appends outside the trail, so an element added during
/// search would survive backtracking. Only add elements at the root, i.e. while
/// building or simplifying a [`Model`](crate::model::Model).
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub(crate) struct TrailedOpenList<T> {
	/// The elements, of which `list[..closed]` is closed and the rest is open.
	list: Vec<T>,
	/// The trailed length of the closed prefix.
	closed: Trailed<usize>,
}

impl<T> TrailedOpenList<T> {
	/// The element at the given position, whether open or closed.
	///
	/// This is [`index`](Self::index) without the open check, for callers that
	/// cannot read the list's own trail; see
	/// [`open_indices_from`](Self::open_indices_from).
	pub(crate) fn at(&self, index: usize) -> &T {
		&self.list[index]
	}

	/// Close every open element.
	pub(crate) fn clear(&mut self, ctx: &mut (impl TrailingActions + ?Sized)) {
		let _ = ctx.set_trailed(self.closed, self.list.len());
	}

	/// Close the element at the given position, reporting each element that
	/// moved as a result to `moved` as `(element, new position)`. Returns
	/// whether the element was open, i.e. whether anything changed.
	pub(crate) fn close(
		&mut self,
		ctx: &mut (impl TrailingActions + ?Sized),
		index: usize,
		mut moved: impl FnMut(&T, usize),
	) -> bool {
		let boundary = ctx.trailed(self.closed);
		if index < boundary {
			return false;
		}
		if index > boundary {
			self.list.swap(index, boundary);
			moved(&self.list[boundary], boundary);
			moved(&self.list[index], index);
		}
		let _ = ctx.set_trailed(self.closed, boundary + 1);
		true
	}

	/// The trailed slot holding the length of the closed prefix, for callers
	/// that must read it off a trail other than the one they write. See
	/// [`open_indices_from`](Self::open_indices_from).
	pub(crate) fn closed_slot(&self) -> Trailed<usize> {
		self.closed
	}

	/// Create a list whose elements are all open.
	///
	/// Building a list this way needs no trail *writes* at all — useful where
	/// there is nothing to backtrack over yet, as when lowering a model into a
	/// solver.
	pub(crate) fn from_open(ctx: &mut (impl ConstructionActions + ?Sized), list: Vec<T>) -> Self {
		Self {
			closed: ctx.new_trailed(0_usize),
			list,
		}
	}

	/// The element at the given position, which must be open.
	pub(crate) fn index(&self, ctx: &(impl TrailingActions + ?Sized), index: usize) -> &T {
		self.index_opt(ctx, index)
			.expect("index refers to a closed element")
	}

	/// The element at the given position, or `None` if it has been closed.
	pub(crate) fn index_opt(
		&self,
		ctx: &(impl TrailingActions + ?Sized),
		index: usize,
	) -> Option<&T> {
		(index >= ctx.trailed(self.closed)).then(|| &self.list[index])
	}

	/// Whether no element is open.
	pub(crate) fn is_empty(&self, ctx: &(impl TrailingActions + ?Sized)) -> bool {
		self.num_open(ctx) == 0
	}

	/// Create an empty list.
	pub(crate) fn new(ctx: &mut (impl ConstructionActions + ?Sized)) -> Self {
		Self::from_open(ctx, Vec::new())
	}

	/// The number of open elements.
	pub(crate) fn num_open(&self, ctx: &(impl TrailingActions + ?Sized)) -> usize {
		self.list.len() - ctx.trailed(self.closed)
	}

	/// The positions of the open elements.
	pub(crate) fn open_indices(&self, ctx: &(impl TrailingActions + ?Sized)) -> Range<usize> {
		self.open_indices_from(ctx.trailed(self.closed))
	}

	/// The positions of the open elements given the length of the closed
	/// prefix.
	///
	/// This is [`open_indices`](Self::open_indices) for callers that cannot
	/// read the list's own trail, such as
	/// [`to_solver`](crate::constraints::Constraint::to_solver), which must
	/// read the boundary off the [`Model`](crate::model::Model) trail through
	/// [`LoweringContext::model_trailed`](crate::lower::LoweringContext::model_trailed)
	/// while writing the solver's. Pass a length read from
	/// [`closed_slot`](Self::closed_slot), and reach the elements with
	/// [`at`](Self::at).
	pub(crate) fn open_indices_from(&self, closed: usize) -> Range<usize> {
		closed..self.list.len()
	}

	/// Append an open element.
	///
	/// This addition is permanent; see the note on [`TrailedOpenList`].
	pub(crate) fn push(&mut self, value: T) {
		self.list.push(value);
	}

	/// The number of elements, open and closed.
	pub(crate) fn total_len(&self) -> usize {
		self.list.len()
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;

	use crate::{
		actions::TrailingActions,
		helpers::trailed_open_list::TrailedOpenList,
		model::Model,
		solver::{Solver, trail::Trail},
	};

	/// Collect the open elements of `list` in position order.
	fn open<T: Copy>(list: &TrailedOpenList<T>, ctx: &impl TrailingActions) -> Vec<T> {
		list.open_indices(ctx)
			.map(|i| *list.index(ctx, i))
			.collect_vec()
	}

	#[test]
	fn test_trailed_open_list_backtracking() {
		let mut slv: Solver = Solver::default();
		let mut list = TrailedOpenList::new(&mut slv);
		for i in 0..4 {
			list.push(i);
		}

		let mut handle = slv.engine.borrow_mut();
		let trail: &mut Trail = &mut handle.state.trail;
		assert!(list.close(trail, 0, |_, _| {}));

		trail.notify_new_decision_level();
		assert!(list.close(trail, 2, |_, _| {}));
		assert_eq!(open(&list, trail), vec![1, 3]);

		// Backtracking reopens the element closed at the deeper level, but not
		// the one closed before it.
		trail.notify_backtrack(0);
		assert_eq!(open(&list, trail), vec![2, 1, 3]);
	}

	#[test]
	fn test_trailed_open_list_close() {
		let mut prb = Model::default();
		let mut list = TrailedOpenList::new(&mut prb);
		for i in 0..4 {
			list.push(i);
		}
		assert_eq!(list.total_len(), 4);
		assert_eq!(list.num_open(&prb), 4);

		// Closing a position past the boundary swaps the boundary element into
		// it, so both elements are reported as moved.
		let mut moves = Vec::new();
		assert!(list.close(&mut prb, 2, |&elem, pos| moves.push((elem, pos))));
		assert_eq!(moves, vec![(2, 0), (0, 2)]);
		assert_eq!(list.num_open(&prb), 3);
		assert_eq!(open(&list, &prb), vec![1, 0, 3]);

		// Closing the boundary itself moves nothing.
		moves.clear();
		assert!(list.close(&mut prb, 1, |&elem, pos| moves.push((elem, pos))));
		assert!(moves.is_empty());
		assert_eq!(open(&list, &prb), vec![0, 3]);

		// Closing an already closed element is a no-op.
		assert!(!list.close(&mut prb, 0, |_, _| unreachable!()));
		assert_eq!(list.num_open(&prb), 2);
	}

	#[test]
	fn test_trailed_open_list_close_while_iterating() {
		let mut prb = Model::default();
		let mut list = TrailedOpenList::new(&mut prb);
		for i in 0..6 {
			list.push(i);
		}

		// Closing from within an iteration over the initial open range must
		// visit every element exactly once.
		let mut visited = Vec::new();
		for i in list.open_indices(&prb) {
			let elem = *list.index(&prb, i);
			visited.push(elem);
			if elem % 2 == 0 {
				assert!(list.close(&mut prb, i, |_, _| {}));
			}
		}
		visited.sort_unstable();
		assert_eq!(visited, vec![0, 1, 2, 3, 4, 5]);

		let mut remaining = open(&list, &prb);
		remaining.sort_unstable();
		assert_eq!(remaining, vec![1, 3, 5]);
	}

	#[test]
	fn test_trailed_open_list_index_opt() {
		let mut prb = Model::default();
		let mut list = TrailedOpenList::new(&mut prb);
		list.push('a');
		list.push('b');
		assert!(list.close(&mut prb, 0, |_, _| {}));

		assert_eq!(list.index_opt(&prb, 0), None);
		assert_eq!(list.index_opt(&prb, 1), Some(&'b'));

		list.clear(&mut prb);
		assert!(list.is_empty(&prb));
		assert_eq!(list.index_opt(&prb, 1), None);
		// Clearing only closes: the elements are still there.
		assert_eq!(list.total_len(), 2);
	}

	#[test]
	fn test_trailed_open_list_open_indices_from_matches() {
		let mut prb = Model::default();
		let mut list = TrailedOpenList::new(&mut prb);
		for i in 0..3 {
			list.push(i);
		}
		assert!(list.close(&mut prb, 1, |_, _| {}));

		let closed = prb.trailed(list.closed_slot());
		assert_eq!(
			list.open_indices_from(closed)
				.map(|i| *list.at(i))
				.collect_vec(),
			open(&list, &prb)
		);
	}
}
