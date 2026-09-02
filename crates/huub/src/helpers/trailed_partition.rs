//! Backtrackable disjoint-set partition over `{0, .., n-1}`.
//!
//! Each block is a contiguous slice of [`TrailedPartition::elems`]; block
//! membership is maintained across search by trailed per-position slots so it
//! is restored automatically on backtrack. The data structure is generic in
//! what `{0..n}` means — its first consumer (`IntUniqueDomain`) uses variable
//! indices, but nothing here depends on that interpretation.

use std::cmp;

use crate::{
	DeepClone,
	actions::{ConstructionActions, Trailed, TrailingActions},
};

/// Backtrackable disjoint-set partition of `{0, .., n-1}`. Each block is a
/// contiguous slice of the underlying element permutation (see
/// [`Self::elements`]). Block membership is maintained during search by a
/// trailed per-position layout slot.
///
/// The layout uses a dual encoding, indexed by position in the permutation:
///
/// - if position `p` is the **root** (smallest position) of its block, the slot
///   stores the block's exclusive end position;
/// - otherwise the slot stores the root position of `p`'s block.
///
/// Example with 4 elements partitioned into `{0,2}` (positions 0..2) and
/// `{1,3}` (positions 2..4):
///
/// ```text
///   pos:           0  1  2  3
///   elements():    0  2  1  3
///   positions:     0  2  1  3
///   layout:        2  0  4  2     // pos 0 -> end 2; pos 2 -> end 4
/// ```
#[derive(Clone, Debug, DeepClone)]
pub(crate) struct TrailedPartition {
	/// Permutation of `0..n` whose contiguous slices are the current blocks.
	elems: Vec<usize>,
	/// Inverse permutation: `elems[positions[i]] == i` for every `i`.
	positions: Vec<usize>,
	/// Per-position trailed slot (see struct doc for dual encoding).
	layout: Vec<Trailed<i64>>,
}

impl TrailedPartition {
	/// Exclusive end position of the block rooted at `root`. Caller must pass
	/// the block's root position or otherwise results are meaningless.
	pub(crate) fn block_end(&self, ctx: &impl TrailingActions, root: usize) -> usize {
		debug_assert_eq!(
			self.block_root(ctx, self.elems[root]),
			root,
			"block_end called with a non-root position"
		);
		ctx.trailed::<i64>(self.layout[root]) as usize
	}

	/// Root position of the block containing `elem`.
	pub(crate) fn block_root(&self, ctx: &impl TrailingActions, elem: usize) -> usize {
		let pos = self.positions[elem];
		let info = ctx.trailed::<i64>(self.layout[pos]) as usize;
		cmp::min(info, pos)
	}

	/// The element permutation, as a slice. Contiguous sub-slices correspond
	/// to the current blocks (see [`Self::block_root`] / [`Self::block_end`]
	/// to find their boundaries).
	pub(crate) fn elements(&self) -> &[usize] {
		&self.elems
	}

	/// Create a partition over the elements `0..n`, all initially in a single
	/// block. Allocates the `n` trailed layout slots through `ctx`, encoding
	/// the single-block start state (root at position 0 with end position `n`).
	pub(crate) fn new<C: ConstructionActions + ?Sized>(ctx: &mut C, n: usize) -> Self {
		let layout: Vec<Trailed<i64>> = (0..n)
			.map(|i| ctx.new_trailed::<i64>(if i == 0 { n as i64 } else { 0 }))
			.collect();
		Self {
			elems: (0..n).collect(),
			positions: (0..n).collect(),
			layout,
		}
	}

	/// Split the listed `elems` (all of which must currently belong to the
	/// same block) out into a new block. Returns `(orig_root, Some(new_root))`,
	/// or `(orig_root, None)` if every member of the original block was moved.
	pub(crate) fn split_off(
		&mut self,
		ctx: &mut impl TrailingActions,
		elems: &[usize],
	) -> (usize, Option<usize>) {
		let orig_root = self.block_root(ctx, elems[0]);
		let orig_end = self.block_end(ctx, orig_root);
		debug_assert!(elems.iter().all(|&i| self.block_root(ctx, i) == orig_root));
		if elems.len() == (orig_end - orig_root) {
			return (orig_root, None);
		}

		let mut new_end = orig_end;
		for &elem in elems {
			let pos = self.positions[elem];
			let swap_pos = new_end - 1;
			let swap_ele = self.elems[swap_pos];
			self.elems[pos] = swap_ele;
			self.elems[swap_pos] = elem;
			self.positions[elem] = swap_pos;
			self.positions[swap_ele] = pos;
			new_end -= 1;
			debug_assert!(new_end >= orig_root);
		}

		let new_root = new_end;
		for &elem in elems {
			let pos = self.positions[elem];
			let _ = ctx.set_trailed::<i64>(
				self.layout[pos],
				if pos == new_root {
					(new_root + elems.len()) as i64
				} else {
					new_root as i64
				},
			);
		}
		let _ = ctx.set_trailed::<i64>(self.layout[orig_root], new_end as i64);
		(orig_root, Some(new_root))
	}
}
