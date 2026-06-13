//! The successor-variable graph shared by the `check`, `prevent`, and `scc`
//! circuit propagators, with the node/value/edge translation and the
//! explanation-literal (`push_*`) builders.

use crate::{
	IntVal,
	actions::{IntDecisionActions, IntInspectionActions, PropagationActions, ReasoningContext},
	solver::IntLitMeaning,
};

/// The successor-variable graph the circuit propagators reason over: one
/// successor variable per node position `0..n`, plus the value `offset` and the
/// `subcircuit` flag. Node/value/edge translation and the explanation-literal
/// (`push_*`) builders are methods here, so algorithms borrow it immutably
/// while mutating their own scratch.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct CircuitGraph<I> {
	/// Successor variables, indexed by node position `0..n`.
	pub(crate) vars: Vec<I>,
	/// Successor value of node `0` (`vars[i] == offset + j` -> `i`'s successor
	/// is `j`).
	pub(crate) offset: IntVal,
	/// Whether this is the `subcircuit` variant.
	pub(crate) subcircuit: bool,
}

impl<I> CircuitGraph<I> {
	/// The successor value that represents node `pos` pointing at node `to`.
	#[inline]
	pub(crate) fn edge_val(&self, to: usize) -> IntVal {
		self.offset + to as IntVal
	}

	/// Fill `out` with the successor position of every fixed node (`None` for
	/// unfixed), reusing `out`'s allocation.
	pub(crate) fn fixed_successors<C>(&self, ctx: &C, out: &mut Vec<Option<usize>>)
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
	{
		out.clear();
		out.extend((0..self.n()).map(|i| self.vars[i].val(ctx).and_then(|v| self.val_to_pos(v))));
	}

	/// Whether node `k` is *forced into* the cycle: it cannot take itself as
	/// successor, so every solution must route the single cycle through `k`.
	#[inline]
	pub(crate) fn forced_in<C>(&self, ctx: &C, k: usize) -> bool
	where
		C: PropagationActions,
		I: IntInspectionActions<C>,
	{
		!self.vars[k].in_domain(ctx, self.edge_val(k))
	}

	/// Number of nodes.
	#[inline]
	pub(crate) fn n(&self) -> usize {
		self.vars.len()
	}

	/// Create a new successor graph.
	pub(crate) fn new(vars: Vec<I>, offset: IntVal, subcircuit: bool) -> Self {
		Self {
			vars,
			offset,
			subcircuit,
		}
	}

	/// Push the currently-true literal explaining `x_i != val` (edge `i → val`
	/// absent), in the form carrying the correct decision level: a bound
	/// literal when `val` is outside `[min, max]`, else the `NotEq` hole
	/// literal. A bare `NotEq` can be true yet stale-levelled after a bound
	/// move, making the explanation non-asserting (cf. [`Self::push_fixed`]).
	#[inline]
	pub(crate) fn push_absent<C>(&self, out: &mut Vec<C::Atom>, i: usize, val: IntVal, ctx: &mut C)
	where
		C: ReasoningContext + ?Sized,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		let (lb, ub) = self.vars[i].bounds(ctx);
		if val < lb {
			out.push(self.vars[i].min_lit(ctx));
		} else if val > ub {
			out.push(self.vars[i].max_lit(ctx));
		} else {
			out.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(val)));
		}
	}

	/// Push the bound literals pinning node `i`'s *fixed* successor (`x_i ≥ v ∧
	/// x_i ≤ v`). Use these, not `Eq(v)`, when explaining an inference from a
	/// fixed successor: `Eq(v)` can sit at an earlier level than the bound
	/// collapse `val()` observes, giving a non-asserting reason; the bound
	/// literals carry the level `val()` reads.
	#[inline]
	pub(crate) fn push_fixed<C>(&self, out: &mut Vec<C::Atom>, i: usize, ctx: &mut C)
	where
		C: ReasoningContext + ?Sized,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		let (lb, ub) = self.vars[i].bounds(ctx);
		debug_assert_eq!(lb, ub, "push_fixed called on an unfixed variable");
		out.push(self.vars[i].lit(ctx, IntLitMeaning::GreaterEq(lb)));
		out.push(self.vars[i].lit(ctx, IntLitMeaning::Less(ub + 1)));
	}

	/// Append the `x_i != j` literals for every `i` in `from`, `j` in `to`
	/// (skipping `i == j` and the optional `except` pair) — see
	/// [`Self::push_absent`].
	pub(crate) fn push_no_edge<C>(
		&self,
		out: &mut Vec<C::Atom>,
		from: &[usize],
		to: &[usize],
		except: Option<(usize, usize)>,
		ctx: &mut C,
	) where
		C: ReasoningContext + ?Sized,
		I: IntDecisionActions<C> + IntInspectionActions<C>,
	{
		for &i in from {
			// Emit each bound literal at most once, so the clause stays duplicate-free.
			let (lb, ub) = self.vars[i].bounds(ctx);
			let mut pushed_min = false;
			let mut pushed_max = false;
			for &j in to {
				if i == j || except == Some((i, j)) {
					continue;
				}
				let val = self.edge_val(j);
				if val < lb {
					if !pushed_min {
						out.push(self.vars[i].min_lit(ctx));
						pushed_min = true;
					}
				} else if val > ub {
					if !pushed_max {
						out.push(self.vars[i].max_lit(ctx));
						pushed_max = true;
					}
				} else {
					out.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(val)));
				}
			}
		}
	}

	/// Append the successor positions of `node` (skipping a self-loop for
	/// `subcircuit`) to `out`, reusing `out`'s allocation.
	pub(crate) fn scc_successors<C>(&self, ctx: &C, node: usize, out: &mut Vec<usize>)
	where
		C: PropagationActions,
		I: IntInspectionActions<C>,
	{
		for val in self.vars[node].domain(ctx).iter().flatten() {
			if let Some(p) = self.val_to_pos(val) {
				if self.subcircuit && p == node {
					continue;
				}
				out.push(p);
			}
		}
	}

	/// Translate a successor value `val` into a node position, if it refers to
	/// a node of this circuit.
	#[inline]
	pub(crate) fn val_to_pos(&self, val: IntVal) -> Option<usize> {
		if val >= self.offset && val < self.offset + self.n() as IntVal {
			Some((val - self.offset) as usize)
		} else {
			None
		}
	}
}
