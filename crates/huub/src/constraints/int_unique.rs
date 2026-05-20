//! Structure and algorithms for the integer unique constraint, which
//! enforces that a list of integer variables each take a different value.

use std::cmp;

use fixedbitset::FixedBitSet;
use itertools::{Either, Itertools};
use rangelist::IntervalIterator;
use tracing::warn;

use crate::{
	Conjunction, IntVal,
	actions::{
		InitActions, IntEvent, IntInspectionActions, IntPropCond, PostingActions,
		PropagationActions, ReasoningContext, ReasoningEngine, Trailed, TrailingActions,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::{IntLitMeaning, engine::Engine, queue::PriorityLevel},
};

/// Representation of the integer `unique` constraint within a model.
///
/// This constraint enforces that all the given integer decisions take different
/// values.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntUnique {
	/// Instance of the [`IntUniqueBounds`] propagator.
	pub(crate) bounds_prop: IntUniqueBounds<View<IntVal>>,
	/// Instance of the [`IntUniqueValue`] propagator.
	pub(crate) value_prop: IntUniqueValue<View<IntVal>>,
	/// Whether to enable the bounds consistent propagator.
	///
	/// Defaults to `true`.
	pub(crate) bounds_propagation: Option<bool>,
	/// Whether to enable the value consistent propagator.
	///
	/// Defaults to `false`.
	pub(crate) value_propagation: Option<bool>,
	/// Whether to enable the domain consistent propagator.
	///
	/// Defaults to `false`.
	pub(crate) domain_propagation: Option<bool>,
}

/// Bounds consistent propagator for the integer `unique` constraint.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntUniqueBounds<I> {
	/// List of integer variables that must take different values.
	pub(crate) var: Vec<I>,
	/// Struct to store information about variable
	var_info: Vec<UniqueVarMeta>,
	/// Cached lower bounds
	lb_cache: Vec<IntVal>,
	/// Cached upper bounds
	ub_cache: Vec<IntVal>,
	/// Index (from vars) of all variables sorted by min bound
	min_sorted: Vec<usize>,
	/// Index (from vars) of all variables sorted by max bound
	max_sorted: Vec<usize>,
	/// Number of different bounds
	num_bounds: usize,
	/// Ordered vector of distinct max and min bounds with dummies
	bounds: Vec<IntVal>,
	/// The critical capacity pointers; that is, `predecessor[i]` points to the
	/// predecessor of i in the `bounds` list.
	predecessor: Vec<usize>,
	/// The diﬀerences between critical capacities; that is `diff[i]` is the
	/// diﬀerence of capacities between `bounds[i]` and its predecessor element
	/// in the list `bounds[predecessor[i]]`
	diff: Vec<IntVal>,
	/// The Hall interval pointers; that is, if `hall_interval[i] < i` then the
	/// half-open interval [`bounds[hall_interval[i]]`, `bounds[i]`) is
	/// contained in a Hall interval, and otherwise holds a pointer to the Hall
	/// interval it belongs to. This Hall interval is represented by a tree,
	/// with the root containing the value of its right end.
	hall_interval: Vec<usize>,
	/// Hall interval bucket transitions
	bucket: Vec<usize>,
}

/// Value consistent propagator for the integer `unique` constraint.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntUniqueValue<I> {
	/// List of integer variables that must take different values.
	vars: Vec<I>,
	/// List of (indexes of) variable signaled to be fixed.
	action_list: Vec<usize>,
}

/// Information that is tracked for each variable for the propagation of
/// [`IntUniqueBounds`]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UniqueVarMeta {
	/// Transition for the variable's position in the Hall interval tree.
	next: usize,
	/// Minimum index in the [`IntUniqueBounds::bounds`] vector
	min_rank: usize,
	/// Maximum index in the [`IntUniqueBounds::bounds`] vector
	max_rank: usize,
}

impl IntUnique {
	/// Returns whether a bounds consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn bounds_propagation(&self) -> bool {
		self.bounds_propagation.unwrap_or(true)
	}

	/// Returns whether a value consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn value_propagation(&self) -> bool {
		self.value_propagation.unwrap_or(false)
	}

	/// Returns whether a domain consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn domain_propagation(&self) -> bool {
		self.domain_propagation.unwrap_or(false)
	}
}

impl<E> Constraint<E> for IntUnique
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let (_vals, vars): (Vec<_>, Vec<_>) = self.bounds_prop.var.iter().partition_map(|&var| {
			let var = slv.solver_view(var);
			if let Some(val) = var.val(slv) {
				Either::Left(val)
			} else {
				Either::Right(var)
			}
		});
		// Propagation should have detected any duplicate fixed values and removed them
		// from the domains of other decision variables.
		debug_assert!(_vals.iter().unique().collect_vec().len() == _vals.len());
		debug_assert!(
			_vals
				.iter()
				.all(|&val| vars.iter().all(|var| !var.in_domain(slv, val)))
		);

		// If the number of non-fixed decision variables is less than or equal
		// to 1, there is no need to post any propagators.
		if vars.len() <= 1 {
			return Ok(());
		}

		let value_propagation = self.value_propagation();
		if value_propagation {
			IntUniqueValue::post(slv, vars.clone());
		}
		let domain_propagation = self.domain_propagation();
		let mut bounds_propagation = self.bounds_propagation();
		if !value_propagation && !bounds_propagation && !domain_propagation {
			warn!(
				"all propagation algorithms are disabled for `int_unique` constraint, override with bounds propagation to ensure consistency"
			);
			bounds_propagation = true;
		}
		if bounds_propagation {
			IntUniqueBounds::post(slv, vars.clone());
		}
		if domain_propagation {
			IntUniqueDomain::post(slv, vars);
		}
		Ok(())
	}
}

impl<E> Propagator<E> for IntUnique
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, ctx: &mut E::NotificationContext<'_>) {
		self.value_prop.advise_of_backtrack(ctx);
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		self.value_prop.advise_of_int_change(ctx, data, event)
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		self.value_prop.initialize(ctx);
		self.bounds_prop.initialize(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		if !self.value_prop.action_list.is_empty() {
			self.value_prop.propagate(ctx)?;
		}
		self.bounds_prop.propagate(ctx)
	}
}

impl<I> IntUniqueBounds<I> {
	/// Filter the lower bounds of the considered variables
	fn filter_lower<E>(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		for i in 1..=self.num_bounds + 1 {
			self.hall_interval[i] = i - 1;
			self.predecessor[i] = i - 1;
			self.diff[i] = self.bounds[i] - self.bounds[i - 1];
			self.bucket[i] = usize::MAX;
		}

		for i in 0..self.var.len() {
			let max_rank = self.var_info[self.max_sorted[i]].max_rank;
			let min_rank = self.var_info[self.max_sorted[i]].min_rank;

			let mut z = Self::path_max(&self.predecessor, min_rank + 1);
			let j = self.predecessor[z];
			self.diff[z] -= 1;
			self.var_info[self.max_sorted[i]].next = self.bucket[z];
			self.bucket[z] = self.max_sorted[i];
			if self.diff[z] == 0 {
				self.predecessor[z] = z + 1;
				z = Self::path_max(&self.predecessor, self.predecessor[z]);
				self.predecessor[z] = j;
			};
			Self::path_set(&mut self.predecessor, min_rank + 1, z, z);

			if self.hall_interval[min_rank] > min_rank {
				let w = Self::path_max(&self.hall_interval, self.hall_interval[min_rank]);
				let hall_max = self.bounds[w];
				let mut hall_min = self.bounds[min_rank];
				let mut k = w;
				while self.bounds[k] > hall_min {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						hall_min = cmp::min(hall_min, self.lb_cache[l]);
						l = self.var_info[l].next;
					}
					k -= 1;
				}

				let mut k = w;
				let mut reason = Vec::new();
				reason.push(
					self.var[self.max_sorted[i]].lit(ctx, IntLitMeaning::GreaterEq(hall_min)),
				);
				while self.bounds[k] > hall_min {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						reason.push(self.var[l].lit(ctx, IntLitMeaning::GreaterEq(hall_min)));
						reason.push(self.var[l].lit(ctx, IntLitMeaning::Less(hall_max)));
						l = self.var_info[l].next;
					}
					k -= 1;
				}

				self.var[self.max_sorted[i]].tighten_min(ctx, hall_max, reason)?;
				self.lb_cache[self.max_sorted[i]] = hall_max;

				Self::path_set(&mut self.hall_interval, min_rank, w, w);
			}
			if self.diff[z] == self.bounds[z] - self.bounds[max_rank] {
				let h_max_rank = self.hall_interval[max_rank];
				// Save Hall interval
				Self::path_set(&mut self.hall_interval, h_max_rank, j - 1, max_rank);
				self.hall_interval[max_rank] = j - 1;
			}
		}
		Ok(())
	}

	/// Filter the upper bounds of the considered variables
	fn filter_upper<E>(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		for i in 0..=self.num_bounds {
			self.hall_interval[i] = i + 1;
			self.predecessor[i] = i + 1;
			self.diff[i] = self.bounds[i + 1] - self.bounds[i];
			self.bucket[i] = usize::MAX;
		}

		for i in (0..self.var.len()).rev() {
			let max_rank = self.var_info[self.min_sorted[i]].max_rank;
			let min_rank = self.var_info[self.min_sorted[i]].min_rank;

			let mut z = Self::path_min(&self.predecessor, max_rank - 1);
			let j = self.predecessor[z];
			self.diff[z] -= 1;
			self.var_info[self.min_sorted[i]].next = self.bucket[z];
			self.bucket[z] = self.min_sorted[i];
			if self.diff[z] == 0 {
				self.predecessor[z] = z - 1;
				z = Self::path_min(&self.predecessor, self.predecessor[z]);
				self.predecessor[z] = j;
			}
			Self::path_set(&mut self.predecessor, max_rank - 1, z, z);

			if self.hall_interval[max_rank] < max_rank {
				let w = Self::path_min(&self.hall_interval, self.hall_interval[max_rank]);
				let hall_min = self.bounds[w];
				let mut hall_max = self.bounds[max_rank];
				let mut k = w;
				while self.bounds[k] < hall_max {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						hall_max = cmp::max(hall_max, self.ub_cache[l] + 1);
						l = self.var_info[l].next;
					}
					k += 1;
				}

				let mut k = w;
				let mut reason = Vec::new();
				reason.push(self.var[self.min_sorted[i]].lit(ctx, IntLitMeaning::Less(hall_max)));
				while self.bounds[k] < hall_max {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						reason.push(self.var[l].lit(ctx, IntLitMeaning::GreaterEq(hall_min)));
						reason.push(self.var[l].lit(ctx, IntLitMeaning::Less(hall_max)));
						l = self.var_info[l].next;
					}
					k += 1;
				}

				self.var[self.min_sorted[i]].tighten_max(ctx, hall_min - 1, reason)?;
				self.ub_cache[self.min_sorted[i]] = hall_min - 1;

				Self::path_set(&mut self.hall_interval, max_rank, w, w);
			}

			if self.diff[z] == self.bounds[min_rank] - self.bounds[z] {
				let h_min_rank = self.hall_interval[min_rank];
				// Save Hall interval
				Self::path_set(&mut self.hall_interval, h_min_rank, j + 1, min_rank);
				self.hall_interval[min_rank] = j + 1;
			}
		}
		Ok(())
	}

	/// Create a new [`IntUniqueBounds`] propagator.
	pub(crate) fn new(vars: Vec<I>) -> Self {
		let interval = vec![
			UniqueVarMeta {
				next: 0,
				min_rank: 0,
				max_rank: 0
			};
			vars.len()
		];
		let min_sorted: Vec<_> = (0..vars.len()).collect();
		let max_sorted: Vec<_> = (0..vars.len()).collect();

		let n = 2 * vars.len() + 2;
		Self {
			var: vars,
			var_info: interval,
			lb_cache: vec![0; n],
			ub_cache: vec![0; n],
			min_sorted,
			max_sorted,
			num_bounds: 0,
			bounds: vec![0; n],
			predecessor: vec![0; n],
			diff: vec![0; n],
			hall_interval: vec![0; n],
			bucket: vec![0; n],
		}
	}

	/// Follows path given by `transition` from `start` until we stop increasing
	fn path_max(transition: &[usize], mut start: usize) -> usize {
		while transition[start] > start {
			start = transition[start];
		}
		start
	}

	/// Follows path given by `transition` from `start` until we stop decreasing
	fn path_min(transition: &[usize], mut start: usize) -> usize {
		while transition[start] < start {
			start = transition[start];
		}
		start
	}

	/// Sets everything in the `transition` slice, between `start` and `end` to
	/// `to`
	///
	/// # Example
	///
	/// ```ignore
	/// # use huub::constraints::int_unique::IntUniqueBounds;
	/// let mut transition = vec![4, 2, 0, 1, 3, 0]; // giving e.g. 0 -> 4 -> 3 -> 1 -> 2 -> 0
	/// IntUniqueBounds::path_set(&mut transition, 2, 3, 5);
	/// assert_eq!(transition, vec![5, 2, 5, 1, 5, 0]); // now gives // 0 -> 5 -> 0
	/// ```
	fn path_set(transition: &mut [usize], start: usize, end: usize, to: usize) {
		let mut last;
		let mut cur = start;
		while cur != end {
			last = cur;
			cur = transition[cur];
			transition[last] = to;
		}
	}

	/// Create a new [`IntUniqueBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars)));
	}

	/// Sorts max_sorted and min_sorted and sets the bounds vector
	fn sort<E>(&mut self, ctx: &mut E::PropagationContext<'_>)
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let size: usize = self.var.len();

		for (i, v) in self.var.iter().enumerate() {
			(self.lb_cache[i], self.ub_cache[i]) = v.bounds(ctx);
		}

		self.min_sorted.sort_by_key(|&i| self.lb_cache[i]);
		self.max_sorted.sort_by_key(|&i| self.ub_cache[i] + 1);

		let mut min: IntVal = self.lb_cache[self.min_sorted[0]];
		let mut max: IntVal = self.ub_cache[self.max_sorted[0]] + 1;
		let mut last: IntVal = min - 2;
		self.bounds[0] = last; // Dummy

		let mut i = 0;
		let mut j = 0;
		self.num_bounds = 0;
		loop {
			if i < size && min <= max {
				if min != last {
					self.num_bounds += 1;
					last = min;
					self.bounds[self.num_bounds] = min;
				}
				self.var_info[self.min_sorted[i]].min_rank = self.num_bounds;
				i += 1;
				if i < size {
					min = self.lb_cache[self.min_sorted[i]];
				}
			} else {
				if max != last {
					self.num_bounds += 1;
					last = max;
					self.bounds[self.num_bounds] = max;
				}
				self.var_info[self.max_sorted[j]].max_rank = self.num_bounds;
				j += 1;
				if j == size {
					break;
				}
				max = self.ub_cache[self.max_sorted[j]] + 1;
			}
		}
		self.bounds[self.num_bounds + 1] = self.bounds[self.num_bounds] + 2; // Dummy
	}
}

impl<E, I> Propagator<E> for IntUniqueBounds<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut <E as ReasoningEngine>::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in &self.var {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	#[tracing::instrument(
		name = "int_unique_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		self.sort(ctx);
		self.filter_lower(ctx)?;
		self.filter_upper(ctx)?;
		Ok(())
	}
}

impl<I> IntUniqueValue<I> {
	/// Create a new [`IntUniqueValue`] propagator.
	pub(crate) fn new(vars: Vec<I>) -> Self {
		Self {
			vars,
			action_list: Vec::new(),
		}
	}

	/// Create a new [`IntUniqueBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars)));
	}
}

impl<E, I> Propagator<E> for IntUniqueValue<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationContext<'_>) {
		// We forget any previously remembered fixed decisions.
		self.action_list.clear();
	}

	fn advise_of_int_change(
		&mut self,
		_: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		// We remember that the decision at index `data` has been fixed to a value.
		debug_assert_eq!(event, IntEvent::Fixed);
		self.action_list.push(data as usize);
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// Let the propagator be advised when each specific decision is fixed to a
		// value, with the index of the decision.
		for (i, v) in self.vars.iter().enumerate() {
			if self.vars[i].val(ctx).is_some() {
				// If the variable is already fixed, then add it to the action list immediately.
				self.action_list.push(i);
				ctx.enqueue_now(true);
			} else {
				v.advise_when(ctx, IntPropCond::Fixed, i as u64);
			}
		}
		// Advise the propagator of backtracking to clear the list of fixed decision
		// (indices).
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(
		name = "int_unique_value",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		debug_assert!(!self.action_list.is_empty() && self.action_list.iter().all_unique());
		// We walk through all fixed decisions (indices).
		for &i in &self.action_list {
			// Retrieve the value and value literal for the fixed decision.
			let val = self.vars[i].val(ctx).unwrap();
			let reason = &[self.vars[i].val_lit(ctx).unwrap()];

			// We now enforce that all other decisions (at different indices) are not
			// equal to the fixed value.
			for (j, v) in self.vars.iter().enumerate() {
				if j != i {
					v.remove_val(ctx, val, reason)?;
				}
			}
		}
		// We clear the list of indices of fixed decisions.
		self.action_list.clear();
		Ok(())
	}
}

/// Backtrackable disjoint-set partition of `{0, .., n-1}`. Each block is a
/// contiguous slice of [`Self::elems`]. Block membership is maintained during
/// search by trailed [`Self::layout`]. The data structure is
/// generic in what `{0..n}` means — in [`IntUniqueDomain`] the elements are
/// variable indices, but nothing here depends on that.
///
/// `layout` uses a dual encoding, indexed by position in `elems`:
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
///   elems:         0  2  1  3
///   positions:     0  2  1  3
///   layout:        2  0  4  2     // pos 0 -> end 2; pos 2 -> end 4
/// ```
#[derive(Clone, Debug)]
struct TrailedPartition {
	/// Permutation of `0..n` whose contiguous slices are the current blocks.
	elems: Vec<usize>,
	/// Inverse permutation: `elems[positions[i]] == i` for every `i`.
	positions: Vec<usize>,
	/// Per-position trailed slot (see struct doc for dual encoding).
	layout: Vec<Trailed<i64>>,
}

impl TrailedPartition {
	/// Root position of the block containing `elem`.
	fn block_root(&self, elem: usize, ctx: &impl TrailingActions) -> usize {
		let pos = self.positions[elem];
		let info = ctx.trailed::<i64>(self.layout[pos]) as usize;
		cmp::min(info, pos)
	}

	/// Exclusive end position of the block rooted at `root`. Caller must pass
	/// the block's root position or otherwise results are meaningless.
	fn block_end(&self, root: usize, ctx: &impl TrailingActions) -> usize {
		debug_assert_eq!(
			self.block_root(self.elems[root], ctx),
			root,
			"block_end called with a non-root position"
		);
		ctx.trailed::<i64>(self.layout[root]) as usize
	}

	/// Split the listed `elems` (all of which must currently belong to the
	/// same block) out into a new block. Returns `(orig_root, Some(new_root))`,
	/// or `(orig_root, None)` if every member of the original block was moved.
	fn split_off(
		&mut self,
		elems: &[usize],
		ctx: &mut impl TrailingActions,
	) -> (usize, Option<usize>) {
		let orig_root = self.block_root(elems[0], ctx);
		let orig_end = self.block_end(orig_root, ctx);
		debug_assert!(elems.iter().all(|&i| self.block_root(i, ctx) == orig_root));
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

/// The bipartite "variable <-> value" graph that Régin's algorithm operates on,
/// together with the current maximum matching between the two sides.
///
/// All variable/value bookkeeping lives here: the variable list, the
/// union-domain origin used to translate between integer values and right-side
/// indices, and the matching tables. Algorithms (augmenting-path search,
/// Tarjan, Hall-set reasoning) operate on this struct from the outside.
#[derive(Clone, Debug)]
struct VariableValueMatching<I> {
	/// Left side: the integer decision variables.
	vars: Vec<I>,
	/// Lower bound of the union of all initial variable domains. The
	/// right-side index `r` represents the integer value
	/// `union_domain_lb + r`, for `r` in `0..n_values()`.
	union_domain_lb: IntVal,
	/// Matching: variable index -> value index.
	var_to_val: Vec<Option<usize>>,
	/// Matching: value index -> variable index. Sized once in [`Self::init`]
	/// to the size of the union of initial variable domains.
	val_to_var: Vec<Option<usize>>,
}

impl<I> VariableValueMatching<I> {
	/// Number of left-side nodes (variables).
	fn n_vars(&self) -> usize {
		self.vars.len()
	}

	/// Number of right-side nodes (values in the union of initial domains).
	fn n_values(&self) -> usize {
		self.val_to_var.len()
	}

	/// Total nodes in the bipartite graph.
	fn n_nodes(&self) -> usize {
		self.n_vars() + self.n_values()
	}

	/// Integer value at the given right-side index.
	fn value_at(&self, right_idx: usize) -> IntVal {
		self.union_domain_lb + right_idx as IntVal
	}

	/// Right-side index for a value already known to lie in
	/// `[union_domain_lb, union_domain_lb + n_values())`.
	fn value_index(&self, val: IntVal) -> usize {
		(val - self.union_domain_lb) as usize
	}

	/// Rewire the matching along a freshly discovered BFS-augmenting path
	/// ending at `(end_var, end_val)`. Walks backwards through
	/// `bfs_parent`, flipping each edge until it reaches the path's root
	/// (a variable whose previous match was `None`).
	fn augment_along_path(&mut self, end_var: usize, end_val: usize, bfs_parent: &[usize]) {
		let mut cur_var = end_var;
		let mut cur_val = end_val;
		loop {
			let prev_val = self.var_to_val[cur_var];
			self.val_to_var[cur_val] = Some(cur_var);
			self.var_to_val[cur_var] = Some(cur_val);
			let Some(pv) = prev_val else {
				break;
			};
			cur_val = pv;
			let parent = bfs_parent[cur_var];
			debug_assert_ne!(parent, usize::MAX, "BFS parent missing");
			cur_var = parent;
		}
	}

	/// One-shot lazy initialisation: compute union-domain extents from
	/// variable bounds and size the matching's right side accordingly. Must
	/// be called exactly once before any propagation; calling twice would
	/// empty `val_to_var` and discard the current matching.
	fn init<E>(&mut self, ctx: &mut E::InitializationContext<'_>)
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut lb = IntVal::MAX;
		let mut ub = IntVal::MIN;
		for v in &self.vars {
			let (l, u) = v.bounds(ctx);
			lb = cmp::min(lb, l);
			ub = cmp::max(ub, u);
		}
		debug_assert!(lb <= ub);
		self.union_domain_lb = lb;
		self.val_to_var = vec![None; (ub - lb + 1) as usize];
	}
}

/// Reusable scratch for BFS-based augmenting-path search on a bipartite
/// graph. Depends only on the number of left nodes.
#[derive(Clone, Debug)]
struct AugmentingPathScratch {
	/// BFS queue (over left nodes).
	queue: Vec<usize>,
	/// Per-left-node BFS visited flag; cleared at the start of each search.
	visited: FixedBitSet,
	/// Per-left-node BFS parent pointer; `usize::MAX` means "no parent /
	/// root".
	parent: Vec<usize>,
}

/// Reusable scratch for Tarjan's SCC algorithm over a graph with `n` total
/// nodes. `vars_buf` / `vals_buf` are sized for the bipartite use-case (one
/// bitset per side); a single-bucket variant would suit a non-bipartite
/// consumer.
#[derive(Clone, Debug)]
struct TarjanScratch {
	/// Stack for Tarjan's algorithm.
	dfs_stack: Vec<usize>,
	/// Whether a node is currently on the DFS stack.
	dfs_on_stack: Vec<bool>,
	/// DFS index assigned to each node during the current search.
	/// Value `0` means "not yet visited in this run".
	dfs_index: Vec<usize>,
	/// Lowest reachable DFS index from each node during the current search.
	/// Value `0` means "not yet visited in this run".
	low_link: Vec<usize>,
	/// Neighbour frame-stack: each `tarjan_dfs` call appends its current
	/// node's neighbours, remembers `(start, end)` for its own slice, and
	/// truncates back on unwind. Reuses one allocation across all DFS frames.
	neighbours: Vec<usize>,
	/// Scratch bitset of left nodes in the SCC currently being popped.
	vars_buf: Vec<usize>,
	/// Scratch bitset of right nodes in the SCC currently being popped.
	vals_buf: Vec<usize>,
}

impl TarjanScratch {
	/// Reset bookkeeping before a fresh DFS run. After this call,
	/// `dfs_index[v] == 0` signals "not yet visited" (indices are assigned
	/// starting at `1`).
	fn reset(&mut self) {
		self.dfs_stack.clear();
		self.dfs_on_stack.fill(false);
		self.dfs_index.fill(0);
		self.low_link.fill(0);
		self.neighbours.clear();
	}

	/// Size the per-node buffers to fit a graph with `n_nodes` total nodes and
	/// `n_values` right-side nodes. Called once after the union-domain
	/// extents are known.
	fn resize(&mut self, n_nodes: usize) {
		self.dfs_on_stack = vec![false; n_nodes];
		self.dfs_index = vec![0; n_nodes];
		self.low_link = vec![0; n_nodes];
	}
}

/// Domain consistent propagator for the integer `unique` constraint.
///
/// Implements Régin's bipartite matching + Tarjan SCC algorithm (AAAI 1994):
/// maintain a maximum matching from variables to values. After each domain
/// change, repair the matching with BFS-augmenting paths. Then run Tarjan's SCC
/// on the residual bipartite graph, and remove any value from a variable's
/// domain whenever the variable and value land in different SCCs.
///
/// The four nested structs are intentionally written in graph-generic language
/// so they can be lifted into `crates/huub/src/helpers/` when a second consumer
/// appears (e.g. `circuit`, `global_cardinality`). No other propagator in the
/// crate currently uses them, so they live here for now.
///
/// **References**
///
/// - Régin, Jean-Charles. "A filtering algorithm for constraints of difference
///   in CSPs." AAAI 94 (1994): 362-367.
/// - Gent, Ian P., Ian Miguel, and Peter Nightingale. "Generalised arc
///   consistency for the AllDifferent constraint: An empirical survey."
///   Artificial Intelligence 172.18 (2008): 1973-2000.
/// - Downing, Nicholas, Thibaut Feydy, and Peter J. Stuckey. "Explaining
///   alldifferent." In Proceedings of the Australasian Computer Science
///   Conference (ACSC 2012), CRPIT Volume 122, pages 115--124, 2012
#[derive(Clone, Debug)]
pub struct IntUniqueDomain<I> {
	/// Variables, values, and their current matching.
	graph: VariableValueMatching<I>,
	/// Set of variable indices whose domain has changed since the last
	/// propagation pass; cleared by `propagate` and `advise_of_backtrack`.
	dirty_vars: FixedBitSet,
	/// Always-empty (but `n_vars`-sized) scratch bitset. `propagate` swaps
	/// this with `dirty_vars` so it can iterate the dirty bits while
	/// `advise_of_int_change` keeps writing into the (now empty) bitset.
	dirty_scratch: FixedBitSet,
	/// Backtrackable partition of variable indices into current SCCs.
	partition: TrailedPartition,
	/// Per-call scratch for augmenting-path search.
	bfs: AugmentingPathScratch,
	/// Per-call scratch for Tarjan SCC.
	tarjan: TarjanScratch,
}

impl<I> IntUniqueDomain<I> {
	/// Create a new [`IntUniqueDomain`] propagator and post it in the solver.
	///
	/// Domain extents and the value-side tables are sized lazily on the first
	/// propagation call (we cannot probe variable bounds from
	/// [`PostingActions`]).
	pub fn post<E>(solver: &mut E, vars: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		let n = vars.len();
		// Each variable owns one trailed slot; the partition layout starts as a
		// single block containing every variable: `layout[0] = n` (end position)
		// and every other entry is `0` (pointing to root position 0).
		let layout: Vec<Trailed<i64>> = (0..n)
			.map(|i| solver.new_trailed::<i64>(if i == 0 { n as i64 } else { 0 }))
			.collect();

		solver.add_propagator(Box::new(Self {
			graph: VariableValueMatching {
				vars,
				union_domain_lb: 0,
				var_to_val: vec![None; n],
				val_to_var: Vec::new(),
			},
			dirty_vars: FixedBitSet::with_capacity(n),
			dirty_scratch: FixedBitSet::with_capacity(n),
			partition: TrailedPartition {
				elems: (0..n).collect(),
				positions: (0..n).collect(),
				layout,
			},
			bfs: AugmentingPathScratch {
				queue: Vec::new(),
				visited: FixedBitSet::with_capacity(n),
				parent: vec![usize::MAX; n],
			},
			tarjan: TarjanScratch {
				dfs_stack: Vec::new(),
				dfs_on_stack: Vec::new(),
				dfs_index: Vec::new(),
				low_link: Vec::new(),
				neighbours: Vec::new(),
				vars_buf: Vec::new(),
				vals_buf: Vec::new(),
			},
		}));
	}

	/// One-shot lazy initialisation performed on the first propagate.
	/// Initialises the graph's union-domain extents and sizes every
	/// Tarjan scratch buffer that depends on them.
	fn init_lazy_state<E>(&mut self, ctx: &mut E::InitializationContext<'_>)
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		self.graph.init::<E>(ctx);
		self.tarjan.resize(self.graph.n_nodes());
	}

	/// Attempt to repair the matching for `start_var` (whose previously matched
	/// value is no longer in its domain) by finding a BFS-augmenting path.
	///
	/// On success, rewires the matching along the discovered path and returns
	/// `Ok(())`. On failure, restores the previous matching and returns
	/// `Err(conflict)`. The conflict closure constructs a Hall-set explanation
	/// from the BFS-visited variables, whose domain union has strictly fewer
	/// values than variables.
	fn find_augmenting_path<E>(
		&mut self,
		start_var: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let matched_val_idx = self.graph.var_to_val[start_var];
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_var[val_idx] = None;
			self.graph.var_to_val[start_var] = None;
		}

		self.bfs.queue.clear();
		self.bfs.queue.push(start_var);
		self.bfs.visited.clear();
		self.bfs.parent.fill(usize::MAX);
		self.bfs.visited.insert(start_var);
		let mut queue_head = 0;
		while queue_head < self.bfs.queue.len() {
			let var_idx = self.bfs.queue[queue_head];
			queue_head += 1;
			for val in self.graph.vars[var_idx].domain(ctx).iter().flatten() {
				let val_idx = self.graph.value_index(val);
				if let Some(matched_var) = self.graph.val_to_var[val_idx] {
					if !self.bfs.visited.contains(matched_var) {
						self.bfs.queue.push(matched_var);
						self.bfs.parent[matched_var] = var_idx;
						self.bfs.visited.insert(matched_var);
					}
				} else {
					self.graph
						.augment_along_path(var_idx, val_idx, &self.bfs.parent);
					return Ok(());
				}
			}
		}

		// No augmenting path: restore the previous matching and signal conflict
		// with a Hall-set explanation built from the BFS-visited variables.
		if let Some(val_idx) = matched_val_idx {
			self.graph.val_to_var[val_idx] = Some(start_var);
			self.graph.var_to_val[start_var] = Some(val_idx);
		}

		Err(ctx.declare_conflict(
			move |ctx: &mut E::PropagationContext<'_>| -> Vec<<E as ReasoningEngine>::Atom> {
				self.build_hall_set_reason(ctx, &self.bfs.queue, |var, ctx, meaning| {
					var.lit(ctx, meaning)
				})
			},
		))
	}

	/// Append `start_idx`'s residual-graph neighbours to `tarjan.neighbours`.
	/// Caller records `tarjan.neighbours.len()` before and after this call to
	/// know which slice belongs to its frame, and truncates back on unwind.
	fn push_tarjan_neighbours<E>(&mut self, start_idx: usize, ctx: &mut E::PropagationContext<'_>)
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let n_vars = self.graph.n_vars();
		if start_idx < n_vars {
			let var_idx = start_idx;
			for val in self.graph.vars[var_idx].domain(ctx).iter().flatten() {
				let val_idx = self.graph.value_index(val);
				if self.graph.var_to_val[var_idx] == Some(val_idx) {
					continue;
				}
				self.tarjan.neighbours.push(n_vars + val_idx);
			}
		} else {
			let val_idx = start_idx - n_vars;
			if let Some(var_idx) = self.graph.val_to_var[val_idx] {
				self.tarjan.neighbours.push(var_idx);
			} else {
				// Unmatched value: connected to every matched value node.
				for vi in 0..self.graph.n_values() {
					if self.graph.val_to_var[vi].is_some() {
						self.tarjan.neighbours.push(n_vars + vi);
					}
				}
			}
		}
	}

	/// Process the SCC rooted at `start_idx`: pop nodes off the DFS stack into
	/// `tarjan.vars_buf` / `vals_buf`, partition the variables out of the live
	/// SCC, and remove the SCC's values from any variable outside it.
	fn process_scc_root<E>(
		&mut self,
		start_idx: usize,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let n_vars = self.graph.n_vars();
		self.tarjan.vars_buf.clear();
		self.tarjan.vals_buf.clear();

		// Pop the SCC off the DFS stack into the two bitsets.
		let mut has_var_in_scc = false;
		loop {
			let node = self.tarjan.dfs_stack.pop().expect("non-empty DFS stack");
			self.tarjan.dfs_on_stack[node] = false;
			if node < n_vars {
				self.tarjan.vars_buf.push(node);
				has_var_in_scc = true;
			} else {
				self.tarjan.vals_buf.push(node - n_vars);
			}
			if node == start_idx {
				break;
			}
		}

		// An SCC with no variable nodes does nothing useful: any matched value
		// in this SCC would force its matched var to be in the SCC too (the
		// matching edge is in the residual graph), and an unmatched value with
		// no adjacent var has no support to remove from anywhere.
		if !has_var_in_scc {
			return Ok(());
		}

		// Move the SCC's variables into their own block. `split_off` keeps the
		// SCC's vars in positions [new_root..orig_end); the *other* vars from
		// the same original block now occupy [orig_root..new_root) — exactly
		// the variables that still need this SCC's values stripped from them.
		let (orig_root, new_scc_root) = self.partition.split_off(&self.tarjan.vars_buf, ctx);
		let Some(new_root) = new_scc_root else {
			// The new SCC absorbed the entire original block — no outside
			// variables to strip values from.
			return Ok(());
		};

		// `new_root` is the SCC's block root for both matched and unmatched
		// values (a matched val's matched_var is in this SCC; for an unmatched
		// val, any in-SCC var serves as the SCC representative). One scc_id
		// covers every value in the SCC.
		let scc_id = new_root;
		let val_reason = ctx.deferred_reason(scc_id as u64);
		for &val_idx in self.tarjan.vals_buf.iter() {
			let val = self.graph.value_at(val_idx);
			for pos in orig_root..new_root {
				let var_idx = self.partition.elems[pos];
				let var = self.graph.vars[var_idx].clone();
				if !var.in_domain(ctx, val) {
					continue;
				}
				var.remove_val(ctx, val, val_reason)?;
			}
		}
		Ok(())
	}

	/// Recursive Tarjan DFS on the bipartite var/value residual graph. When
	/// the root of a non-trivial SCC is popped and the run already detected an
	/// SCC split, delegates filtering to [`Self::process_scc_root`].
	fn tarjan_dfs<E>(
		&mut self,
		start_idx: usize,
		next_dfs_index: &mut usize,
		n_left_visited: &mut usize,
		scc_split_detected: &mut bool,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let n_vars = self.graph.n_vars();
		if start_idx < n_vars {
			*n_left_visited += 1;
		}

		self.tarjan.dfs_stack.push(start_idx);
		self.tarjan.dfs_on_stack[start_idx] = true;
		self.tarjan.dfs_index[start_idx] = *next_dfs_index;
		self.tarjan.low_link[start_idx] = *next_dfs_index;
		*next_dfs_index += 1;

		let frame_start = self.tarjan.neighbours.len();
		self.push_tarjan_neighbours::<E>(start_idx, ctx);
		let frame_end = self.tarjan.neighbours.len();
		let mut i = frame_start;
		while i < frame_end {
			let nb = self.tarjan.neighbours[i];
			if self.tarjan.dfs_index[nb] != 0 {
				if self.tarjan.dfs_on_stack[nb] {
					self.tarjan.low_link[start_idx] =
						cmp::min(self.tarjan.low_link[start_idx], self.tarjan.dfs_index[nb]);
				}
			} else {
				self.tarjan_dfs::<E>(nb, next_dfs_index, n_left_visited, scc_split_detected, ctx)?;
				self.tarjan.low_link[start_idx] =
					cmp::min(self.tarjan.low_link[start_idx], self.tarjan.low_link[nb]);
			}
			i += 1;
		}
		self.tarjan.neighbours.truncate(frame_start);

		// SCC root?
		if self.tarjan.low_link[start_idx] == self.tarjan.dfs_index[start_idx] {
			// Either we entered the DFS in the middle (low_link > 1) or some
			// left nodes weren't reached from this root -> graph is not one
			// single SCC. The counter avoids re-scanning `dfs_index` on every
			// SCC-root pop.
			if self.tarjan.low_link[start_idx] > 1 || *n_left_visited < n_vars {
				*scc_split_detected = true;
			}
			if *scc_split_detected {
				self.process_scc_root::<E>(start_idx, ctx)?;
			}
		}
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntUniqueDomain<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationContext<'_>) {
		self.dirty_vars.clear();
	}

	/// When a variable's domain changes, mark it as dirty and only enqueue
	/// propagation if its domain size is now less than the number of variables.
	/// Larger domains cannot participate in any non-trivial Hall set, so there
	/// is nothing to propagate.
	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		_event: IntEvent,
	) -> bool {
		// safe to unwrap: `card()` only returns `None` if the number of steps would
		// overflow `usize`
		let domain_size = self.graph.vars[data as usize].domain(ctx).card().unwrap();
		self.dirty_vars.set(data as usize, true);
		domain_size < self.graph.n_vars()
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		self.init_lazy_state(ctx);
		self.dirty_vars.set_range(.., true);
		ctx.set_priority(PriorityLevel::Low);
		for (i, v) in self.graph.vars.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Domain, i as u64);
		}
		ctx.advise_on_backtrack();
		ctx.enqueue_now(true);
	}

	fn explain(
		&mut self,
		ctx: &mut E::ExplanationContext<'_>,
		_lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		let scc_id = data as usize;
		let scc_end = self.partition.block_end(scc_id, ctx);
		self.build_hall_set_reason(
			ctx,
			&self.partition.elems[scc_id..scc_end],
			|var, ctx, meaning| {
				let (atom, _) = var.lit_relaxed(ctx, meaning);
				atom
			},
		)
	}

	#[tracing::instrument(
		name = "int_unique_domain",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// Phase 1: drain dirty variables, fix the matching, and collect the
		// set of SCC roots whose residual graph may have changed.
		//
		// Swap the dirty bitset out into a local so `advise_of_int_change` can
		// keep writing during the call (it sees the just-emptied scratch in
		// `self.dirty_vars`). Restore the scratch at the end so the next
		// propagate is set up again.
		std::mem::swap(&mut self.dirty_vars, &mut self.dirty_scratch);
		let mut dirty = std::mem::take(&mut self.dirty_scratch);
		let result = self.repair_matching_and_propagate_fixed(&dirty, ctx);
		// Restore the scratch *before* propagating the error so the next
		// propagate call sees a sized (empty) `dirty_scratch`.
		dirty.clear();
		self.dirty_scratch = dirty;
		let changed_scc = result?;

		// Phase 2: re-run Tarjan on every SCC that changed in phase 1.
		self.run_tarjan_on_changed_sccs(&changed_scc, ctx)
	}
}

impl<I> IntUniqueDomain<I> {
	/// Phase 1 of `propagate`. For each dirty variable: repair its matching
	/// entry if its previous match left the domain, then either propagate the
	/// "newly fixed" case (singleton domain -> strip its value from the rest of
	/// its SCC) or mark the surrounding SCC as needing a Tarjan re-run.
	///
	/// Returns the set of SCC roots that need to be revisited in phase 2.
	fn repair_matching_and_propagate_fixed<E>(
		&mut self,
		dirty: &FixedBitSet,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<FixedBitSet, E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		let mut changed_scc = FixedBitSet::with_capacity(self.graph.n_vars());
		for i in dirty.ones() {
			let scc_id = self.partition.block_root(i, ctx);
			let needs_augment = match self.graph.var_to_val[i] {
				None => true,
				Some(val_idx) => !self.graph.vars[i].in_domain(ctx, self.graph.value_at(val_idx)),
			};
			if needs_augment {
				self.find_augmenting_path::<E>(i, ctx)?;
			}

			// If the variable is now fixed, propagate the newly fixed event.
			// Otherwise, mark its involved SCC as dirty for phase 2.
			if let Some(val) = self.graph.vars[i].val(ctx) {
				changed_scc.set(scc_id, false);
				let (orig_scc, new_scc) = self.partition.split_off(&[i], ctx);
				if new_scc.is_some() {
					let orig_scc_end = self.partition.block_end(orig_scc, ctx);
					let reason_lit = self.graph.vars[i].lit(ctx, IntLitMeaning::Eq(val));
					for pos in orig_scc..orig_scc_end {
						let idx = self.partition.elems[pos];
						let v = self.graph.vars[idx].clone();
						v.remove_val(ctx, val, [reason_lit.clone()].as_slice())?;
					}
					changed_scc.set(orig_scc, orig_scc_end - orig_scc > 1);
				}
			} else {
				let scc_end = self.partition.block_end(scc_id, ctx);
				changed_scc.set(scc_id, scc_end - scc_id > 1);
			}
		}
		Ok(changed_scc)
	}

	/// Phase 2 of `propagate`. Runs Tarjan on every SCC root flagged in
	/// `changed_scc`. Tarjan walks the residual bipartite graph and, for each
	/// non-trivial SCC discovered, partitions the variables out and removes
	/// the SCC's values from variables outside it.
	fn run_tarjan_on_changed_sccs<E>(
		&mut self,
		changed_scc: &FixedBitSet,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: IntSolverActions<E>,
	{
		self.tarjan.reset();
		let mut next_dfs_index: usize = 1;
		let mut n_left_visited: usize = 0;
		let mut scc_split_detected = false;
		for i in changed_scc.ones() {
			let scc_end = self.partition.block_end(i, ctx);
			for var_idx in i..scc_end {
				if self.tarjan.dfs_index[var_idx] == 0 {
					self.tarjan_dfs::<E>(
						var_idx,
						&mut next_dfs_index,
						&mut n_left_visited,
						&mut scc_split_detected,
						ctx,
					)?;
				}
			}
		}
		Ok(())
	}

	/// Build a Hall-set explanation over `members`.
	///
	/// For the set `S = members`, computes
	///   `dom_lb = min_{v in S} lb(v)`,
	///   `dom_ub = max_{v in S} ub(v)`,
	///   `holes  = { x in [dom_lb, dom_ub] : x not in dom(v) for any v in S }`,
	/// and emits, for each `v in S`: `v >= dom_lb`, `v <= dom_ub`, and `v != x`
	/// for every `x in holes`. The reason pins each member into the shared
	/// window minus the union's complement, so a Hall set of size `|S|`
	/// occupying `|S|` values can be reconstructed from the reason alone.
	///
	/// This is the form Régin's algorithm requires for both UNSAT conflicts
	/// (no augmenting path) and value-removal explanations (SCC pruning).
	/// `get_lit` lets the caller choose between `lit` (propagation) and
	/// `lit_relaxed` (explanation), which live in different traits with
	/// different context mutability.
	fn build_hall_set_reason<C, A, F>(
		&self,
		ctx: &mut C,
		members: &[usize],
		mut get_lit: F,
	) -> Vec<A>
	where
		C: ReasoningContext,
		I: IntInspectionActions<C>,
		F: FnMut(&I, &mut C, IntLitMeaning) -> A,
	{
		// Pass 1: dom_lb / dom_ub from bounds only — cheap and lets us size
		// the union bitset to the [dom_lb, dom_ub] window (typically far
		// smaller than the absolute union-domain span).
		let mut dom_lb = IntVal::MAX;
		let mut dom_ub = IntVal::MIN;
		for &vid in members {
			let (lb, ub) = self.graph.vars[vid].bounds(ctx);
			dom_lb = cmp::min(dom_lb, lb);
			dom_ub = cmp::max(dom_ub, ub);
		}
		let window = (dom_ub - dom_lb + 1) as usize;

		// Pass 2: union of member domains, window-indexed.
		let mut union_bits = FixedBitSet::with_capacity(window);
		for &vid in members {
			for val in self.graph.vars[vid].domain(ctx).iter().flatten() {
				union_bits.insert((val - dom_lb) as usize);
			}
		}

		// Pass 3: emit per-member literals, deriving holes inline from the
		// bitset's zero positions (no separate holes Vec).
		let n_holes = window - union_bits.count_ones(..);
		let mut reason: Vec<A> = Vec::with_capacity(members.len() * (2 + n_holes));
		for &vid in members {
			let var = &self.graph.vars[vid];
			reason.push(get_lit(var, ctx, IntLitMeaning::GreaterEq(dom_lb)));
			reason.push(get_lit(var, ctx, IntLitMeaning::Less(dom_ub + 1)));
			for hole_idx in union_bits.zeroes() {
				reason.push(get_lit(
					var,
					ctx,
					IntLitMeaning::NotEq(dom_lb + hole_idx as IntVal),
				));
			}
		}
		reason
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		constraints::{
			int_linear::IntLinearLessEqBounds,
			int_unique::{IntUniqueBounds, IntUniqueDomain, IntUniqueValue},
		},
		model::Model,
		solver::{LiteralStrategy, Solver, Status, Valuation},
	};

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_1() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueBounds::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}
	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_2() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(2..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let d = slv
			.new_int_decision(2..=5)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let e = slv
			.new_int_decision(3..=6)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let f = slv
			.new_int_decision(1..=6)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueBounds::post(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_3() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(3..=6)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(2..=5)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let d = slv
			.new_int_decision(2..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let e = slv
			.new_int_decision(3..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let f = slv
			.new_int_decision(1..=6)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueBounds::post(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_unsat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueBounds::post(&mut slv, vec![a, b, c]);
		IntLinearLessEqBounds::post(&mut slv, vec![-a, -b, -c], -8);
		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueValue::post(&mut slv, vec![a, b, c]);

		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_unsat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueValue::post(&mut slv, vec![a, b, c]);

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_all_different_domain_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_domain_unsat() {
		// Three variables on {1,2}: Hall set, no matching exists.
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_all_different_domain_filtering() {
		// Régin-style example: {1,2}, {1,2}, {1,2,3}. The Hall set {a,b} on
		// {1,2} should prune 1 and 2 from c, leaving c = 3.
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=3)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		IntUniqueDomain::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| {
			sol.iter().all_unique() && sol[2] == crate::solver::Value::Int(3)
		});
	}

	#[test]
	#[traced_test]
	fn test_gapped_domain_regression() {
		let mut prb = Model::default();
		let prev: Vec<_> = [
			IntSet::from_iter([15..=15, 20..=20]),
			(20..=20).into(),
			IntSet::from_iter([15..=15, 20..=20]),
		]
		.into_iter()
		.map(|domain| prb.new_int_decision(domain))
		.collect();

		assert!(prb.unique(prev.iter().copied()).post().is_err());
	}

	fn test_sudoku(grid: &[&str], expected: Status) {
		debug_assert_eq!(grid.len(), 9);
		debug_assert!(grid.iter().all(|row| row.len() == 9));

		let mut slv: Solver = Solver::default();
		// create variables and add int_unique propagator for each row
		let all_vars: Vec<_> = grid
			.iter()
			.map(|row| {
				let vars: Vec<_> = row
					.chars()
					.map(|c| {
						if c.is_ascii_digit() {
							let num = IntVal::from(c.to_digit(10).unwrap());
							num.into()
						} else {
							slv.new_int_decision(1..=9)
								.order_literals(LiteralStrategy::Eager)
								.direct_literals(LiteralStrategy::Eager)
								.view()
						}
					})
					.collect();

				IntUniqueValue::post(&mut slv, vars.clone());
				vars
			})
			.collect();

		// add int_unique propagator for each column
		for (i, _) in grid.iter().enumerate() {
			let col_vars: Vec<_> = grid
				.iter()
				.enumerate()
				.map(|(j, _)| all_vars[j][i])
				.collect();

			IntUniqueValue::post(&mut slv, col_vars);
		}
		// add int_unique propagator for each 3 by 3 grid
		for i in 0..3 {
			for j in 0..3 {
				let mut block_vars: Vec<_> = Vec::with_capacity(grid.len());
				for x in 0..3 {
					for y in 0..3 {
						block_vars.push(all_vars[3 * i + x][3 * j + y]);
					}
				}

				IntUniqueValue::post(&mut slv, block_vars);
			}
		}
		assert_eq!(
			slv.solve()
				.on_solution(|sol| {
					(0..9).for_each(|r| {
						let row = all_vars[r].iter().map(|&v| v.val(sol)).collect_vec();
						assert!(
							row.iter().all_unique(),
							"Values in row {r} are not all different: {row:?}",
						);
					});
					(0..9).for_each(|c| {
						let col = all_vars.iter().map(|row| row[c].val(sol)).collect_vec();
						assert!(
							col.iter().all_unique(),
							"Values in column {c} are not all different: {col:?}",
						);
					});
					(0..3).for_each(|i| {
						(0..3).for_each(|j| {
							let block = (0..3)
								.flat_map(|x| (0..3).map(move |y| (x, y)))
								.map(|(x, y)| all_vars[3 * i + x][3 * j + y].val(sol))
								.collect_vec();
							assert!(
								block.iter().all_unique(),
								"Values in block ({i}, {j}) are not all different: {block:?}",
							);
						});
					});
				})
				.satisfy(),
			expected
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_1() {
		test_sudoku(
			&[
				"2581.4.37",
				"936827514",
				"47153.28.",
				"7152.3.4.",
				"849675321",
				"36241..75",
				"1249..753",
				"593742168",
				"687351492",
			],
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_2() {
		test_sudoku(
			&[
				"...2.5...",
				".9....73.",
				"..2..9.6.",
				"2.....4.9",
				"....7....",
				"6.9.....1",
				".8.4..1..",
				".63....8.",
				"...6.8...",
			],
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_3() {
		test_sudoku(
			&[
				"3..9.4..1",
				"..2...4..",
				".61...79.",
				"6..247..5",
				".........",
				"2..836..4",
				".46...23.",
				"..9...6..",
				"5..3.9..8",
			],
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_4() {
		test_sudoku(
			&[
				"....1....",
				"3.14..86.",
				"9..5..2..",
				"7..16....",
				".2.8.5.1.",
				"....97..4",
				"..3..4..6",
				".48..69.7",
				"....8....",
			],
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_5() {
		test_sudoku(
			&[
				"..4..3.7.",
				".8..7....",
				".7...82.5",
				"4.....31.",
				"9.......8",
				".15.....4",
				"1.69...3.",
				"....2..6.",
				".2.4..5..",
			],
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
	fn test_sudoku_6() {
		test_sudoku(
			&[
				".43.8.25.",
				"6........",
				".....1.94",
				"9....4.7.",
				"...6.8...",
				".1.2....3",
				"82.5.....",
				"........5",
				".34.9.71.",
			],
			Status::Satisfied,
		);
	}
}
