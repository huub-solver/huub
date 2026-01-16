//! Structure and algorithms for the integer all different constraint, which
//! enforces that a list of integer variables each take a different value.

use std::{cmp, ops::AddAssign};

use itertools::{Either, Itertools};
use rangelist::RangeList;

use crate::{
	IntDecision, IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInspectionActions, IntSimplificationActions,
		ReasoningEngine, ReformulationActions, TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	reformulate::ReformulationError,
	solver::{
		IntLitMeaning, IntView,
		activation_list::{IntEvent, IntPropCond},
		queue::PriorityLevel,
	},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Information that is tracked for each variable for the propagation of
/// [`IntAllDifferentBounds`]
struct AllDiffVarMeta {
	/// Transition for the variable's position in the Hall interval tree.
	next: usize,
	/// Minimum index in the [`IntAllDifferentBounds::bounds`] vector
	min_rank: usize,
	/// Maximum index in the [`IntAllDifferentBounds::bounds`] vector
	max_rank: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `all_different_int` constraint within a model.
///
/// This constraint enforces that all the given integer decisions take different
/// values.
pub struct IntAllDifferent {
	/// List of integer decision variables that must take different values.
	pub(crate) prop: IntAllDifferentBounds<IntDecision>,
	/// Whether to enable the bounds consistent propagator.
	///
	/// Defaults to `true`.
	pub(crate) bounds_prop: Option<bool>,
	/// Whether to enable the value consistent propagator.
	///
	/// Defaults to `false`.
	pub(crate) value_prop: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `all_different_int` constraint.
pub struct IntAllDifferentBounds<I> {
	/// List of integer variables that must take different values.
	pub(crate) var: Vec<I>,
	/// Struct to store information about variable
	var_info: Vec<AllDiffVarMeta>,
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
	/// Ordered vector of all different max and min bounds with dummies
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `all_different_int` constraint.
pub struct IntAllDifferentValue<I> {
	/// List of integer variables that must take different values.
	vars: Vec<I>,
	/// List of (indexes of) variable signaled to be fixed.
	action_list: Vec<usize>,
}

impl IntAllDifferent {
	/// Returns whether a bounds consistent propagator will be posted when
	/// creating a [`Solver`] object.
	pub fn bounds_consistent_propagator_enabled(&self) -> bool {
		self.bounds_prop.unwrap_or(true)
	}

	/// Ensure the use of the bounds consistent propagator when this constraint
	/// is posted to a [`Solver`] object.
	///
	/// Note that this method does not affect whether a value consistent
	/// propagator will be used or not.
	pub fn use_bounds_consistent_propagator(&mut self, enable: bool) {
		self.bounds_prop = Some(enable);
	}

	/// Ensure the use of the value consistent propagator when this constraint
	/// is posted to a [`Solver`] object.
	///
	/// Note that this method does not affect whether a bounds consistent
	/// propagator will be used or not.
	pub fn use_value_consistent_propagator(&mut self, enable: bool) {
		self.value_prop = Some(enable);
	}

	/// Returns whether a value consistent propagator will be posted when
	/// creating a [`Solver`] object.
	pub fn value_consistent_propagator_enabled(&self) -> bool {
		self.value_prop.unwrap_or(false)
	}
}

impl<E> Constraint<E> for IntAllDifferent
where
	E: ReasoningEngine,
	IntDecision: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		// TODO: Should this just use the value consistent propagator, or should this
		// not be done by the bounds consistent propagator?
		let (vals, vars): (Vec<_>, Vec<_>) =
			self.prop.var.iter().enumerate().partition_map(|(i, &var)| {
				if let Some(val) = var.val(ctx) {
					Either::Left((i, val))
				} else {
					Either::Right(var)
				}
			});
		if !vals.is_empty() {
			let neg: RangeList<_> = vals.iter().map(|&(_, v)| v..=v).collect();
			for var in &vars {
				var.set_not_in_set(ctx, &neg, |ctx: &mut E::PropagationCtx<'_>| {
					vals.iter()
						.map(|&(i, _)| self.prop.var[i].val_lit(ctx).unwrap())
						.collect_vec()
				})?;
			}
			// Shrink variable array (and related caches)
			let n = 2 * vars.len() + 2;
			self.prop.lb_cache.shrink_to(n);
			self.prop.ub_cache.shrink_to(n);
			self.prop.min_sorted = (0..vars.len()).collect();
			self.prop.max_sorted = (0..vars.len()).collect();
			self.prop.bounds.shrink_to(n);
			self.prop.predecessor.shrink_to(n);
			self.prop.diff.shrink_to(n);
			self.prop.hall_interval.shrink_to(n);
			self.prop.bucket.shrink_to(n);
			self.prop.var = vars;
		}

		if self.prop.var.iter().all(|v| v.val(ctx).is_some()) {
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(
		&self,
		slv: &mut dyn ReformulationActions,
		_model_trail: &dyn TrailingActions,
	) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.prop.var.iter().map(|v| slv.solver_int(*v)).collect();
		// propagation should have removed any fixed values
		debug_assert!(vars.iter().all(|v| v.val(slv).is_none()));
		if self.value_consistent_propagator_enabled() {
			IntAllDifferentValue::post(slv, vars.clone());
		}
		if self.bounds_consistent_propagator_enabled() {
			IntAllDifferentBounds::post(slv, vars);
		}
		Ok(())
	}
}

impl<E> Propagator<E> for IntAllDifferent
where
	E: ReasoningEngine,
	IntDecision: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		self.prop.initialize(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.prop.propagate(ctx)
	}
}

impl<I> IntAllDifferentBounds<I> {
	/// Filter the lower bounds of the considered variables
	fn filter_lower<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
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

				self.var[self.max_sorted[i]].set_lower_bound(ctx, hall_max, reason)?;
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
	fn filter_upper<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
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

				self.var[self.min_sorted[i]].set_upper_bound(ctx, hall_min - 1, reason)?;
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

	/// Create a new [`IntAllDifferentBounds`] propagator.
	pub(crate) fn new(vars: Vec<I>) -> Self {
		let interval = vec![
			AllDiffVarMeta {
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
	/// # use huub::constraints::int_all_different::IntAllDifferentBounds;
	/// let mut transition = vec![4, 2, 0, 1, 3, 0]; // giving e.g. 0 -> 4 -> 3 -> 1 -> 2 -> 0
	/// IntAllDifferentBounds::path_set(&mut transition, 2, 3, 5);
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

	/// Sorts max_sorted and min_sorted and sets the bounds vector
	fn sort<E>(&mut self, ctx: &mut E::PropagationCtx<'_>)
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
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

impl IntAllDifferentBounds<IntView> {
	/// Create a new [`IntAllDifferentBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<IntView>)
	where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self::new(vars));
	}
}

impl<E, I> Propagator<E> for IntAllDifferentBounds<I>
where
	E: ReasoningEngine,
	I: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut <E as ReasoningEngine>::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in &self.var {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	#[tracing::instrument(name = "all_different", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		self.sort(ctx);
		self.filter_lower(ctx)?;
		self.filter_upper(ctx)?;
		Ok(())
	}
}

impl IntAllDifferentValue<IntView> {
	/// Create a new [`IntAllDifferentValue`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, vars: Vec<IntView>)
	where
		E: AddAssign<BoxedPropagator> + ?Sized,
	{
		*solver += Box::new(Self {
			vars: vars.clone(),
			action_list: Vec::new(),
		});
	}
}

impl<E, I> Propagator<E> for IntAllDifferentValue<I>
where
	E: ReasoningEngine,
	I: SolverIntView<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationCtx<'_>) {
		// We forget any previously remembered fixed decisions.
		self.action_list.clear();
	}

	fn advise_of_int_change(
		&mut self,
		_: &mut E::NotificationCtx<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		// We remember that the decision at index `data` has been fixed to a value.
		debug_assert_eq!(event, IntEvent::Fixed);
		self.action_list.push(data as usize);
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		// Let the propagator be advised when each specific decision is fixed to a
		// value, with the index of the decision.
		for (i, v) in self.vars.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		// Advise the propagator of backtracking to clear the list of fixed decision
		// (indices).
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(name = "all_different", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
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
					v.set_not_eq(ctx, val, reason)?;
				}
			}
		}
		// We clear the list of indices of fixed decisions.
		self.action_list.clear();
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		constraints::{
			int_all_different::{IntAllDifferentBounds, IntAllDifferentValue},
			int_linear::IntLinearLessEqBounds,
		},
		solver::{
			SolveResult, Solver,
			int_var::{EncodingType, IntVar},
		},
	};

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_1() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		IntAllDifferentBounds::post(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}
	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_2() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let d = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let e = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=6]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let f = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=6]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntAllDifferentBounds::post(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_3() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=6]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let d = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let e = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let f = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=6]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntAllDifferentBounds::post(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_unsat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from(1..=3),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from(1..=3),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from(1..=3),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntAllDifferentBounds::post(&mut slv, vec![a, b, c]);
		IntLinearLessEqBounds::post(&mut slv, vec![-a, -b, -c], -8);
		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_sat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntAllDifferentValue::post(&mut slv, vec![a, b, c]);

		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_unsat() {
		let mut slv = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntAllDifferentValue::post(&mut slv, vec![a, b, c]);

		slv.assert_unsatisfiable();
	}

	fn test_sudoku(grid: &[&str], expected: SolveResult) {
		debug_assert_eq!(grid.len(), 9);
		debug_assert!(grid.iter().all(|row| row.len() == 9));

		let mut slv: Solver = Solver::default();
		// create variables and add all different propagator for each row
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
							IntVar::new_in(
								&mut slv,
								RangeList::from_iter([1..=9]),
								EncodingType::Eager,
								EncodingType::Eager,
							)
						}
					})
					.collect();

				IntAllDifferentValue::post(&mut slv, vars.clone());
				vars
			})
			.collect();

		// add all different propagator for each column
		for (i, _) in grid.iter().enumerate() {
			let col_vars: Vec<_> = grid
				.iter()
				.enumerate()
				.map(|(j, _)| all_vars[j][i])
				.collect();

			IntAllDifferentValue::post(&mut slv, col_vars);
		}
		// add all different propagator for each 3 by 3 grid
		for i in 0..3 {
			for j in 0..3 {
				let mut block_vars: Vec<_> = Vec::with_capacity(grid.len());
				for x in 0..3 {
					for y in 0..3 {
						block_vars.push(all_vars[3 * i + x][3 * j + y]);
					}
				}

				IntAllDifferentValue::post(&mut slv, block_vars);
			}
		}
		assert_eq!(
			slv.solve(|val| {
				(0..9).for_each(|r| {
					let row = all_vars[r].iter().map(|&v| val(v.into())).collect_vec();
					assert!(
						row.iter().all_unique(),
						"Values in row {r} are not all different: {row:?}",
					);
				});
				(0..9).for_each(|c| {
					let col = all_vars.iter().map(|row| val(row[c].into())).collect_vec();
					assert!(
						col.iter().all_unique(),
						"Values in column {c} are not all different: {col:?}",
					);
				});
				(0..3).for_each(|i| {
					(0..3).for_each(|j| {
						let block = (0..3)
							.flat_map(|x| (0..3).map(move |y| (x, y)))
							.map(|(x, y)| val(all_vars[3 * i + x][3 * j + y].into()))
							.collect_vec();
						assert!(
							block.iter().all_unique(),
							"Values in block ({i}, {j}) are not all different: {block:?}",
						);
					});
				});
			}),
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
			SolveResult::Satisfied,
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
			SolveResult::Satisfied,
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
			SolveResult::Satisfied,
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
			SolveResult::Satisfied,
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
			SolveResult::Satisfied,
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
			SolveResult::Satisfied,
		);
	}
}
