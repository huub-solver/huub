//! Bounds-consistent propagator for the integer `unique` constraint.
//!
//! Implements López-Ortiz/Quimper/van Beek's O(n log n) bounds-consistency
//! algorithm: sort variables by their bounds, walk the bound positions with a
//! tree of critical capacities, detect Hall intervals, and tighten the bounds
//! of any variable whose domain straddles a discovered Hall interval.

use std::cmp;

use crate::{
	IntVal,
	actions::{InitActions, IntPropCond, PostingActions, ReasoningEngine},
	constraints::{IntSolverActions, Propagator},
	solver::{IntLitMeaning, engine::Engine, queue::PriorityLevel},
};

/// Bounds consistent propagator for the integer `unique` constraint.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntUniqueBounds<I> {
	/// List of integer variables that must take different values.
	pub(crate) vars: Vec<I>,
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

/// Information that is tracked for each variable for the propagation of
/// [`IntUniqueBounds`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UniqueVarMeta {
	/// Transition for the variable's position in the Hall interval tree.
	next: usize,
	/// Minimum index in the [`IntUniqueBounds::bounds`] vector
	min_rank: usize,
	/// Maximum index in the [`IntUniqueBounds::bounds`] vector
	max_rank: usize,
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

		for i in 0..self.vars.len() {
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
					self.vars[self.max_sorted[i]].lit(ctx, IntLitMeaning::GreaterEq(hall_min)),
				);
				while self.bounds[k] > hall_min {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						reason.push(self.vars[l].lit(ctx, IntLitMeaning::GreaterEq(hall_min)));
						reason.push(self.vars[l].lit(ctx, IntLitMeaning::Less(hall_max)));
						l = self.var_info[l].next;
					}
					k -= 1;
				}

				self.vars[self.max_sorted[i]].tighten_min(ctx, hall_max, |_, sink| {
					sink.extend(reason);
				})?;
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

		for i in (0..self.vars.len()).rev() {
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
				reason.push(self.vars[self.min_sorted[i]].lit(ctx, IntLitMeaning::Less(hall_max)));
				while self.bounds[k] < hall_max {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						reason.push(self.vars[l].lit(ctx, IntLitMeaning::GreaterEq(hall_min)));
						reason.push(self.vars[l].lit(ctx, IntLitMeaning::Less(hall_max)));
						l = self.var_info[l].next;
					}
					k += 1;
				}

				self.vars[self.min_sorted[i]].tighten_max(ctx, hall_min - 1, |_, sink| {
					sink.extend(reason);
				})?;
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
			vars,
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
		let size: usize = self.vars.len();

		for (i, v) in self.vars.iter().enumerate() {
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
		for v in &self.vars {
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

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		constraints::{int_linear::IntLinearLessEqBounds, int_unique::IntUniqueBounds},
		solver::{LiteralStrategy, Solver},
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
}
