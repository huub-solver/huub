//! Structure and algorithms for the integer all different constraint, which
//! enforces that a list of integer variables each take a different value.

use std::{cmp, iter::repeat_with};

use itertools::{Either, Itertools};
use rangelist::{IntervalIterator, RangeList};
use tracing::trace;

use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView, IntViewInner,
	},
	IntDecision, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `all_different_int` constraint within a model.
///
/// This constraint enforces that all the given integer decisions take different
/// values.
pub struct IntAllDifferent {
	/// List of integer decision variables that must take different values.
	pub(crate) vars: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `all_different_int` constraint.
pub struct IntAllDifferentBounds {
	/// List of integer variables that must take different values.
	vars: Vec<IntView>,
	interval: Vec<Interval>,
	/// Struct to store information about variable
	min_sorted: Vec<usize>,
	/// Index (from vars) of all variables sorted by min bound
	max_sorted: Vec<usize>,
	/// Index (from vars) of all variables sorted by max bound
	num_bounds: usize,
	/// Number of different bounds
	bounds: Vec<IntVal>,
	/// Ordered vector of all different max and min bounds with dummies
	t: Vec<usize>,
	d: Vec<IntVal>,
	h: Vec<usize>,
	bucket: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `all_different_int` constraint.
pub struct IntAllDifferentValue {
	/// List of integer variables that must take different values.
	vars: Vec<IntView>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Interval {
	next: usize,
	/// Minimum observed value of decision variable
	min: IntVal,
	/// Maximum observed value of decision variable
	max: IntVal,
	/// Minimum index in the bounds vector
	min_rank: usize,
	/// Maximum index in the bounds vector
	max_rank: usize,
}

impl<S: SimplificationActions> Constraint<S> for IntAllDifferent {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let (vals, vars): (Vec<_>, Vec<_>) = self.vars.iter().partition_map(|&var| {
			if let Some(val) = actions.get_int_val(var) {
				Either::Left(val)
			} else {
				Either::Right(var)
			}
		});
		self.vars = vars;
		let neg_dom = RangeList::from_iter(vals.iter().map(|&i| i..=i));
		if neg_dom.card() != vals.len() {
			return Err(ReformulationError::TrivialUnsatisfiable);
		}
		if self.vars.is_empty() {
			return Ok(SimplificationStatus::Subsumed);
		}
		if vals.is_empty() {
			return Ok(SimplificationStatus::Fixpoint);
		}
		for &v in &self.vars {
			actions.set_int_not_in_set(v, &neg_dom)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		IntAllDifferentValue::new_in(slv, vars);
		Ok(())
	}
}

impl IntAllDifferentBounds {
	fn filter_lower<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let size: usize = self.vars.len();
		let mut j: usize;
		let mut z: usize;
		let mut w: usize;

		for i in 1..=self.num_bounds + 1 {
			self.h[i] = i - 1;
			self.t[i] = self.h[i];
			self.d[i] = self.bounds[i] - self.bounds[i - 1];
			self.bucket[i] = usize::MAX;
		}

		for i in 0..size {
			let max_rank = self.interval[self.max_sorted[i]].max_rank;
			let min_rank = self.interval[self.max_sorted[i]].min_rank;
			trace!(
				"var {:?}, [{:?}, {:?}))",
				self.max_sorted[i],
				self.bounds[min_rank],
				self.bounds[max_rank]
			);

			z = IntAllDifferentBounds::path_max(&self.t, min_rank + 1);
			j = self.t[z];
			self.d[z] -= 1;
			self.interval[self.max_sorted[i]].next = self.bucket[z];
			self.bucket[z] = self.max_sorted[i];
			if self.d[z] == 0 {
				self.t[z] = z + 1;
				z = IntAllDifferentBounds::path_max(&self.t, self.t[z]);
				self.t[z] = j;
			}
			IntAllDifferentBounds::path_set(&mut self.t, min_rank + 1, z, z);

			if self.h[min_rank] > min_rank {
				w = IntAllDifferentBounds::path_max(&self.h, self.h[min_rank]);
				let hall_max: IntVal = self.bounds[w];
				let mut hall_min: IntVal = self.bounds[min_rank];
				let mut k: usize = w;
				while self.bounds[k] > hall_min {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						hall_min = cmp::min(hall_min, self.interval[l].min);
						l = self.interval[l].next;
					}
					k -= 1;
				}

				k = w;
				trace!(hall_min, hall_max, "hall interval");
				let mut reason = Vec::new();
				trace!(
					"Reason [[ var {:?}: [{:?}, {:?}) >= {:?}]",
					i,
					self.interval[self.max_sorted[i]].min,
					self.interval[self.max_sorted[i]].max,
					hall_min
				);
				reason.push(actions.get_int_lit(
					self.vars[self.max_sorted[i]],
					IntLitMeaning::GreaterEq(hall_min),
				));
				while self.bounds[k] > hall_min {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						trace!(
							"Reason [[var {:?} [{:?}, {:?}) >= {:?}]",
							l,
							self.interval[l].min,
							self.interval[l].max,
							hall_max
						);
						reason.push(
							actions.get_int_lit(self.vars[l], IntLitMeaning::GreaterEq(hall_min)),
						);
						trace!(
							"Reason [[ var {:?} [{:?}, {:?}) < {:?}]",
							l,
							self.interval[l].min,
							self.interval[l].max,
							hall_max
						);
						reason
							.push(actions.get_int_lit(self.vars[l], IntLitMeaning::Less(hall_max))); // since [x<d+1] = [x<=d]
						l = self.interval[l].next;
					}
					k -= 1;
				}

				actions.set_int_lower_bound(self.vars[self.max_sorted[i]], hall_max, reason)?; //reason type might be an issue
				self.interval[self.max_sorted[i]].min = hall_max;
				IntAllDifferentBounds::path_set(&mut self.h, min_rank, w, w);
			}
			if self.d[z] == self.bounds[z] - self.bounds[max_rank] {
				let h_max_rank = self.h[max_rank];
				// Save Hall interval
				IntAllDifferentBounds::path_set(&mut self.h, h_max_rank, j - 1, max_rank);
				self.h[max_rank] = j - 1;
			}
		}
		Ok(())
	}

	fn filter_upper<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let size: usize = self.vars.len();
		let mut j: usize;
		let mut z: usize;
		let mut w: usize;

		for i in 0..=self.num_bounds {
			self.h[i] = i + 1;
			self.t[i] = self.h[i];
			self.d[i] = self.bounds[i + 1] - self.bounds[i];
			self.bucket[i] = usize::MAX;
		}

		for i in (0..size).rev() {
			let max_rank = self.interval[self.min_sorted[i]].max_rank;
			let min_rank = self.interval[self.min_sorted[i]].min_rank;

			trace!(
				"var {:?}, [{:?}, {:?})",
				self.min_sorted[i],
				self.bounds[min_rank],
				self.bounds[max_rank]
			);
			z = IntAllDifferentBounds::path_min(&self.t, max_rank - 1);
			j = self.t[z];
			self.d[z] -= 1;
			self.interval[self.min_sorted[i]].next = self.bucket[z];
			self.bucket[z] = self.min_sorted[i];
			if self.d[z] == 0 {
				self.t[z] = z - 1;
				z = IntAllDifferentBounds::path_min(&self.t, self.t[z]);
				self.t[z] = j;
			}
			IntAllDifferentBounds::path_set(&mut self.t, max_rank - 1, z, z);

			if self.h[max_rank] < max_rank {
				w = IntAllDifferentBounds::path_min(&self.h, self.h[max_rank]);
				let hall_min: IntVal = self.bounds[w];
				let mut hall_max: IntVal = self.bounds[max_rank];
				let mut k: usize = w;
				while self.bounds[k] < hall_max {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						hall_max = cmp::max(hall_max, self.interval[l].max);
						l = self.interval[l].next;
					}
					k += 1;
				}

				k = w;
				trace!(hall_min, hall_max, "hall interval");
				let mut reason = Vec::new();
				reason.push(
					actions
						.get_int_lit(self.vars[self.min_sorted[i]], IntLitMeaning::Less(hall_max)),
				);
				trace!(
					"Reason [[ var {:?}: [{:?}, {:?}) < {:?}]",
					i,
					self.interval[self.min_sorted[i]].min,
					self.interval[self.min_sorted[i]].max,
					hall_max
				);
				while self.bounds[k] < hall_max {
					let mut l = self.bucket[k];
					while l != usize::MAX {
						reason.push(
							actions.get_int_lit(self.vars[l], IntLitMeaning::GreaterEq(hall_min)),
						);
						trace!(
							"Reason [[ var {:?}: [{:?}, {:?}) >= {:?}]",
							l,
							self.interval[l].min,
							self.interval[l].max,
							hall_min
						);
						reason
							.push(actions.get_int_lit(self.vars[l], IntLitMeaning::Less(hall_max)));
						trace!(
							"Reason [[ var {:?}: [{:?}, {:?}) < {:?}]",
							l,
							self.interval[l].min,
							self.interval[l].max,
							hall_max
						);
						l = self.interval[l].next;
					}
					k += 1;
				}
				trace!(
					"Setting upper bound of variable {:?} with bounds [{:?}, {:?})  to {:?}",
					self.min_sorted[i],
					self.interval[self.min_sorted[i]].min,
					self.interval[self.min_sorted[i]].max,
					hall_min
				);
				actions.set_int_upper_bound(self.vars[self.min_sorted[i]], hall_min - 1, reason)?;
				self.interval[self.min_sorted[i]].max = hall_min;

				IntAllDifferentBounds::path_set(&mut self.h, max_rank, w, w);
			}

			if self.d[z] == self.bounds[min_rank] - self.bounds[z] {
				let h_min_rank = self.h[min_rank];
				// Save Hall interval
				IntAllDifferentBounds::path_set(&mut self.h, h_min_rank, j + 1, min_rank);
				self.h[min_rank] = j + 1;
			}
		}
		Ok(())
	}

	/// Create a new [`AllDifferentBounds`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P, vars: Vec<IntView>) {
		let interval = repeat_with(|| Interval {
			next: 0,
			min: 0,
			max: 0,
			min_rank: 0,
			max_rank: 0,
		})
		.take(vars.len())
		.collect();
		let min_sorted: Vec<_> = (0..vars.len()).collect();
		let max_sorted: Vec<_> = (0..vars.len()).collect();

		let num_bounds: usize = 0;
		let n = 2 * vars.len() + 2;
		let enqueue = vars
			.iter()
			.any(|v| matches!(v, IntView(IntViewInner::Const(_))));
		let prop = solver.add_propagator(
			Box::new(Self {
				vars: vars.clone(),
				interval,
				min_sorted,
				max_sorted,
				num_bounds,
				bounds: vec![0; n],
				t: vec![0; n],
				d: vec![0; n],
				h: vec![0; n],
				bucket: vec![0; n],
			}),
			PriorityLevel::Low,
		);
		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
		if enqueue {
			solver.enqueue_now(prop);
		}
	}

	/// Follows path i, t[i], t[t[i]], ... until we stop increasing
	fn path_max(t: &Vec<usize>, mut i: usize) -> usize {
		while t[i] > i {
			i = t[i];
		}
		i
	}

	/// Follows path i, t[i], t[t[i]], ... until we stop decreasing
	fn path_min(t: &Vec<usize>, mut i: usize) -> usize {
		while t[i] < i {
			i = t[i];
		}
		i
	}

	/// Sets everything in t, between start and end to to e.g.
	/// start = 2, end = 3, to = 5
	/// t = 0->4->3->1->2->0 gives:
	/// 0->5->5->5->2->0
	fn path_set(t: &mut Vec<usize>, start: usize, end: usize, to: usize) -> () {
		let mut k;
		let mut l = start;
		while l != end {
			k = l;
			l = t[k];
			t[k] = to;
		}
	}

	/// Sorts max_sorted and min_sorted and sets the bounds vector
	fn sort<P: PropagationActions>(&mut self, actions: &mut P) {
		let size: usize = self.vars.len();

		for i in 0..size {
			self.interval[i].min = actions.get_int_lower_bound(self.vars[i]);
			self.interval[i].max = actions.get_int_upper_bound(self.vars[i]) + 1;
		}

		self.min_sorted.sort_by_key(|&i| self.interval[i].min);
		self.max_sorted.sort_by_key(|&i| self.interval[i].max);

		let mut min: IntVal = self.interval[self.min_sorted[0]].min;
		let mut max: IntVal = self.interval[self.max_sorted[0]].max;
		let mut last: IntVal = min - 2;
		self.bounds[0] = min - 2; // Dummy

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
				self.interval[self.min_sorted[i]].min_rank = self.num_bounds;
				i += 1;
				if i < size {
					min = self.interval[self.min_sorted[i]].min;
				}
			} else {
				if max != last {
					self.num_bounds += 1;
					last = max;
					self.bounds[self.num_bounds] = max;
				}
				self.interval[self.max_sorted[j]].max_rank = self.num_bounds;
				j += 1;
				if j == size {
					break;
				}
				max = self.interval[self.max_sorted[j]].max;
			}
		}
		self.bounds[self.num_bounds + 1] = self.bounds[self.num_bounds] + 2; // Dummy
	}
}

impl<P, E> Propagator<P, E> for IntAllDifferentBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "all_different", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		self.sort(actions);
		self.filter_lower(actions)?;
		self.filter_upper(actions)?;
		Ok(())
	}
}

impl IntAllDifferentValue {
	/// Create a new [`AllDifferentIntValue`] propagator and post it in the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P, vars: Vec<IntView>) {
		let enqueue = vars
			.iter()
			.any(|v| matches!(v, IntView(IntViewInner::Const(_))));
		let prop = solver.add_propagator(Box::new(Self { vars: vars.clone() }), PriorityLevel::Low);
		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Fixed);
		}
		if enqueue {
			solver.enqueue_now(prop);
		}
	}
}

impl<P, E> Propagator<P, E> for IntAllDifferentValue
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "all_different", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		for (i, &var) in self.vars.iter().enumerate() {
			if let Some(val) = actions.get_int_val(var) {
				let reason = actions.get_int_lit(var, IntLitMeaning::Eq(val));
				for (j, &other) in self.vars.iter().enumerate() {
					let other_val = actions.get_int_val(other);
					if j != i && (other_val.is_none() || other_val.unwrap() == val) {
						actions.set_int_not_eq(other, val, reason)?;
					}
				}
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		all_different_int,
		constraints::{
			int_all_different::{IntAllDifferentBounds, IntAllDifferentValue},
			int_linear::IntLinearLessEqBounds,
		},
		solver::{
			int_var::{EncodingType, IntVar},
			IntView, SolveResult, Solver,
		},
		IntVal, Model,
	};

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_1() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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
		IntAllDifferentBounds::new_in(&mut slv, vec![a, b, c]);
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}
	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_2() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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

		IntAllDifferentBounds::new_in(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_sat_3() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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

		IntAllDifferentBounds::new_in(&mut slv, vec![a, b, c, d, e, f]);
		slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_bounds_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((1..=3).into());
		let b = prb.new_int_var((1..=3).into());
		let c = prb.new_int_var((1..=3).into());
		prb += all_different_int(vec![a, b, c]);
		prb += (a + b + c).geq(8);
		prb.assert_unsatisfiable()
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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

		IntAllDifferentValue::new_in(&mut slv, vec![a, b, c]);

		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_unsat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
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

		IntAllDifferentValue::new_in(&mut slv, vec![a, b, c]);

		slv.assert_unsatisfiable();
	}

	fn test_sudoku(grid: &[&str], expected: SolveResult) {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let mut all_vars = vec![];
		// create variables and add all different propagator for each row
		grid.iter().for_each(|row| {
			let mut vars = Vec::with_capacity(row.len());
			for c in row.chars() {
				if c.is_ascii_digit() {
					let num = IntVal::from(c.to_digit(10).unwrap());
					vars.push(num.into());
				} else {
					vars.push(IntVar::new_in(
						&mut slv,
						RangeList::from_iter([1..=9]),
						EncodingType::Eager,
						EncodingType::Eager,
					));
				}
			}

			IntAllDifferentValue::new_in(&mut slv, vars.clone());

			all_vars.push(vars);
		});
		// add all different propagator for each column
		for i in 0..9 {
			let col_vars: Vec<IntView> = (0..9).map(|j| all_vars[j][i]).collect();

			IntAllDifferentValue::new_in(&mut slv, col_vars);
		}
		// add all different propagator for each 3 by 3 grid
		for i in 0..3 {
			for j in 0..3 {
				let mut block_vars: Vec<IntView> = Vec::with_capacity(9);
				for x in 0..3 {
					for y in 0..3 {
						block_vars.push(all_vars[3 * i + x][3 * j + y]);
					}
				}

				IntAllDifferentValue::new_in(&mut slv, block_vars);
			}
		}
		assert_eq!(
			slv.solve(|val| {
				(0..9).for_each(|r| {
					let row = all_vars[r].iter().map(|&v| val(v.into())).collect_vec();
					assert!(
						row.iter().all_unique(),
						"Values in row {} are not all different: {:?}",
						r,
						row
					);
				});
				(0..9).for_each(|c| {
					let col = all_vars.iter().map(|row| val(row[c].into())).collect_vec();
					assert!(
						col.iter().all_unique(),
						"Values in column {} are not all different: {:?}",
						c,
						col
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
							"Values in block ({}, {}) are not all different: {:?}",
							i,
							j,
							block
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
