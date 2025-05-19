//! Structure and algorithms for the value_precede_chain constraint, which
//! enforces that a fixed order of the first occurrences of a given list of
//! integers in a list of integer variables.

use std::cmp::{max, min};

use crate::{
	actions::{
		ExplanationActions, InspectionActions, PropagatorInitActions, ReformulationActions,
		SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, BoolView,
		IntLitMeaning, IntView,
	},
	IntDecision, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `seq_precede_chain_int` constraint within a model.
///
/// This constraint enforces that the first occurrences of all i>0 are ordered
/// in the given list.
pub struct IntSeqPrecedeChain {
	/// List of integer decision variables where first occurrences of all i>0 must
	/// be ordered.
	pub(crate) vars: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the `seq_precede_chain_int` constraint.
pub struct IntSeqPrecedeChainBounds {
	/// List of integer variables where first occurrences of all i>0 must be
	/// ordered.
	vars: Vec<IntView>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of i.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of i.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies
	/// `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i that has to occur.
	max_last: TrailedInt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `value_precede_chain_int` constraint within a model.
///
/// This constraint enforces that the first occurrences of the elements of the
/// given integer list in the list of integer decision variables are ordered
/// according to the given list.
pub struct IntValuePrecedeChain {
	/// List of integers that need to occur in order
	pub(crate) values: Vec<IntVal>,
	/// List of integer decision variables where first occurrences of specified
	/// values must be ordered.
	pub(crate) vars: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `value_precede_chain` constraint.
pub struct IntValuePrecedeChainValue {
	/// List of integers that need to occur in order
	values: Vec<IntVal>,
	/// List of integer variables where first occurrences of specified values must
	/// be ordered.
	vars: Vec<IntView>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of `values[i]`.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of `values[i]`.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies
	/// `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i such that `values[i]` has to occur.
	max_last: TrailedInt,
	/// Minimum value in values.
	min_val: IntVal,
	/// Maximum value in values.
	max_val: IntVal,
	/// Minimum value with `min_val<min_hole<max_val` such that min_hole is not an
	/// element of values.
	min_hole: IntVal,
	/// Used to iterate through the holes in values.
	next_hole: Vec<IntVal>,
	/// List of holes in values.
	holes: Vec<IntVal>,
	/// Reverse mapping of actual values to their indices in the `values` array
	mapping: Vec<Option<usize>>,
}

impl<S: SimplificationActions> Constraint<S> for IntSeqPrecedeChain {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let mut ub = 0;
		for &v in self.vars.iter() {
			if actions.check_int_in_domain(v, ub + 1) {
				ub += 1;
			}
			//todo if ub is not in the domain, more tight bounds could be propagated
			actions.set_int_upper_bound(v, ub)?;
		}
		// Variables that do not allow positive values are irrelevant.
		self.vars.retain(|&v| actions.get_int_upper_bound(v) > 0);
		if self.vars.is_empty() {
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		IntSeqPrecedeChainBounds::new_in(slv, vars);
		Ok(())
	}
}

impl IntSeqPrecedeChainBounds {
	/// Lower bound explanation: Could not have this value earlier (=upper bound
	/// explanation) and some later value requires the lower bound (recursive
	/// lower bound).
	fn explain_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		k: IntVal,
	) -> Vec<BoolView> {
		let mut v = self.explain_lower_recursive(actions, i + 1, k);
		v.extend(self.explain_upper(actions, i, k));
		v
	}
	/// Recursively explain a lower bound via 3 cases:
	/// - Lower bound of var i is above k - This is the value that required the
	///   earlier lower bound that is currently explained (end of recursion).
	/// - k is in the domain of var i - Go one step up and to the next variable.
	/// - k is not in the domain of var i - i can be anything else, go to next
	///   variable.
	fn explain_lower_recursive<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		k: IntVal,
	) -> Vec<BoolView> {
		if actions.get_int_lower_bound(self.vars[i]) > k {
			return vec![actions.get_int_lit(self.vars[i], IntLitMeaning::GreaterEq(k + 1))];
		}
		if actions.check_int_in_domain(self.vars[i], k) {
			return self.explain_lower_recursive(actions, i + 1, k + 1);
		}
		let mut v = self.explain_lower_recursive(actions, i + 1, k);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(k)));
		v
	}

	/// Upper bound explanation: All previous elements are smaller.
	fn explain_upper<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		k: IntVal,
	) -> Vec<BoolView> {
		self.vars
			.iter()
			.take(i)
			.map(|&v| actions.get_int_lit(v, IntLitMeaning::Less(k)))
			.collect()
	}

	/// Get the latest occurrence of k, or the maximum variable index if there is
	/// no latest.
	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(
			actions.get_trailed_int(self.last[k]),
			self.vars.len() as IntVal - 1,
		)
	}

	/// Do a full propagation run, requires checking all variables in both
	/// directions.
	fn initial_propagation<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
		// Current upper bound
		let mut up = 0;
		// Current lower bound
		let mut low = 0;

		// Forward pass to set upper bounds and capture the highest lower bound.
		for (i, &v) in self.vars.iter().enumerate() {
			let mut ub_v = actions.get_int_upper_bound(v);
			// Upper bound can only increase by 1, set new bound if larger values are in the domain.
			if ub_v > up + 1 {
				if actions.check_int_in_domain(v, up + 1) {
					ub_v = up + 1;
				}
				actions.set_int_upper_bound(self.vars[i], up + 1, |a: &mut P| {
					self.explain_upper(a, i, up + 1)
				})?;
			}
			// The current var is the first possibility to reach value up + 1.
			if ub_v == up + 1 {
				up += 1;
				let _ = actions.set_trailed_int(self.first[up as usize], i as IntVal);
				let _ = actions.set_trailed_int(self.first_val[i], up);
			}
			let lb_v = actions.get_int_lower_bound(v);
			// The lower bound will be needed for the backward pass.
			if low < lb_v {
				let _ = actions.set_trailed_int(self.last[lb_v as usize], i as IntVal);
				low = lb_v;
			}
		}
		// The highest lower bound is stored.
		let _ = actions.set_trailed_int(self.max_last, low);

		// Backward pass to set lower bounds.
		for (i, &v) in self.vars.iter().enumerate().rev() {
			// Lower bound is enforced if upper and lower bound coincide.
			if actions.get_trailed_int(self.first[low as usize]) == i as IntVal {
				actions.set_int_lower_bound(self.vars[i], low, |a: &mut P| {
					self.explain_lower(a, i, low)
				})?;
			}
			// Found possibility to use a lower value - reduce lower bound.
			if i as IntVal <= actions.get_trailed_int(self.last[low as usize])
				&& actions.check_int_in_domain(v, low)
			{
				let _ = actions.set_trailed_int(self.last[low as usize], i as IntVal);
				low -= 1;
			}
			// Stop early if no more lower bounds can be propagated.
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Create a new [`IntSeqPrecedeChainBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P, vars: Vec<IntView>) {
		let n = vars.len();
		let ub = vars.iter().fold(0, |u, &item| {
			if solver.get_int_upper_bound(item) > u {
				u + 1
			} else {
				u
			}
		});

		let first = (0..=ub).map(|_| solver.new_trailed_int(0)).collect();
		let last = (0..=ub)
			.map(|i| {
				if i == 0 {
					solver.new_trailed_int(IntVal::MIN)
				} else {
					solver.new_trailed_int(IntVal::MAX)
				}
			})
			.collect();
		let first_val = (0..n).map(|_| solver.new_trailed_int(0)).collect();
		let max_last = solver.new_trailed_int(0);

		let prop = solver.add_propagator(
			Box::new(Self {
				vars: vars.clone(),
				initialized: false,
				first,
				last,
				first_val,
				max_last,
			}),
			PriorityLevel::Low,
		);

		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Domain);
		}
		solver.enqueue_now(prop);
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as far
	/// as necessary.
	fn repair_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: IntVal,
	) -> Result<(IntVal, IntVal), Conflict> {
		// Start at the last possible occurrence of k, then iterate backwards.
		let mut i = actions.get_trailed_int(self.last[k as usize]);
		// If k == 0, no more lower bounds can be propagated.
		while k > 0 {
			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _ = actions.set_trailed_int(self.last[k as usize], i);
				// Enforce lower bound if lower and upper bound coincide.
				if actions.get_trailed_int(self.first[k as usize]) == i {
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| {
						self.explain_lower(a, i as usize, k)
					})?;
				}
				k -= 1;
				// Abort early if the previous state is rejoined.
				if actions.get_trailed_int(self.last[k as usize]) < i {
					return Ok((i, k + 1));
				}
			}

			i -= 1;
			// Hit boundary case, this will cause a conflict.
			if i < 0 {
				actions.set_int_lower_bound(self.vars[0], k, |a: &mut P| {
					self.explain_lower(a, 0, k)
				})?;
			}
		}

		Ok((i, 0))
	}

	/// Iteratively repair the upper bounds starting with k, only iterates as far
	/// as necessary.
	fn repair_upper<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: IntVal,
	) -> Result<(), Conflict> {
		let mut i = actions.get_trailed_int(self.first[k as usize]);
		let mut lim = self.get_upper_limit(actions, k as usize);

		while i <= lim {
			// Set new upper bound if necessary.
			if actions.get_int_upper_bound(self.vars[i as usize]) > k {
				actions.set_int_upper_bound(self.vars[i as usize], k, |a: &mut P| {
					self.explain_upper(a, i as usize, k)
				})?;
			}
			// If var i is the first possibility to reach value k
			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _ = actions.set_trailed_int(self.first[k as usize], i);
				let _ = actions.set_trailed_int(self.first_val[i as usize], k);
				// Enforce lower bound if lower and upper bound coincide.
				if actions.get_trailed_int(self.last[k as usize]) == i {
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| {
						self.explain_lower(a, i as usize, k)
					})?;
				}
				k += 1;
				// Abort early if the previous state is rejoined.
				if (k as usize) == self.first.len()
					|| i < actions.get_trailed_int(self.first[k as usize])
				{
					return Ok(());
				}
				lim = self.get_upper_limit(actions, k as usize);
			}
			i += 1;
		}

		// Hit boundary case, this will cause a conflict.
		if (i as usize) < self.vars.len() {
			actions.set_int_lower_bound(self.vars[i as usize - 1], k, |a: &mut P| {
				self.explain_lower(a, i as usize - 1, k)
			})?;
		}

		let _ = actions.set_trailed_int(self.first[k as usize], 0);
		Ok(())
	}
}

impl<P, E> Propagator<P, E> for IntSeqPrecedeChainBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "seq_precede_chain", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		if !self.initialized {
			return self.initial_propagation(actions);
		}

		// Check upper bound updates, only necessary for all elements in first,
		// not all variables.
		for (k, &t) in self.first.iter().enumerate() {
			let i = actions.get_trailed_int(t);
			if actions.get_trailed_int(self.first_val[i as usize]) == k as IntVal
				&& actions.get_int_upper_bound(self.vars[i as usize]) < k as IntVal
			{
				self.repair_upper(actions, k as IntVal)?;
			}
		}
		// Lower bound requires full pass to catch all potential propagations.
		let mut i = self.vars.len() as IntVal;
		let mut k = actions.get_trailed_int(self.max_last);
		while i > 0 {
			i -= 1;
			if k > 0 && actions.get_trailed_int(self.last[k as usize - 1]) == i {
				k -= 1;
			}
			let lb = actions.get_int_lower_bound(self.vars[i as usize]);
			// Deal with increase of lower bound.
			if lb > k {
				let _ = actions.set_trailed_int(self.last[lb as usize], i);
				// Update highest lower bound if necessary.
				if lb > actions.get_trailed_int(self.max_last) {
					let _ = actions.set_trailed_int(self.max_last, lb);
				}
				// If a repair is necessary, continue check where the repair ended.
				(i, k) = self.repair_lower(actions, lb)?;
				continue;
			}
			// Deal with moving the last possibility to have value k for the first.
			if actions.get_trailed_int(self.last[k as usize]) == i
				&& !actions.check_int_in_domain(self.vars[i as usize], k)
			{
				(i, k) = self.repair_lower(actions, k)?;
			}
		}
		Ok(())
	}
}

impl<S: SimplificationActions> Constraint<S> for IntValuePrecedeChain {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		if self.values.len() <= 1 {
			return Ok(SimplificationStatus::Subsumed);
		}
		let mut ub = 0;
		for &var in self.vars.iter() {
			// Index can increase if the value corresponding to the upper bound is present.
			if ub < self.values.len() && actions.check_int_in_domain(var, self.values[ub]) {
				ub += 1;
			}
			// Remove all values with too high indices.
			for j in ub..self.values.len() {
				actions.set_int_not_eq(var, self.values[j])?;
			}
		}
		// Variables that do not any tracked values are irrelevant.
		self.vars.retain(|&var| {
			self.values
				.iter()
				.any(|&val| actions.check_int_in_domain(var, val))
		});
		if self.vars.is_empty() {
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		IntValuePrecedeChainValue::new_in(slv, self.values.clone(), vars);
		Ok(())
	}
}

impl IntValuePrecedeChainValue {
	/// Lower bound explanation: Could not have this index earlier (=upper bound
	/// explanation) and some later index requires the lower bound (recursive lower bound).
	fn explain_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Vec<BoolView> {
		let mut v = self.explain_lower_recursive(actions, i + 1, j);
		if j > 0 {
			v.append(&mut self.explain_upper(actions, i, j));
		}
		v
	}

	/// Recursively explain a lower bound via 3 cases:
	/// - Current lower bound index is above k - This is the value that required
	///   the earlier lower bound that is currently explained (end of recursion).
	/// - Index k is in the domain of var i - Go one step up and to the next
	///   variable.
	/// - Index k is not in the domain of var i - i can be anything else, go to
	///   next variable.
	fn explain_lower_recursive<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Vec<BoolView> {
		// A lower bound is explained by stating that all untracked values are excluded
		// (< min value, > max value, all holes), as well as all values with smaller indices.
		if let Some(lb) = self.get_lowest_index(actions, i) {
			if lb > j {
				let mut v = vec![
					actions.get_int_lit(self.vars[i], IntLitMeaning::GreaterEq(self.min_val)),
					actions.get_int_lit(self.vars[i], IntLitMeaning::Less(self.max_val + 1)),
				];
				v.append(
					&mut self
						.holes
						.iter()
						.map(|&h| actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(h)))
						.collect(),
				);
				v.append(
					&mut (0..j)
						.map(|k| {
							actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(self.values[k]))
						})
						.collect(),
				);
				return v;
			}
		}
		if actions.check_int_in_domain(self.vars[i], self.values[j - 1]) {
			return self.explain_lower_recursive(actions, i + 1, j + 1);
		}
		let mut v = self.explain_lower_recursive(actions, i + 1, j);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(self.values[j - 1])));
		v
	}

	/// Upper bound explanation: All previous indices are smaller (exclude values
	/// with larger index).
	fn explain_upper<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Vec<BoolView> {
		self.vars
			.iter()
			.take(i)
			.map(|&v| actions.get_int_lit(v, IntLitMeaning::NotEq(self.values[j - 1])))
			.collect()
	}

	/// Get the lower bound for the index in values, None if any options outside
	/// values are still in the domain. Has to exclude values below and above the
	/// range of values, then all holes, finally values with lower index.
	fn get_lowest_index<I: InspectionActions>(&self, actions: &mut I, i: usize) -> Option<usize> {
		let lb = actions.get_int_lower_bound(self.vars[i]);
		let ub = actions.get_int_upper_bound(self.vars[i]);
		// Easy case with no lower index bound.
		if lb < self.min_val || ub > self.max_val {
			return None;
		}
		// Shortcut for fixed variables.
		if lb == ub {
			return self.mapping[(lb - self.min_val) as usize];
		}
		// Iteration over holes (via nex_hole for efficiency).
		let mut h = max(lb, self.min_hole);
		while ((h - self.min_hole) as usize) < self.next_hole.len() {
			h = self.next_hole[(h - self.min_hole) as usize];
			if h > ub {
				break;
			}
			if actions.check_int_in_domain(self.vars[i], h) {
				return None;
			}
			h += 1;
		}
		// Find the first possible index in values.
		for (j, &val) in self.values.iter().enumerate() {
			if actions.check_int_in_domain(self.vars[i], val) {
				return Some(j + 1);
			}
		}
		Some(self.values.len() + 1)
	}

	/// Get the latest occurrence of value index k, or the maximum variable index
	/// if there is no latest.
	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(
			actions.get_trailed_int(self.last[k]),
			self.vars.len() as IntVal - 1,
		)
	}

	/// Do a full propagation run, requires checking all variables in both
	/// directions.
	fn initial_propagation<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
		// Current upper bound
		let mut up = 0;
		// Current lower bound
		let mut low = 0;

		// Forward pass to set upper bounds and capture the highest lower bound.
		for (i, &v) in self.vars.iter().enumerate() {
			// Upper bound can only increase by 1, set new bound if larger values are in the domain.
			self.propagate_upper_bound(actions, i, up + 1)?;
			// The current var is the first possibility to reach index up + 1.
			if up < self.values.len() && actions.check_int_in_domain(v, self.values[up]) {
				up += 1;
				let _ = actions.set_trailed_int(self.first[up], i as IntVal);
				let _ = actions.set_trailed_int(self.first_val[i], up as IntVal);
			}
			// The lower bound will be needed for the backward pass.
			if let Some(lb) = self.get_lowest_index(actions, i) {
				if low < lb {
					let _ = actions.set_trailed_int(self.last[lb], i as IntVal);
					low = lb;
				}
			}
		}

		// Backward pass to set lower bounds.
		for (i, &v) in self.vars.iter().enumerate().rev() {
			// Lower bound is enforced if upper and lower bound coincide.
			if actions.get_trailed_int(self.first[low]) == i as IntVal {
				self.propagate_lower_bound(actions, i, low)?;
			}
			// Found possibility to use a lower value - reduce lower bound.
			if i as IntVal <= actions.get_trailed_int(self.last[low])
				&& actions.check_int_in_domain(v, self.values[low - 1])
			{
				let _ = actions.set_trailed_int(self.last[low], i as IntVal);
				low -= 1;
			}
			// Stop early if no more lower bounds can be propagated.
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Create a new [`ValuePrecedeChainValue`] propagator and post it in the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
		solver: &mut P,
		values: Vec<IntVal>,
		vars: Vec<IntView>,
	) {
		let n = vars.len();

		let first = (0..=values.len())
			.map(|i| {
				if i == 0 {
					solver.new_trailed_int(0)
				} else {
					solver.new_trailed_int(vars.len() as IntVal - 1)
				}
			})
			.collect();
		let last = (0..=values.len())
			.map(|i| {
				if i == 0 {
					solver.new_trailed_int(IntVal::MIN)
				} else {
					solver.new_trailed_int(IntVal::MAX)
				}
			})
			.collect();
		let first_val = (0..n).map(|_| solver.new_trailed_int(0)).collect();
		let max_last = solver.new_trailed_int(0);
		// Set up some data structures to deal with holes in values more efficiently.
		let min_val = *values.iter().min().unwrap_or(&IntVal::MAX);
		let max_val = *values.iter().max().unwrap_or(&IntVal::MIN);
		let holes = (min_val..=max_val)
			.filter(|&i| values.iter().all(|&v| v != i))
			.collect::<Vec<_>>();
		let min_hole = *holes.iter().min().unwrap_or(&0);
		let mut next_hole = vec![0; (*holes.iter().max().unwrap_or(&-1) - min_hole + 1) as usize];
		let mut cur_hole = 0;
		for (i, h) in next_hole.iter_mut().enumerate() {
			if i as IntVal + min_hole > holes[cur_hole] {
				cur_hole += 1;
			}
			*h = holes[cur_hole];
		}
		let mut mapping = vec![None; (max_val - min_val + 1) as usize];
		for (i, &val) in values.iter().enumerate() {
			mapping[(val - min_val) as usize] = Some(i + 1);
		}

		let prop = solver.add_propagator(
			Box::new(Self {
				values,
				vars: vars.clone(),
				initialized: false,
				first,
				last,
				first_val,
				max_last,
				min_val,
				max_val,
				holes,
				min_hole,
				next_hole,
				mapping,
			}),
			PriorityLevel::Low,
		);

		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Domain);
		}
		solver.enqueue_now(prop);
	}

	/// Propagate a lower bound by excluding all elements outside values, and
	/// values with lower index.
	fn propagate_lower_bound<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Result<(), Conflict> {
		let lb = actions.get_int_lower_bound(self.vars[i]);
		let ub = actions.get_int_upper_bound(self.vars[i]);
		// Exclude values below the minimum tracked value.
		if lb < self.min_val {
			actions.set_int_lower_bound(self.vars[i], self.min_val, |a: &mut P| {
				self.explain_lower(a, i, j)
			})?;
		}
		// Exclude values above the maximum tracked value.
		if ub > self.max_val {
			actions.set_int_upper_bound(self.vars[i], self.max_val, |a: &mut P| {
				self.explain_lower(a, i, j)
			})?;
		}
		// Exclude holes in the tracked values.
		let mut h = max(lb, self.min_hole);
		while ((h - self.min_hole) as usize) < self.next_hole.len() {
			h = self.next_hole[(h - self.min_hole) as usize];
			if h > ub {
				break;
			}
			if actions.check_int_in_domain(self.vars[i], h) {
				actions.set_int_not_eq(self.vars[i], h, |a: &mut P| self.explain_lower(a, i, j))?;
			}
			h += 1;
		}
		// Exclude values with lower index.
		for k in 0..j - 1 {
			if actions.check_int_in_domain(self.vars[i], self.values[k]) {
				actions.set_int_not_eq(self.vars[i], self.values[k], |a: &mut P| {
					self.explain_lower(a, i, j)
				})?;
			}
		}
		Ok(())
	}

	/// Propagate an upper bound by removing all values with higher index.
	fn propagate_upper_bound<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Result<(), Conflict> {
		for k in j..self.values.len() {
			if actions.check_int_in_domain(self.vars[i], self.values[k]) {
				actions.set_int_not_eq(self.vars[i], self.values[k], |a: &mut P| {
					self.explain_upper(a, i, k)
				})?;
			}
		}
		Ok(())
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as far
	/// as necessary.
	fn repair_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: usize,
	) -> Result<(usize, usize), Conflict> {
		// Start at the last possible occurrence of k, then iterate backwards.
		let mut i = actions.get_trailed_int(self.last[k]);
		// If k == 0, no more lower bounds can be propagated.
		while k > 0 {
			if actions.check_int_in_domain(self.vars[i as usize], self.values[k - 1]) {
				let _ = actions.set_trailed_int(self.last[k], i);
				// Enforce lower bound if lower and upper bound coincide.
				if actions.get_trailed_int(self.first[k]) == i {
					self.propagate_lower_bound(actions, i as usize, k)?;
				}
				k -= 1;
				// Abort early if the previous state is rejoined.
				if actions.get_trailed_int(self.last[k]) < i {
					return Ok((i as usize, k + 1));
				}
			}

			i -= 1;
			// Hit boundary case, this will cause a conflict.
			if i < 0 {
				self.propagate_lower_bound(actions, 0, k)?;
				// Return Ok since the conflict is only detected during propagation
				// (several domain elements are removed separately).
				return Ok((0, k));
			}
		}

		if i < 0 {
			return Ok((0, 0));
		}
		Ok((i as usize, 0))
	}

	/// Iteratively repair the upper bounds starting with k, only iterates as far
	/// as necessary.
	fn repair_upper<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: usize,
	) -> Result<(), Conflict> {
		let mut i = actions.get_trailed_int(self.first[k]);
		let mut lim = self.get_upper_limit(actions, k);

		while i <= lim {
			// Set new upper bound if necessary.
			self.propagate_upper_bound(actions, i as usize, k)?;
			// If var i is the first possibility to reach value k
			if actions.check_int_in_domain(self.vars[i as usize], self.values[k - 1]) {
				let _ = actions.set_trailed_int(self.first[k], i);
				let _ = actions.set_trailed_int(self.first_val[i as usize], k as IntVal);
				// Enforce lower bound if lower and upper bound coincide.
				if actions.get_trailed_int(self.last[k]) == i {
					self.propagate_lower_bound(actions, i as usize, k)?;
				}
				k += 1;
				// Abort early if the previous state is rejoined.
				if k == self.first.len() || i < actions.get_trailed_int(self.first[k]) {
					return Ok(());
				}
				lim = self.get_upper_limit(actions, k);
			}
			i += 1;
		}

		// Hit boundary case, this will cause a conflict.
		if (i as usize) < self.vars.len() {
			self.propagate_lower_bound(actions, i as usize - 1, k)?;
			// Return Ok since the conflict is only detected during propagation
			// (several domain elements are removed separately).
			return Ok(());
		}

		let _ = actions.set_trailed_int(self.first[k], 0);
		Ok(())
	}
}

impl<P, E> Propagator<P, E> for IntValuePrecedeChainValue
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "value_precede_chain", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		if !self.initialized {
			return self.initial_propagation(actions);
		}

		// Check upper bound updates, only necessary for all elements in first,
		// not all variables.
		for (k, &t) in self.first.iter().enumerate().skip(1) {
			let i = actions.get_trailed_int(t);
			if actions.get_trailed_int(self.first_val[i as usize]) == k as IntVal
				&& !actions.check_int_in_domain(self.vars[i as usize], self.values[k - 1])
			{
				self.repair_upper(actions, k)?;
			}
		}
		// Lower bound requires full pass to catch all potential propagations.
		let mut i = self.vars.len();
		let mut k = actions.get_trailed_int(self.max_last) as usize;
		while i > 0 {
			i -= 1;
			if k > 0 && actions.get_trailed_int(self.last[k - 1]) == i as IntVal {
				k -= 1;
			}
			if let Some(lb) = self.get_lowest_index(actions, i) {
				// Deal with increase of lower bound.
				if lb > k {
					let _ = actions.set_trailed_int(self.last[lb], i as IntVal);
					// Update highest lower bound if necessary.
					if lb as IntVal > actions.get_trailed_int(self.max_last) {
						let _ = actions.set_trailed_int(self.max_last, lb as IntVal);
					}
					// If a repair is necessary, continue check where the repair ended.
					(i, k) = self.repair_lower(actions, lb)?;
					continue;
				}
			}
			// Deal with moving the last possibility to have value k for the first.
			if actions.get_trailed_int(self.last[k]) == i as IntVal
				&& !actions.check_int_in_domain(self.vars[i], self.values[k - 1])
			{
				(i, k) = self.repair_lower(actions, k)?;
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use std::cmp::max;

	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
			Value::{self, Int},
		},
		IntVal,
	};

	#[test]
	#[traced_test]
	fn test_seq_precede_chain_paper() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1, 5..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2, 4..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x5 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x6 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x7 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x8 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([4..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x9 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntSeqPrecedeChainBounds::new_in(&mut slv, vec![x1, x2, x3, x4, x5, x6, x7, x8, x9]);
		slv.assert_all_solutions(
			&[x1, x2, x3, x4, x5, x6, x7, x8, x9],
			valid_sequence_precede,
		);
	}

	#[test]
	#[traced_test]
	fn test_seq_precede_chain_unrestricted() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntSeqPrecedeChainBounds::new_in(&mut slv, vec![x1, x2, x3, x4]);
		slv.assert_all_solutions(&[x1, x2, x3, x4], valid_sequence_precede);
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_complex() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=-3, 1..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=0, 2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x5 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x6 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=-1, 1..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x7 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-1..=-1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x8 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::new_in(
			&mut slv,
			vec![2, -2, 1, -1],
			vec![x0, x1, x2, x3, x4, x5, x6, x7, x8],
		);
		slv.assert_all_solutions(
			&[x0, x1, x2, x3, x4, x5, x6, x7, x8],
			valid_value_precede(vec![2, -2, 1, -1]),
		);
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_out_of_bounds() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::new_in(&mut slv, vec![1, 3], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 3]));
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_simple() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::new_in(&mut slv, vec![1, 2], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 2]));
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_unrestricted() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::new_in(&mut slv, vec![2, -2, 1, -1], vec![x0, x1, x2, x3]);
		slv.assert_all_solutions(&[x0, x1, x2, x3], valid_value_precede(vec![2, -2, 1, -1]));
	}

	fn valid_sequence_precede(sol: &[Value]) -> bool {
		sol.iter()
			.map(|v| {
				let Int(val) = *v else { return None };
				Some(val)
			})
			.try_fold(0, |u, val| match (u, val) {
				(uv, Some(val)) => {
					if val <= uv + 1 {
						Some(max(uv, val))
					} else {
						None
					}
				}
				_ => None,
			})
			.is_some()
	}

	fn valid_value_precede(values: Vec<IntVal>) -> impl Fn(&[Value]) -> bool {
		move |sol| {
			let mut cur_index = 0;
			for v in sol.iter() {
				if let Int(val) = *v {
					for &forbidden in values.iter().skip(cur_index + 1) {
						if forbidden == val {
							return false;
						}
					}
					if cur_index < values.len() && val == values[cur_index] {
						cur_index += 1;
					}
				} else {
					return false;
				}
			}
			true
		}
	}
}
