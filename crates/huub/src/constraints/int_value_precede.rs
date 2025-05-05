//! Structure and algorithms for the value_precede_chain constraint, which
//! enforces that a fixed order of the first occurrences of a given list of integers in
//! a list of integer variables.

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
/// Representation of the `seq_precede_chain` constraint within a model.
///
/// This constraint enforces that the first occurrences of all i>0 are ordered in the given list.
pub struct SeqPrecedeChain {
	/// List of integer decision variables where first occurrences of all i>0 must be ordered.
	pub(crate) vars: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the `seq_precede_chain` constraint.
pub struct SeqPrecedeChainBounds {
	/// List of integer variables where first occurrences of all i>0 must be ordered.
	vars: Vec<IntView>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of i.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of i.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i that has to occur.
	max_last: TrailedInt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `value_precede_chain` constraint within a model.
///
/// This constraint enforces that the first occurrences of the elements of the given integer list
/// in the list of integer decision variables are ordered according to the given list.
pub struct ValuePrecedeChain {
	/// List of integers that need to occur in order
	pub(crate) values: Vec<IntVal>,
	/// List of integer decision variables where first occurrences of specified values must be ordered.
	pub(crate) vars: Vec<IntDecision>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `value_precede_chain` constraint.
pub struct ValuePrecedeChainValue {
	/// List of integers that need to occur in order
	values: Vec<IntVal>,
	/// List of integer variables where first occurrences of specified values must be ordered.
	vars: Vec<IntView>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of `values[i]`.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of `values[i]`.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i such that `values[i]` has to occur.
	max_last: TrailedInt,
	/// Minimum value in values.
	min_val: IntVal,
	/// Maximum value in values.
	max_val: IntVal,
	/// Minimum value with `min_val<min_hole<max_val` such that min_hole is not an element of values.
	min_hole: IntVal,
	/// Used to iterate through the holes in values.
	next_hole: Vec<IntVal>,
	/// List of holes in values.
	holes: Vec<IntVal>,
	/// Reverse mapping of actual values to their indices in the `values` array
	mapping: Vec<Option<usize>>,
}

impl<S: SimplificationActions> Constraint<S> for SeqPrecedeChain {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		let mut ub = 0;
		for &v in self.vars.iter() {
			if actions.check_int_in_domain(v, ub + 1) {
				ub += 1;
			}
			actions.set_int_upper_bound(v, ub)?;
		}
		//todo this can become more powerful if updated upper bound from previous loop is available
		self.vars.retain(|&v| actions.get_int_upper_bound(v) > 0);
		if self.vars.is_empty() {
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		SeqPrecedeChainBounds::new_in(slv, vars);
		Ok(())
	}
}

impl SeqPrecedeChainBounds {
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

	/// Lower bound explanation: Could not have this value earlier (=upper bound explanation)
	/// and some later value requires the lower bound.
	fn explain_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		k: IntVal,
	) -> Vec<BoolView> {
		let mut v = self.ex_l(actions, i + 1, k);
		v.extend(self.explain_upper(actions, i, k));
		v
	}

	/// 3 cases:
	/// - Current lower bound is above k - This is the value that required the earlier lower bound.
	/// - k is in the domain of var i - Go one step up and to the next variable.
	/// - k is not in the domain of var i - i can be anything else, go to next variable.
	fn ex_l<P: PropagationActions>(&self, actions: &mut P, i: usize, k: IntVal) -> Vec<BoolView> {
		if actions.get_int_lower_bound(self.vars[i]) > k {
			return vec![actions.get_int_lit(self.vars[i], IntLitMeaning::GreaterEq(k + 1))];
		}
		if actions.check_int_in_domain(self.vars[i], k) {
			return self.ex_l(actions, i + 1, k + 1);
		}
		let mut v = self.ex_l(actions, i + 1, k);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(k)));
		v
	}

	/// Do a full propagation run, requires checking all variables in both directions.
	fn propagate_full<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut up = 0;
		let mut low = 0;

		for (i, &v) in self.vars.iter().enumerate() {
			let mut ub_v = actions.get_int_upper_bound(v);
			if ub_v > up + 1 {
				if actions.check_int_in_domain(v, up + 1) {
					ub_v = up + 1;
				}
				actions.set_int_upper_bound(self.vars[i], up + 1, |a: &mut P| {
					self.explain_upper(a, i, up + 1)
				})?;
			}
			if ub_v == up + 1 {
				up += 1;
				let _ = actions.set_trailed_int(self.first[up as usize], i as IntVal);
				let _ = actions.set_trailed_int(self.first_val[i], up);
			}
			let lb_v = actions.get_int_lower_bound(v);
			if low < lb_v {
				let _ = actions.set_trailed_int(self.last[lb_v as usize], i as IntVal);
				low = lb_v;
			}
		}
		let _ = actions.set_trailed_int(self.max_last, low);

		for (i, &v) in self.vars.iter().enumerate().rev() {
			if actions.get_trailed_int(self.first[low as usize]) == i as IntVal {
				actions.set_int_lower_bound(self.vars[i], low, |a: &mut P| {
					self.explain_lower(a, i, low)
				})?;
			}
			if i as IntVal <= actions.get_trailed_int(self.last[low as usize])
				&& actions.check_int_in_domain(v, low)
			{
				let _ = actions.set_trailed_int(self.last[low as usize], i as IntVal);
				low -= 1;
			}
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Get the latest occurrence of k, or the maximum variable index if there is no latest.
	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(
			actions.get_trailed_int(self.last[k]),
			self.vars.len() as IntVal - 1,
		)
	}

	/// Iteratively repair the upper bounds starting with k, only iterates as far as necessary.
	fn repair_upper<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: IntVal,
	) -> Result<(), Conflict> {
		let mut i = actions.get_trailed_int(self.first[k as usize]);
		let mut lim = self.get_upper_limit(actions, k as usize);

		while i <= lim {
			if actions.get_int_upper_bound(self.vars[i as usize]) > k {
				actions.set_int_upper_bound(self.vars[i as usize], k, |a: &mut P| {
					self.explain_upper(a, i as usize, k)
				})?;
			}
			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _ = actions.set_trailed_int(self.first[k as usize], i);
				let _ = actions.set_trailed_int(self.first_val[i as usize], k);
				if actions.get_trailed_int(self.last[k as usize]) == i {
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| {
						self.explain_lower(a, i as usize, k)
					})?;
				}
				k += 1;
				if (k as usize) == self.first.len()
					|| i < actions.get_trailed_int(self.first[k as usize])
				{
					return Ok(());
				}
				lim = self.get_upper_limit(actions, k as usize);
			}
			i += 1;
		}

		if (i as usize) < self.vars.len() {
			actions.set_int_lower_bound(self.vars[i as usize - 1], k, |a: &mut P| {
				self.explain_lower(a, i as usize - 1, k)
			})?;
		}

		let _ = actions.set_trailed_int(self.first[k as usize], 0);
		Ok(())
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as far as necessary.
	fn repair_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: IntVal,
	) -> Result<(IntVal, IntVal), Conflict> {
		let mut i = actions.get_trailed_int(self.last[k as usize]);
		while k > 0 {
			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _ = actions.set_trailed_int(self.last[k as usize], i);
				if actions.get_trailed_int(self.first[k as usize]) == i {
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| {
						self.explain_lower(a, i as usize, k)
					})?;
				}
				k -= 1;
				if actions.get_trailed_int(self.last[k as usize]) < i {
					return Ok((i, k + 1));
				}
			}

			i -= 1;
			if i < 0 {
				actions.set_int_lower_bound(self.vars[0], k, |a: &mut P| {
					self.explain_lower(a, 0, k)
				})?;
			}
		}

		Ok((i, 0))
	}

	/// Create a new [`SeqPrecedeChainBounds`] propagator and post it in the solver.
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
}

impl<P, E> Propagator<P, E> for SeqPrecedeChainBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "seq_precede_chain", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		if self.initialized {
			// Check upper bound updates, only necessary for all elements in first, not all variables.
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
				if lb > k {
					let _ = actions.set_trailed_int(self.last[lb as usize], i);
					if lb > actions.get_trailed_int(self.max_last) {
						let _ = actions.set_trailed_int(self.max_last, lb);
					}
					(i, k) = self.repair_lower(actions, lb)?;
					continue;
				}
				if actions.get_trailed_int(self.last[k as usize]) == i
					&& !actions.check_int_in_domain(self.vars[i as usize], k)
				{
					(i, k) = self.repair_lower(actions, k)?;
				}
			}
			return Ok(());
		}

		self.propagate_full(actions)
	}
}

impl<S: SimplificationActions> Constraint<S> for ValuePrecedeChain {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		if self.values.len() <= 1 {
			return Ok(SimplificationStatus::Subsumed);
		}
		let mut ub = 0;
		for &var in self.vars.iter() {
			if ub < self.values.len() && actions.check_int_in_domain(var, self.values[ub]) {
				ub += 1;
			}
			for j in ub..self.values.len() {
				actions.set_int_not_eq(var, self.values[j])?;
			}
		}
		//todo this can become more powerful if updated upper bound from previous loop is available
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
		ValuePrecedeChainValue::new_in(slv, self.values.clone(), vars);
		Ok(())
	}
}

impl ValuePrecedeChainValue {
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

	/// Upper bound explanation: All previous indices are smaller.
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

	/// Get the lower bound for the index in values, None if any options outside values are still in the domain.
	/// Has to exclude values below and above the range of values, then all holes, finally values with lower index.
	fn get_lower_bound<I: InspectionActions>(&self, actions: &mut I, i: usize) -> Option<usize> {
		let lb = actions.get_int_lower_bound(self.vars[i]);
		let ub = actions.get_int_upper_bound(self.vars[i]);
		if lb < self.min_val || ub > self.max_val {
			return None;
		}
		if lb == ub {
			return self.mapping[(lb - self.min_val) as usize];
		}
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
		for (j, &val) in self.values.iter().enumerate() {
			if actions.check_int_in_domain(self.vars[i], val) {
				return Some(j + 1);
			}
		}
		Some(self.values.len() + 1)
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
		if lb < self.min_val {
			actions.set_int_lower_bound(self.vars[i], self.min_val, |a: &mut P| {
				self.explain_lower(a, i, j)
			})?;
		}
		if ub > self.max_val {
			actions.set_int_upper_bound(self.vars[i], self.max_val, |a: &mut P| {
				self.explain_lower(a, i, j)
			})?;
		}
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
		for k in 0..j - 1 {
			if actions.check_int_in_domain(self.vars[i], self.values[k]) {
				actions.set_int_not_eq(self.vars[i], self.values[k], |a: &mut P| {
					self.explain_lower(a, i, j)
				})?;
			}
		}
		Ok(())
	}

	/// Lower bound explanation: Could not have this index earlier (=upper bound
	/// explanation) and some later index requires the lower bound.
	fn explain_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		i: usize,
		j: usize,
	) -> Vec<BoolView> {
		let mut v = self.ex_l(actions, i + 1, j);
		if j > 0 {
			v.append(&mut self.explain_upper(actions, i, j));
		}
		v
	}

	/// 3 cases:
	/// - Current lower bound index is above k - This is the value that required
	/// the earlier lower bound.
	/// - Index k is in the domain of var i - Go one step
	/// up and to the next variable.
	/// - Index k is not in the domain of var i - i
	/// can be anything else, go to next variable.
	fn ex_l<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Vec<BoolView> {
		if let Some(lb) = self.get_lower_bound(actions, i) {
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
			return self.ex_l(actions, i + 1, j + 1);
		}
		let mut v = self.ex_l(actions, i + 1, j);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(self.values[j - 1])));
		v
	}

	/// Do a full propagation run, requires checking all variables in both
	/// directions.
	fn propagate_full<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let mut up = 0;
		let mut low = 0;

		for (i, &v) in self.vars.iter().enumerate() {
			self.propagate_upper_bound(actions, i, up + 1)?;
			if up < self.values.len() && actions.check_int_in_domain(v, self.values[up]) {
				up += 1;
				let _ = actions.set_trailed_int(self.first[up], i as IntVal);
				let _ = actions.set_trailed_int(self.first_val[i], up as IntVal);
			}
			if let Some(lb) = self.get_lower_bound(actions, i) {
				if low < lb {
					let _ = actions.set_trailed_int(self.last[lb], i as IntVal);
					low = lb;
				}
			}
		}

		for (i, &v) in self.vars.iter().enumerate().rev() {
			if actions.get_trailed_int(self.first[low]) == i as IntVal {
				self.propagate_lower_bound(actions, i, low)?;
			}
			if i as IntVal <= actions.get_trailed_int(self.last[low])
				&& actions.check_int_in_domain(v, self.values[low - 1])
			{
				let _ = actions.set_trailed_int(self.last[low], i as IntVal);
				low -= 1;
			}
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Get the latest occurrence of value index k, or the maximum variable index
	/// if there is no latest.
	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(
			actions.get_trailed_int(self.last[k]),
			self.vars.len() as IntVal - 1,
		)
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
			self.propagate_upper_bound(actions, i as usize, k)?;
			if actions.check_int_in_domain(self.vars[i as usize], self.values[k - 1]) {
				let _ = actions.set_trailed_int(self.first[k], i);
				let _ = actions.set_trailed_int(self.first_val[i as usize], k as IntVal);
				if actions.get_trailed_int(self.last[k]) == i {
					self.propagate_lower_bound(actions, i as usize, k)?;
				}
				k += 1;
				if k == self.first.len() || i < actions.get_trailed_int(self.first[k]) {
					return Ok(());
				}
				lim = self.get_upper_limit(actions, k);
			}
			i += 1;
		}

		if (i as usize) < self.vars.len() {
			self.propagate_lower_bound(actions, i as usize - 1, k)?;
			return Ok(()); //todo There is a conflict now, but it might need propagation to trigger
		}

		let _ = actions.set_trailed_int(self.first[k], 0);
		Ok(())
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as far as necessary.
	fn repair_lower<P: PropagationActions>(
		&self,
		actions: &mut P,
		mut k: usize,
	) -> Result<(usize, usize), Conflict> {
		let mut i = actions.get_trailed_int(self.last[k]);
		while k > 0 {
			if actions.check_int_in_domain(self.vars[i as usize], self.values[k - 1]) {
				let _ = actions.set_trailed_int(self.last[k], i);
				if actions.get_trailed_int(self.first[k]) == i {
					self.propagate_lower_bound(actions, i as usize, k)?;
				}
				k -= 1;
				if actions.get_trailed_int(self.last[k]) < i {
					return Ok((i as usize, k + 1));
				}
			}

			i -= 1;
			if i < 0 {
				self.propagate_lower_bound(actions, 0, k)?;
				return Ok((0, k)); //todo There is a conflict now, but it might need propagation to trigger
			}
		}

		if i < 0 {
			return Ok((0, 0));
		}
		Ok((i as usize, 0))
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
}

impl<P, E> Propagator<P, E> for ValuePrecedeChainValue
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "value_precede_chain", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		if self.initialized {
			// Check upper bound updates, only necessary for all elements in first, not all variables.
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
				if let Some(lb) = self.get_lower_bound(actions, i) {
					if lb > k {
						let _ = actions.set_trailed_int(self.last[lb], i as IntVal);
						if lb as IntVal > actions.get_trailed_int(self.max_last) {
							let _ = actions.set_trailed_int(self.max_last, lb as IntVal);
						}
						(i, k) = self.repair_lower(actions, lb)?;
						continue;
					}
				}
				if actions.get_trailed_int(self.last[k]) == i as IntVal
					&& !actions.check_int_in_domain(self.vars[i], self.values[k - 1])
				{
					(i, k) = self.repair_lower(actions, k)?;
				}
			}
			return Ok(());
		}

		self.propagate_full(actions)
	}
}

#[cfg(test)]
mod tests {
	use std::cmp::max;

	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_value_precede::{SeqPrecedeChainBounds, ValuePrecedeChainValue},
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
			Value::{self, Int},
		},
		IntVal,
	};

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

		SeqPrecedeChainBounds::new_in(&mut slv, vec![x1, x2, x3, x4, x5, x6, x7, x8, x9]);
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

		SeqPrecedeChainBounds::new_in(&mut slv, vec![x1, x2, x3, x4]);
		slv.assert_all_solutions(&[x1, x2, x3, x4], valid_sequence_precede);
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

		ValuePrecedeChainValue::new_in(
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

		ValuePrecedeChainValue::new_in(&mut slv, vec![2, -2, 1, -1], vec![x0, x1, x2, x3]);
		slv.assert_all_solutions(&[x0, x1, x2, x3], valid_value_precede(vec![2, -2, 1, -1]));
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

		ValuePrecedeChainValue::new_in(&mut slv, vec![1, 2], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 2]));
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

		ValuePrecedeChainValue::new_in(&mut slv, vec![1, 3], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 3]));
	}
}
