//! Structure and algorithms for the value_precede_chain constraint, which
//! enforces that a fixed order of the first occurrences of a given list of integers in
//! a list of integer variables.

use std::cmp::{max, min};
use tracing::trace;
use crate::solver::trail::TrailedInt;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	activation_list::IntPropCond, queue::PriorityLevel, IntView,
}, IntDecision, IntVal};
use crate::actions::InspectionActions;

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
	initialized: bool,
	first: Vec<TrailedInt>,
	last: Vec<TrailedInt>,
	first_val: Vec<TrailedInt>,
	max_last: TrailedInt,
	min_val: IntVal,
	max_val: IntVal,
	min_hole: IntVal,
	next_hole: Vec<IntVal>,
	holes: Vec<IntVal>,
	mapping: Vec<Option<usize>>,
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
		self.vars.retain(|&var| self.values.iter().any(|&val| actions.check_int_in_domain(var, val)));
		if self.vars.len() <= 0 {
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

	fn propagate_upper_bound<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Result<(), Conflict> {
		for k in j..self.values.len() {
			if actions.check_int_in_domain(self.vars[i], self.values[k]) {
				trace!("Upper bound restriction on var {i} removing {}", self.values[k]);
				actions.set_int_not_eq(self.vars[i], self.values[k], |a: &mut P| self.explain_upper(a, i, k))?;
			}
		}
		Ok(())
	}

	fn explain_upper<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Vec<BoolView> {
		self.vars.iter()
			.take(i)
			.map(|&v| actions.get_int_lit(v, IntLitMeaning::NotEq(self.values[j-1])))
			.collect()
	}

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
				return Some(j+1);
			}
		}
		Some(self.values.len() + 1)
	}

	fn propagate_lower_bound<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Result<(), Conflict> {
		let lb = actions.get_int_lower_bound(self.vars[i]);
		let ub = actions.get_int_upper_bound(self.vars[i]);
		if lb < self.min_val {
			trace!("Lower bound restriction on var {i} removing values <{}", self.min_val);
			actions.set_int_lower_bound(self.vars[i], self.min_val, |a: &mut P| self.explain_lower(a, i, j))?;
		}
		if ub > self.max_val {
			trace!("Lower bound restriction on var {i} removing values >{}", self.max_val);
			actions.set_int_upper_bound(self.vars[i], self.max_val, |a: &mut P| self.explain_lower(a, i, j))?;
		}
		let mut h = max(lb, self.min_hole);
		while ((h - self.min_hole) as usize) < self.next_hole.len() {
			h = self.next_hole[(h - self.min_hole) as usize];
			if h > ub {
				break;
			}
			if actions.check_int_in_domain(self.vars[i], h) {
				trace!("Lower bound restriction on var {i} removing hole {h}");
				actions.set_int_not_eq(self.vars[i], h, |a: &mut P| self.explain_lower(a, i, j))?;
			}
			h += 1;
		}
		for k in 0..j-1 {
			if actions.check_int_in_domain(self.vars[i], self.values[k]) {
				trace!("Lower bound restriction on var {i} removing {}", self.values[k]);
				actions.set_int_not_eq(self.vars[i], self.values[k], |a: &mut P| self.explain_lower(a, i, j))?;
			}
		}
		Ok(())
	}

	fn explain_lower<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Vec<BoolView> {
		let mut v = self.ex_l(actions, i+1, j);
		if j > 0 {
			v.append(&mut self.explain_upper(actions, i, j));
		}
		v
	}

	fn ex_l<P: PropagationActions>(&self, actions: &mut P, i: usize, j: usize) -> Vec<BoolView> {
		if let Some(lb) = self.get_lower_bound(actions, i) {
			if lb > j {
				let mut v = vec![actions.get_int_lit(self.vars[i], IntLitMeaning::GreaterEq(self.min_val)),
								 actions.get_int_lit(self.vars[i], IntLitMeaning::Less(self.max_val+1))];
				v.append(&mut self.holes.iter().map(|&h| actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(h))).collect());
				v.append(&mut (0..j).into_iter().map(|k| actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(self.values[k]))).collect());
				return v;
			}
		}
		if actions.check_int_in_domain(self.vars[i], self.values[j-1]) {
			return self.ex_l(actions, i+1, j+1);
		}
		let mut v = self.ex_l(actions, i+1, j);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(self.values[j-1])));
		v
	}

	fn propagate_full<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {

		trace!("Initial pass");
		let mut up = 0;
		let mut low = 0;

		for (i, &v) in self.vars.iter().enumerate() {
			self.propagate_upper_bound(actions, i, up+1)?;
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
			if i as IntVal <= actions.get_trailed_int(self.last[low]) && actions.check_int_in_domain(v, self.values[low-1]) {
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

	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(actions.get_trailed_int(self.last[k]), self.vars.len() as IntVal - 1)
	}

	fn repair_upper<P: PropagationActions>(&self, actions: &mut P, mut k: usize) -> Result<(), Conflict> {

		trace!("Repairing upper for {k}");
		let mut i = actions.get_trailed_int(self.first[k]);
		let mut lim = self.get_upper_limit(actions, k);

		while i <= lim {
			self.propagate_upper_bound(actions, i as usize, k)?;
			if actions.check_int_in_domain(self.vars[i as usize], self.values[k-1]) {
				let _= actions.set_trailed_int(self.first[k], i);
				let _= actions.set_trailed_int(self.first_val[i as usize], k as IntVal);
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
			trace!("Hit right side border case with i={}, k={}", i-1, k);
			self.propagate_lower_bound(actions, i as usize - 1, k)?;
			return Ok(());  //todo There is a conflict now, but it might need propagation to trigger
		}

		let _ = actions.set_trailed_int(self.first[k], 0);
		Ok(())

	}

	fn repair_lower<P: PropagationActions>(&self, actions: &mut P, mut k: usize) -> Result<(usize, usize), Conflict> {

		trace!("Repairing lower for {k}");
		let mut i = actions.get_trailed_int(self.last[k]);
		while k > 0 {

			if actions.check_int_in_domain(self.vars[i as usize], self.values[k-1]) {
				let _= actions.set_trailed_int(self.last[k], i);
				if actions.get_trailed_int(self.first[k]) == i {
					self.propagate_lower_bound(actions, i as usize, k)?;
				}
				k -= 1;
				if actions.get_trailed_int(self.last[k]) < i {
					return Ok((i as usize, k+1));
				}
			}

			i -= 1;
			if i < 0 {
				trace!("Hit left side border case with i={}, k={}", i, k);
				self.propagate_lower_bound(actions, 0, k)?;
				return Ok((0, k));  //todo There is a conflict now, but it might need propagation to trigger
			}

		}

		if i < 0 {
			return Ok((0, 0));
		}
		Ok((i as usize, 0))

	}

	/// Create a new [`ValuePrecedeChainValue`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P, values: Vec<IntVal>, vars: Vec<IntView>) {

		let n = vars.len();

		let first = (0..=values.len())
			.map(|i| if i == 0 {
				solver.new_trailed_int(0)
			} else {
				solver.new_trailed_int(vars.len() as IntVal - 1)
			})
			.collect();
		let last = (0..=values.len())
			.map(|i| if i == 0 {
				solver.new_trailed_int(IntVal::MIN)
			} else {
				solver.new_trailed_int(IntVal::MAX)
			})
			.collect();
		let first_val = (0..n).map(|_| solver.new_trailed_int(0)).collect();
		let max_last = solver.new_trailed_int(0);
		let min_val = *values.iter().min().unwrap_or(&IntVal::MAX);
		let max_val = *values.iter().max().unwrap_or(&IntVal::MIN);
		let holes = (min_val..=max_val).into_iter()
			.filter(|&i| values.iter()
				.all(|&v| v != i)).collect::<Vec<_>>();
		let min_hole = *holes.iter().min().unwrap_or(&0);
		let mut next_hole = vec![0; (*holes.iter().max().unwrap_or(&-1) - min_hole + 1) as usize];
		let mut cur_hole = 0;
		for i in 0..next_hole.len() {
			if i as IntVal + min_hole > holes[cur_hole] {
				cur_hole += 1;
			}
			next_hole[i] = holes[cur_hole];
		}
		let mut mapping = vec![None; (max_val - min_val + 1) as usize];
		for (i, &val) in values.iter().enumerate() {
			mapping[(val - min_val) as usize] = Some(i+1);
		}
		trace!("Values has min {min_val}, max {max_val}, and holes {holes:?}, with min {min_hole} and next {next_hole:?}, and mapping {mapping:?}");

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
			PriorityLevel::Low);

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

		trace!("Fixed assignments: {:?}", self.vars.iter().enumerate()
			.map(|(i, &v)| if let Some(val) = actions.get_int_val(v) {Some((i, val))} else {None})
			.flatten()
			.collect::<Vec<_>>());
		/*for (i, &v) in self.vars.iter().enumerate() {
			trace!("Domain of variable {i}: {:?}", (actions.get_int_lower_bound(v)..=actions.get_int_upper_bound(v))
				.into_iter()
				.map(|val| if actions.check_int_in_domain(v, val) {Some(val)} else {None})
				.flatten()
				.collect::<Vec<_>>());
		}
		trace!("first: {:?}", self.first.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("last: {:?}", self.last.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("first_val: {:?}", self.first_val.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("max_last: {:?}", actions.get_trailed_int(self.max_last));*/

		if self.initialized {
			for (k, &t) in self.first.iter().enumerate().skip(1) {
				let i = actions.get_trailed_int(t);
				if actions.get_trailed_int(self.first_val[i as usize]) == k as IntVal && !actions.check_int_in_domain(self.vars[i as usize], self.values[k-1]) {
					self.repair_upper(actions, k)?;
				}
			}
			let mut i = self.vars.len();
			let mut k = actions.get_trailed_int(self.max_last) as usize;
			while i > 0 {
				i -= 1;
				if k > 0 && actions.get_trailed_int(self.last[k-1]) == i as IntVal {
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
				if actions.get_trailed_int(self.last[k]) == i as IntVal && !actions.check_int_in_domain(self.vars[i], self.values[k-1]) {
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
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::solver::{
		int_var::{EncodingType, IntVar},
		Solver,
	};
	use crate::constraints::value_precede_chain::ValuePrecedeChainValue;
	use crate::IntVal;
	use crate::solver::Value;
	use crate::solver::Value::Int;

	fn check_valid_solution(values: Vec<IntVal>) -> impl Fn(&[Value]) -> bool {
		move |sol| {
		let mut cur_index = 0;
			for v in sol.iter() {
				if let Int(val) = *v {
					for j in cur_index + 1..values.len() {
						if values[j] == val {
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

		ValuePrecedeChainValue::new_in(&mut slv, vec![2, -2, 1, -1], vec![x0, x1, x2, x3, x4, x5, x6, x7, x8]);
		slv.assert_all_solutions(&[x0, x1, x2, x3, x4, x5, x6, x7, x8], check_valid_solution(vec![2, -2, 1, -1]));

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
		slv.assert_all_solutions(&[x0, x1, x2, x3], check_valid_solution(vec![2, -2, 1, -1]));

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
		slv.assert_all_solutions(&[x0, x1, x2], check_valid_solution(vec![1, 2]));

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
		slv.assert_all_solutions(&[x0, x1, x2], check_valid_solution(vec![1, 3]));

	}

}
