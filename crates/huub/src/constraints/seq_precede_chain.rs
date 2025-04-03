//! Structure and algorithms for the seq_precede_chain constraint, which
//! enforces that i precedes i+1 for all i>0 in a list of integer variables.

use std::cmp::min;
use tracing::trace;
use crate::solver::trail::TrailedInt;
use crate::solver::{BoolView, IntLitMeaning};
use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	activation_list::IntPropCond, queue::PriorityLevel, IntView,
}, IntDecision, IntVal};

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
pub struct SeqPrecedeChainBounds {  //todo is the name based on what it propagates or what triggers propagation?
	/// List of integer variables where first occurrences of all i>0 must be ordered.
	vars: Vec<IntView>,
	initialized: bool,
	first: Vec<TrailedInt>,
	last: Vec<TrailedInt>,
	first_val: Vec<TrailedInt>,
	max_last: TrailedInt,
}

impl<S: SimplificationActions> Constraint<S> for SeqPrecedeChain {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		if self.vars.iter().all(|&v| actions.get_int_upper_bound(v) <= 0) {
			return Ok(SimplificationStatus::Subsumed);
		}
		for (i, &v) in self.vars.iter().enumerate() {
			actions.set_int_upper_bound(v, i as IntVal + 1)?;
		}
		//todo could do more sophisticated?
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self.vars.iter().map(|v| slv.get_solver_int(*v)).collect();
		SeqPrecedeChainBounds::new_in(slv, vars);
		Ok(())
	}
}

impl SeqPrecedeChainBounds {

	//todo method annotations like inline

	fn explain_upper<P: PropagationActions>(&self, actions: &mut P, i: usize, k: IntVal) -> Vec<BoolView> {
		self.vars.iter()
			.take(i)
			.map(|&v| actions.get_int_lit(v, IntLitMeaning::Less(k)))
			.collect()
	}

	fn explain_lower<P: PropagationActions>(&self, actions: &mut P, i: usize, k: IntVal) -> Vec<BoolView> {
		let mut v = self.ex_l(actions, i+1, k);
		v.append(&mut self.explain_upper(actions, i, k));
		v //todo other options to join?
	}

	fn ex_l<P: PropagationActions>(&self, actions: &mut P, i: usize, k: IntVal) -> Vec<BoolView> {
		if actions.get_int_lower_bound(self.vars[i]) > k {
			return vec![actions.get_int_lit(self.vars[i], IntLitMeaning::GreaterEq(k+1))];
		}
		if actions.check_int_in_domain(self.vars[i], k) {
			return self.ex_l(actions, i+1, k+1);
		}
		let mut v = self.ex_l(actions, i+1, k);
		v.push(actions.get_int_lit(self.vars[i], IntLitMeaning::NotEq(k)));
		v
	}

	fn propagate_full<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {

		trace!("Initial pass");
		let mut up = 0;
		let mut low = 0;

		for (i, &v) in self.vars.iter().enumerate() {
			let mut ub_v = actions.get_int_upper_bound(v); //todo if this upper bound is changed, it is not immediately reflected in further calls
			if ub_v > up + 1 {
				if actions.check_int_in_domain(v, up+1) {
					ub_v = up + 1;
				}
				trace!("Setting upper bound for var {i} to {}", up+1);
				actions.set_int_upper_bound(v, up+1, |a: &mut P| self.explain_upper(a, i, up+1))?;  //todo lazy?
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
				trace!("Setting lower bound for var {i} to {low}");
				actions.set_int_lower_bound(v, low, |a: &mut P| self.explain_lower(a, i, low))?; //todo lazy?
			}
			if i as IntVal <= actions.get_trailed_int(self.last[low as usize]) && actions.check_int_in_domain(v, low) {
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

	fn get_upper_limit<P: PropagationActions>(&self, actions: &mut P, k: usize) -> IntVal {
		min(actions.get_trailed_int(self.last[k]), self.vars.len() as IntVal - 1)
	}

	fn repair_upper<P: PropagationActions>(&self, actions: &mut P, mut k: IntVal) -> Result<(), Conflict> {

		trace!("Repairing upper for {k}");
		let mut i = actions.get_trailed_int(self.first[k as usize]);
		let mut lim = self.get_upper_limit(actions, k as usize);

		while i <= lim {
			if actions.get_int_upper_bound(self.vars[i as usize]) > k {
				trace!("Setting upper bound for var {i} to {k}");
				actions.set_int_upper_bound(self.vars[i as usize], k, |a: &mut P| self.explain_upper(a, i as usize, k))? //todo lazy?
			}
			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _= actions.set_trailed_int(self.first[k as usize], i);
				let _= actions.set_trailed_int(self.first_val[i as usize], k);
				if actions.get_trailed_int(self.last[k as usize]) == i {
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| self.explain_lower(a, i as usize, k))?;
				}
				k += 1;
				if (k as usize) == self.first.len() || i < actions.get_trailed_int(self.first[k as usize]) {
					return Ok(());
				}
				lim = self.get_upper_limit(actions, k as usize);
			}
			i += 1;
		}

		if (i as usize) < self.vars.len() {
			trace!("Hit right side border case with i={}, k={}", i-1, k);
			actions.set_int_lower_bound(self.vars[i as usize - 1], k, |a: &mut P| self.explain_lower(a, i as usize - 1, k))?;
		}

		let _ = actions.set_trailed_int(self.first[k as usize], 0);
		Ok(())

	}

	fn repair_lower<P: PropagationActions>(&self, actions: &mut P, mut k: IntVal) -> Result<(IntVal, IntVal), Conflict> {

		trace!("Repairing lower for {k}");
		let mut i = actions.get_trailed_int(self.last[k as usize]);
		while k > 0 {

			if actions.check_int_in_domain(self.vars[i as usize], k) {
				let _= actions.set_trailed_int(self.last[k as usize], i);
				if actions.get_trailed_int(self.first[k as usize]) == i {
					trace!("Setting lower bound for var {i} to {k}");
					actions.set_int_lower_bound(self.vars[i as usize], k, |a: &mut P| self.explain_lower(a, i as usize, k))? //todo lazy?
				}
				k -= 1;
				if actions.get_trailed_int(self.last[k as usize]) < i {
					return Ok((i, k+1));
				}
			}

			i -= 1;
			if i < 0 {
				trace!("Hit left side border case with i={}, k={}", i, k);
				actions.set_int_lower_bound(self.vars[0], k, |a: &mut P| self.explain_lower(a, 0, k))?;
			}

		}

		Ok((i, 0))

	}

	/// Create a new [`SeqPrecedeChainBounds`] propagator and post it in the solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(solver: &mut P, vars: Vec<IntView>) {

		let n = vars.len();
		let ub = vars.iter()
			.fold(0, |u, &item| if solver.get_int_upper_bound(item) > u { u + 1 } else { u });

		let first = (0..=ub).map(|_| solver.new_trailed_int(0)).collect();
		let last = (0..=ub)
			.map(|i| if i == 0 {
				solver.new_trailed_int(IntVal::MIN)
			} else {
				solver.new_trailed_int(IntVal::MAX)
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
			PriorityLevel::Low);  //todo priority?

		for v in vars {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Domain);  //todo domain or bounds?
		}
		solver.enqueue_now(prop); //todo is it good to enqueue now or init differently?

	}
}

impl<P, E> Propagator<P, E> for SeqPrecedeChainBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "seq_precede_chain", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {

		trace!("Fixed assignments: {:?}", self.vars.iter().enumerate()
			.map(|(i, &v)| if let Some(val) = actions.get_int_val(v) {Some((i, val))} else {None})
			.flatten()
			.collect::<Vec<_>>());
		/*trace!("first: {:?}", self.first.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("last: {:?}", self.last.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("first_val: {:?}", self.first_val.iter().map(|&t| actions.get_trailed_int(t)).collect::<Vec<_>>());
		trace!("max_last: {:?}", actions.get_trailed_int(self.max_last));*/

		if self.initialized {
			for (k, &t) in self.first.iter().enumerate() {
				let i = actions.get_trailed_int(t);
				if actions.get_trailed_int(self.first_val[i as usize]) == k as IntVal && actions.get_int_upper_bound(self.vars[i as usize]) < k as IntVal {
					self.repair_upper(actions, k as IntVal)?;
				}
			}
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
				if actions.get_trailed_int(self.last[k as usize]) == i && !actions.check_int_in_domain(self.vars[i as usize], k) {
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
		constraints::seq_precede_chain::SeqPrecedeChainBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
	};
	use crate::solver::Value;
	use crate::solver::Value::Int;

	fn check_valid_solution(sol: &[Value]) -> bool {
		sol.iter()
			.map(|v| {let Int(val) = *v else { return None }; Some(val)})
			.fold(Some(0), |u, val| {
				match (u, val) {
					(Some(uv), Some(val)) => if val <= uv + 1 {Some(max(uv, val))} else {None},
					_ => None,
				}
			}).is_some()
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
		slv.assert_all_solutions(&[x1, x2, x3, x4, x5, x6, x7, x8, x9], check_valid_solution);

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
		slv.assert_all_solutions(&[x1, x2, x3, x4], check_valid_solution);

	}

}
