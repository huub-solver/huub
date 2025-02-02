//! Structures and algorithms for the integer array element constraint, which
//! enforces that a resulting variable equals an element of an array of integer
//! values or decision variables, chosen by an index variable.

use std::iter::once;

use itertools::Itertools;
use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{
		ConstraintInitActions, ExplanationActions, PropagationActions, PropagatorInitActions,
		ReformulationActions, SimplificationActions,
	},
	constraints::{Conflict, Constraint, Propagator, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, IntLitMeaning,
		IntView,
	},
	IntDecision, IntVal,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_element` constraint with an array of integer
/// decision variables within a model.
///
/// This constraint enforces that a result integer decision variable takes the
/// value equal the element of the given array of integer decision variable at
/// the given index decision variable.
pub struct IntDecisionArrayElement {
	/// The array of integer values
	pub(crate) array: Vec<IntDecision>,
	/// The index variable
	pub(crate) index: IntDecision,
	/// The resulting variable
	pub(crate) result: IntDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `array_element` constraint with an
/// array of integer decision variables.
pub struct IntDecisionArrayElementBounds {
	/// Array of variables from which the element is selected
	vars: Vec<IntView>,
	/// Variable that represent the result of the selection
	result: IntView,
	/// Variable that represent the index of the selected variable
	index: IntView,
	/// The index of the variable that supports the lower bound of the result
	min_support: TrailedInt,
	/// The index of the variable that supports the upper bound of the result
	max_support: TrailedInt,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_element` constraint with an array of integer
/// values within a model.
///
/// This constraint enforces that a result integer decision variable takes the
/// value equal the element of the given array of integer values at the given
/// index decision variable.
pub struct IntValArrayElement {
	/// The array of integer values
	pub(crate) array: Vec<IntVal>,
	/// The index variable
	pub(crate) index: IntDecision,
	/// The resulting variable
	pub(crate) result: IntDecision,
}

impl<S: SimplificationActions> Constraint<S> for IntDecisionArrayElement {
	fn initialize(&self, actions: &mut dyn ConstraintInitActions) {
		for &a in &self.array {
			actions.simplify_on_change_int(a);
		}
		actions.simplify_on_change_int(self.result);
		actions.simplify_on_change_int(self.index);
	}

	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		// make sure idx is within the range of args
		actions.set_int_lower_bound(self.index, 0)?;
		actions.set_int_upper_bound(self.index, self.array.len() as IntVal - 1)?;
		let (min_lb, max_ub) =
			self.array
				.iter()
				.fold((IntVal::MAX, IntVal::MIN), |(min_lb, max_ub), &v| {
					(
						min_lb.min(actions.get_int_lower_bound(v)),
						max_ub.max(actions.get_int_upper_bound(v)),
					)
				});
		if min_lb > actions.get_int_lower_bound(self.result) {
			actions.set_int_lower_bound(self.result, min_lb)?;
		}
		if max_ub < actions.get_int_upper_bound(self.result) {
			actions.set_int_upper_bound(self.result, max_ub)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let array = self.array.iter().map(|&v| slv.get_solver_int(v)).collect();
		let result = slv.get_solver_int(self.result);
		let index = slv.get_solver_int(self.index);
		IntDecisionArrayElementBounds::new_in(slv, array, result, index)
	}
}

impl IntDecisionArrayElementBounds {
	/// Create a new [`ArrayVarIntElementBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<P>(
		solver: &mut P,
		collection: Vec<IntView>,
		result: IntView,
		index: IntView,
	) -> Result<(), ReformulationError>
	where
		P: PropagatorInitActions + ?Sized,
	{
		// Remove out-of-bound values from the index variables
		let index_ub = solver.get_int_lit(index, IntLitMeaning::Less(collection.len() as IntVal));
		let index_lb = solver.get_int_lit(index, IntLitMeaning::GreaterEq(0));
		solver.add_clause([index_ub])?;
		solver.add_clause([index_lb])?;

		// Initialize the min_support and max_support variables
		let mut min_support = -1;
		let mut max_support = -1;
		let mut min_lb = IntVal::MAX;
		let mut max_ub = IntVal::MIN;
		for (i, v) in collection.iter().enumerate() {
			if solver.check_int_in_domain(index, i as IntVal) {
				let (lb, ub) = solver.get_int_bounds(*v);
				if min_support == -1 || lb < min_lb {
					min_support = i as IntVal;
					min_lb = solver.get_int_lower_bound(*v);
				}
				if max_support == -1 || ub > max_ub {
					max_support = i as IntVal;
					max_ub = ub;
				}
			}
		}
		let min_support = solver.new_trailed_int(min_support);
		let max_support = solver.new_trailed_int(max_support);

		// Post the propagator
		let prop = solver.add_propagator(
			Box::new(Self {
				vars: collection.clone(),
				result,
				index,
				min_support,
				max_support,
			}),
			PriorityLevel::Low,
		);

		// Subscribe to changes of the involved variables
		solver.enqueue_on_int_change(prop, result, IntPropCond::Bounds);
		solver.enqueue_on_int_change(prop, index, IntPropCond::Domain);
		for (i, v) in collection.iter().enumerate() {
			if solver.check_int_in_domain(index, i as IntVal) {
				solver.enqueue_on_int_change(prop, *v, IntPropCond::Bounds);
			}
		}

		Ok(())
	}
}

impl<P, E> Propagator<P, E> for IntDecisionArrayElementBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "array_int_element", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// ensure bounds of result and self.vars[self.index] are consistent when self.index is fixed
		// only trigger when self.index is fixed and (1) y is updated or (2) self.vars[self.index] is updated
		if let Some(fixed_index) = actions.get_int_val(self.index) {
			let index_val_lit = actions.get_int_val_lit(self.index).unwrap();
			let fixed_var = self.vars[fixed_index as usize];
			actions.set_int_lower_bound(
				self.result,
				actions.get_int_lower_bound(fixed_var),
				|a: &mut P| [index_val_lit, a.get_int_lower_bound_lit(fixed_var)],
			)?;
			actions.set_int_lower_bound(
				fixed_var,
				actions.get_int_lower_bound(self.result),
				|a: &mut P| [index_val_lit, a.get_int_lower_bound_lit(self.result)],
			)?;
			actions.set_int_upper_bound(
				self.result,
				actions.get_int_upper_bound(fixed_var),
				|a: &mut P| [index_val_lit, a.get_int_upper_bound_lit(fixed_var)],
			)?;
			actions.set_int_upper_bound(
				fixed_var,
				actions.get_int_upper_bound(self.result),
				|a: &mut P| [index_val_lit, a.get_int_upper_bound_lit(self.result)],
			)?;
			return Ok(());
		}

		let result_lb = actions.get_int_lower_bound(self.result);
		let result_ub = actions.get_int_upper_bound(self.result);
		let min_support = actions.get_trailed_int(self.min_support);
		let max_support = actions.get_trailed_int(self.max_support);
		let old_min = actions.get_int_lower_bound(self.vars[min_support as usize]);
		let old_max = actions.get_int_upper_bound(self.vars[max_support as usize]);
		let mut need_min_support = old_min > result_lb;
		let mut need_max_support = old_max < result_ub;
		let mut new_min_support = min_support;
		let mut new_max_support = max_support;
		let mut new_min = if need_min_support {
			IntVal::MAX
		} else {
			old_min
		};
		let mut new_max = if need_max_support {
			IntVal::MIN
		} else {
			old_max
		};

		// Iterate through all variables:
		// 1. remove values from the index variable when:
		// 	(1) result.upper_bound < self.vars[i].lower_bound -> index != i
		//  (2) result.lower_bound > self.vars[i].upper_bound -> index != i
		// 2. update min_support and max_support if necessary
		// only trigger when result variable is updated or self.vars[i] is updated
		for (i, v) in self.vars.iter().enumerate() {
			let (v_lb, v_ub) = actions.get_int_bounds(*v);
			if !actions.check_int_in_domain(self.index, i as IntVal) {
				continue;
			}

			if result_ub < v_lb {
				actions.set_int_not_eq(self.index, i as IntVal, |a: &mut P| {
					[
						a.get_int_lit(self.result, IntLitMeaning::Less(v_lb)),
						a.get_int_lower_bound_lit(*v),
					]
				})?;
			}

			if v_ub < result_lb {
				actions.set_int_not_eq(self.index, i as IntVal, |a: &mut P| {
					[
						a.get_int_lit(self.result, IntLitMeaning::GreaterEq(v_ub + 1)),
						a.get_int_upper_bound_lit(*v),
					]
				})?;
			}

			// update min_support if i is in the domain of self.index and the lower bound of v is less than the current min
			if need_min_support && v_lb < new_min {
				new_min_support = i as IntVal;
				new_min = v_lb;
				need_min_support = new_min > result_lb; // stop finding min_support if new_min ≤ y_lb
			}

			// update max_support if i is in the domain of self.index and the upper bound of v is greater than the current max
			if need_max_support && v_ub > new_max {
				new_max_support = i as IntVal;
				new_max = v_ub;
				need_max_support = new_max < result_ub; // stop finding max_support if new_max ≥ y_ub
			}
		}

		let _ = actions.set_trailed_int(self.min_support, new_min_support);
		let _ = actions.set_trailed_int(self.max_support, new_max_support);

		// propagate the lower bound of the selected variable y if min_support is not valid anymore
		// result.lower_bound >= min(i in domain(x))(self.vars[i].lower_bound)
		// only trigger when self.vars[min_support] is changed or self.vars[min_support] is out of domain
		if new_min > result_lb {
			actions.set_int_lower_bound(self.result, new_min, |a: &mut P| {
				self.vars
					.iter()
					.enumerate()
					.map(|(i, &v)| {
						if a.check_int_in_domain(self.index, i as IntVal) {
							a.get_int_lit(v, IntLitMeaning::GreaterEq(new_min))
						} else {
							a.get_int_lit(self.index, IntLitMeaning::NotEq(i as IntVal))
						}
					})
					.collect_vec()
			})?;
		}

		// propagate the upper bound of the selected variable y if max_support is not valid anymore
		// result.upper_bound <= max(i in domain(x))(self.vars[i].upper_bound)
		// only trigger when self.vars[max_support] is changed or self.vars[max_support] is out of domain
		if new_max < result_ub {
			actions.set_int_upper_bound(self.result, new_max, |a: &mut P| {
				self.vars
					.iter()
					.enumerate()
					.map(|(i, &v)| {
						if a.check_int_in_domain(self.index, i as IntVal) {
							a.get_int_lit(v, IntLitMeaning::Less(new_max + 1))
						} else {
							a.get_int_lit(self.index, IntLitMeaning::NotEq(i as IntVal))
						}
					})
					.collect_vec()
			})?;
		}

		Ok(())
	}
}

impl<S: SimplificationActions> Constraint<S> for IntValArrayElement {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let index = slv.get_solver_int(self.index);
		let result = slv.get_solver_int(self.result);

		// Make a map from the values of the array to the indexes at which they
		// occur
		let idx_map = self
			.array
			.iter()
			.enumerate()
			.map(|(i, v)| (*v, i as IntVal))
			.into_group_map();
		// Sort keys to ensure deterministic order
		let keys = idx_map.keys().sorted();

		for &val in keys {
			let idxs = &idx_map[&val];
			let val_eq = slv.get_int_lit(result, IntLitMeaning::Eq(val));
			let idxs: Vec<_> = idxs
				.iter()
				.map(|&i| slv.get_int_lit(index, IntLitMeaning::Eq(i)))
				.collect();

			for &i in idxs.iter() {
				// (idx = i) -> (val = arr[i])
				slv.add_clause([!i, val_eq])?;
			}
			// (idx not in idxs) -> (val != arr[i])
			slv.add_clause(idxs.into_iter().chain(once(!val_eq)))?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		array_element,
		constraints::int_array_element::IntDecisionArrayElementBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		Model,
	};

	#[test]
	#[traced_test]
	fn test_element_bounds_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([4..=5]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let y = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let index = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntDecisionArrayElementBounds::new_in(&mut slv, vec![a, b, c], y, index).unwrap();

		slv.expect_solutions(
			&[index, y, a, b, c],
			expect![[r#"
		0, 3, 3, 2, 4
		0, 3, 3, 2, 5
		0, 3, 3, 3, 4
		0, 3, 3, 3, 5
		0, 4, 4, 2, 4
		0, 4, 4, 2, 5
		0, 4, 4, 3, 4
		0, 4, 4, 3, 5
		1, 3, 3, 3, 4
		1, 3, 3, 3, 5
		1, 3, 4, 3, 4
		1, 3, 4, 3, 5
		2, 4, 3, 2, 4
		2, 4, 3, 3, 4
		2, 4, 4, 2, 4
		2, 4, 4, 3, 4"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_element_holes() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let y = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let index = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 3..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntDecisionArrayElementBounds::new_in(&mut slv, vec![a, b], y, index).unwrap();

		slv.expect_solutions(
			&[index, y, a, b],
			expect![[r#"
    0, 3, 3, 1
    0, 3, 3, 2
    0, 3, 3, 3"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_element_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let result = prb.new_int_var((1..=2).into());
		let index = prb.new_int_var((0..=2).into());

		prb += array_element(vec![a, b, c], index, result);
		prb.assert_unsatisfiable();
	}
}
