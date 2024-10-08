use itertools::Itertools;

use crate::{
	actions::{explanation::ExplanationActions, initialization::InitializationActions},
	propagator::{conflict::Conflict, PropagationActions, Propagator},
	solver::{
		engine::{activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt},
		poster::{BoxedPropagator, Poster, QueuePreferences},
		value::IntVal,
		view::IntView,
	},
	LitMeaning, ReformulationError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArrayVarIntElementBounds {
	vars: Vec<IntView>,      // Variables to be selected
	result: IntView,         // The selected variable
	index: IntView,          // Variable that stores the index of the selected variable
	min_support: TrailedInt, // The minimum support of the selected variable
	max_support: TrailedInt, // The maximum support of the selected variable
}

impl ArrayVarIntElementBounds {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		result: IntView,
		index: IntView,
	) -> impl Poster {
		ArrayVarIntElementBoundsPoster {
			vars: vars.into_iter().map(Into::into).collect(),
			result,
			index,
		}
	}
}

impl<P, E> Propagator<P, E> for ArrayVarIntElementBounds
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
						a.get_int_lit(self.result, LitMeaning::Less(v_lb)),
						a.get_int_lower_bound_lit(*v),
					]
				})?;
			}

			if v_ub < result_lb {
				actions.set_int_not_eq(self.index, i as IntVal, |a: &mut P| {
					[
						a.get_int_lit(self.result, LitMeaning::GreaterEq(v_ub + 1)),
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
							a.get_int_lit(v, LitMeaning::GreaterEq(new_min))
						} else {
							a.get_int_lit(self.index, LitMeaning::NotEq(i as IntVal))
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
							a.get_int_lit(v, LitMeaning::Less(new_max + 1))
						} else {
							a.get_int_lit(self.index, LitMeaning::NotEq(i as IntVal))
						}
					})
					.collect_vec()
			})?;
		}

		Ok(())
	}
}

struct ArrayVarIntElementBoundsPoster {
	index: IntView,
	result: IntView,
	vars: Vec<IntView>,
}
impl Poster for ArrayVarIntElementBoundsPoster {
	fn post<I: InitializationActions>(
		self,
		actions: &mut I,
	) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
		// remove out-of-bound values from the index variables
		let index_ub = actions.get_int_lit(self.index, LitMeaning::Less(self.vars.len() as IntVal));
		let index_lb = actions.get_int_lit(self.index, LitMeaning::GreaterEq(0));
		actions.add_clause(vec![index_ub])?;
		actions.add_clause(vec![index_lb])?;

		// initialize the min_support and max_support variables
		let mut min_support = -1;
		let mut max_support = -1;
		let mut min_lb = IntVal::MAX;
		let mut max_ub = IntVal::MIN;
		for (i, v) in self.vars.iter().enumerate() {
			if actions.check_int_in_domain(self.index, i as IntVal) {
				actions.enqueue_on_int_change(*v, IntPropCond::Bounds);
				let (lb, ub) = actions.get_int_bounds(*v);
				if min_support == -1 || lb < min_lb {
					min_support = i as IntVal;
					min_lb = actions.get_int_lower_bound(*v);
				}
				if max_support == -1 || ub > max_ub {
					max_support = i as IntVal;
					max_ub = ub;
				}
			}
		}

		let prop = ArrayVarIntElementBounds {
			vars: self.vars.into_iter().map(Into::into).collect(),
			result: self.result,
			index: self.index,
			min_support: actions.new_trailed_int(min_support),
			max_support: actions.new_trailed_int(max_support),
		};
		actions.enqueue_on_int_change(prop.result, IntPropCond::Bounds);
		actions.enqueue_on_int_change(prop.index, IntPropCond::Domain);
		Ok((
			Box::new(prop),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Low,
			},
		))
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		propagator::array_var_int_element::ArrayVarIntElementBounds,
		solver::engine::int_var::{EncodingType, IntVar},
		Constraint, Model, Solver,
	};

	#[test]
	#[traced_test]
	fn test_element_bounds_sat() {
		let mut slv = Solver::<Cadical>::from(&Cnf::default());
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

		slv.add_propagator(ArrayVarIntElementBounds::prepare(vec![a, b, c], y, index))
			.unwrap();
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
	fn test_element_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((1..=2).into());
		let index = prb.new_int_var((0..=2).into());

		prb += Constraint::ArrayVarIntElement(vec![a, b, c], index, y);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_element_holes() {
		let mut slv = Solver::<Cadical>::from(&Cnf::default());
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

		slv.add_propagator(ArrayVarIntElementBounds::prepare(vec![a, b], y, index))
			.unwrap();
		slv.expect_solutions(
			&[index, y, a, b],
			expect![[r#"
    0, 3, 3, 1
    0, 3, 3, 2
    0, 3, 3, 3"#]],
		);
	}
}
