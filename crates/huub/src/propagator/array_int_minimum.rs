use itertools::Itertools;

use crate::{
	actions::{explanation::ExplanationActions, initialization::InitializationActions},
	propagator::{conflict::Conflict, PropagationActions, Propagator},
	solver::{
		engine::{activation_list::IntPropCond, queue::PriorityLevel},
		poster::{BoxedPropagator, Poster, QueuePreferences},
		value::IntVal,
		view::IntView,
	},
	LitMeaning, ReformulationError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArrayIntMinimumBounds {
	vars: Vec<IntView>, // Variables in the minimum constraints
	min: IntView,       // Variable that stores the minimum value
}

impl ArrayIntMinimumBounds {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		min: IntView,
	) -> impl Poster {
		ArrayIntMinimumBoundsPoster {
			vars: vars.into_iter().map(Into::into).collect(),
			min,
		}
	}
}

impl<P, E> Propagator<P, E> for ArrayIntMinimumBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "array_int_minimum", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let min_lb = self
			.vars
			.iter()
			.map(|&x| actions.get_int_lower_bound(x))
			.min()
			.unwrap();
		let (min_ub, min_ub_var) =
			self.vars
				.iter()
				.fold((IntVal::MAX, self.min), |(ub, var), &e| {
					let e_ub = actions.get_int_upper_bound(e);
					if e_ub < ub {
						(e_ub, e)
					} else {
						(ub, var)
					}
				});
		// set y to be less than or equal to the minimum of upper bounds of x_i
		let reason = actions.get_int_upper_bound_lit(min_ub_var);
		actions.set_int_upper_bound(self.min, min_ub, reason)?;

		// set y to be greater than or equal to the minimum of lower bounds of x_i
		actions.set_int_lower_bound(self.min, min_lb, |a: &mut P| {
			self.vars
				.iter()
				.map(|&x| a.get_int_lit(x, LitMeaning::GreaterEq(min_lb)))
				.collect_vec()
		})?;

		// set x_i to be greater than or equal to y.lowerbound
		let reason = actions.get_int_lower_bound_lit(self.min);
		let y_lb = actions.get_int_lower_bound(self.min);
		for &x in self.vars.iter() {
			actions.set_int_lower_bound(x, y_lb, reason)?;
		}

		Ok(())
	}
}

struct ArrayIntMinimumBoundsPoster {
	vars: Vec<IntView>,
	min: IntView,
}
impl Poster for ArrayIntMinimumBoundsPoster {
	fn post<I: InitializationActions>(
		self,
		actions: &mut I,
	) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
		let prop = ArrayIntMinimumBounds {
			vars: self.vars,
			min: self.min,
		};
		for &v in prop.vars.iter() {
			actions.enqueue_on_int_change(v, IntPropCond::Bounds);
		}
		actions.enqueue_on_int_change(prop.min, IntPropCond::LowerBound);
		Ok((
			Box::new(prop),
			QueuePreferences {
				enqueue_on_post: true,
				priority: PriorityLevel::Low,
			},
		))
	}

	fn name(&self) -> &'static str {
		"ArrayIntMinimumBounds"
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{model::ModelView, Constraint, InitConfig, Model};

	#[test]
	#[traced_test]
	fn test_minimum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=4).into());
		let b = prb.new_int_var((2..=3).into());
		let c = prb.new_int_var((2..=3).into());
		let y = prb.new_int_var((3..=4).into());

		prb += Constraint::ArrayIntMinimum(vec![a.clone(), b.clone(), c.clone()], y.clone());
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, &ModelView::from(x)))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		3, 3, 3, 3
		4, 3, 3, 3"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_minimum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((1..=2).into());

		prb += Constraint::ArrayIntMinimum(vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_maximum_sat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((1..=6).into());
		let b = prb.new_int_var((3..=5).into());
		let c = prb.new_int_var((2..=5).into());
		let y = prb.new_int_var((1..=3).into());

		prb += Constraint::ArrayIntMaximum(vec![a.clone(), b.clone(), c.clone()], y.clone());
		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![a, b, c, y]
			.into_iter()
			.map(|x| map.get(&mut slv, &ModelView::from(x)))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
		1, 3, 2, 3
		1, 3, 3, 3
		2, 3, 2, 3
		2, 3, 3, 3
		3, 3, 2, 3
		3, 3, 3, 3"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_maximum_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((3..=5).into());
		let b = prb.new_int_var((4..=5).into());
		let c = prb.new_int_var((4..=10).into());
		let y = prb.new_int_var((13..=20).into());

		prb += Constraint::ArrayIntMaximum(vec![a, b, c], y);
		prb.assert_unsatisfiable();
	}
}
