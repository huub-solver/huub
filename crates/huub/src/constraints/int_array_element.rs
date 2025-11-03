//! Structures and algorithms for the integer array element constraint, which
//! enforces that a resulting variable equals an element of an array of integer
//! values or decision variables, chosen by an index variable.

use std::{iter::once, ops::AddAssign};

use itertools::Itertools;
use pindakaas::{ClauseDatabase, ClauseDatabaseTools, Unsatisfiable};
use rustc_hash::FxHashMap;

use crate::{
	actions::{
		InitializationActions, IntDecisionActions, IntInspectionActions, IntSimplificationActions,
		PostingActions, ReasoningEngine, ReformulationActions, SimplificationActions,
		TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, BoolView,
		IntLitMeaning, IntView,
	},
	BoolDecision, IntDecision, IntVal, Model,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `array_element` constraint with an
/// array of integer decision variables.
pub struct IntArrayElementBounds<I1, I2, I3> {
	/// Array of variables from which the element is selected
	vars: Vec<I1>,
	/// Variable that represent the index of the selected variable
	index: I2,
	/// Variable that represent the result of the selection
	result: I3,
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
pub struct IntValArrayElement<I1, I2>(pub(crate) IntArrayElementBounds<IntVal, I1, I2>);

impl<I1, I2, I3> IntArrayElementBounds<I1, I2, I3> {
	/// Create a new [`ArrayVarIntElementBounds`] propagator and post it in the
	/// solver.
	pub(crate) fn new<E>(engine: &mut E, collection: Vec<I1>, index: I2, result: I3) -> Self
	where
		E: InitializationActions + ?Sized,
		I1: IntInspectionActions<E>,
		I2: IntInspectionActions<E>,
	{
		// Initialize the min_support and max_support variables
		let mut min_support = -1;
		let mut max_support = -1;
		let mut min_lb = IntVal::MAX;
		let mut max_ub = IntVal::MIN;
		for (i, v) in collection.iter().enumerate() {
			if index.check_in_domain(engine, i as IntVal) {
				let (lb, ub) = v.get_bounds(engine);
				if min_support == -1 || lb < min_lb {
					min_support = i as IntVal;
					min_lb = lb;
				}
				if max_support == -1 || ub > max_ub {
					max_support = i as IntVal;
					max_ub = ub;
				}
			}
		}
		let min_support = engine.new_trailed_int(min_support);
		let max_support = engine.new_trailed_int(max_support);

		Self {
			vars: collection.clone(),
			result,
			index,
			min_support,
			max_support,
		}
	}
}

impl IntArrayElementBounds<IntView, IntView, IntView> {
	/// Create a new [`ArrayVarIntElementBounds`] propagator and post it in the
	/// solver.
	pub fn new_in<E>(
		engine: &mut E,
		collection: Vec<IntView>,
		index: IntView,
		result: IntView,
	) -> Result<(), Unsatisfiable>
	where
		E: AddAssign<BoxedPropagator> + ClauseDatabase + InitializationActions + ?Sized,
		IntView: IntDecisionActions<E, Atom = BoolView>,
	{
		// Remove out-of-bound values from the index variables
		let index_ub = index.get_lit(engine, IntLitMeaning::Less(collection.len() as IntVal));
		let index_lb = index.get_lit(engine, IntLitMeaning::GreaterEq(0));
		engine.add_clause([index_ub])?;
		engine.add_clause([index_lb])?;

		let me = Self::new(engine, collection, index, result);
		*engine += Box::new(me);

		Ok(())
	}
}

impl<E, I1, I2, I3> Constraint<E> for IntArrayElementBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	I1: ModelIntView<E>,
	I2: ModelIntView<E>,
	I3: ModelIntView<E>,
	IntDecision: ModelIntView<E>,
	IntVal: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Constrain the index to be within the bounds of the array
		self.index.set_lower_bound(ctx, 0, [])?;
		self.index
			.set_upper_bound(ctx, self.vars.len() as IntVal - 1, [])?;

		self.propagate(ctx)?;
		if let Some(i) = self.index.get_val(ctx) {
			self.vars[i as usize]
				.clone()
				.into()
				.unify(ctx, self.result.clone())?;
			return Ok(SimplificationStatus::Subsumed);
		} else if self.vars.iter().all(|v| v.get_val(ctx).is_some()) {
			let vars = self
				.vars
				.iter()
				.map(|v| v.get_val(ctx).unwrap())
				.collect_vec();
			let rewrite = IntValArrayElement(IntArrayElementBounds {
				vars,
				index: self.index.clone(),
				result: self.result.clone(),
				min_support: self.min_support,
				max_support: self.max_support,
			});
			ctx.add_constraint(rewrite);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, ctx: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let array = self
			.vars
			.iter()
			.map(|v| ctx.get_solver_int(v.clone().into()))
			.collect();
		let result = ctx.get_solver_int(self.result.clone().into());
		let index = ctx.get_solver_int(self.index.clone().into());
		IntArrayElementBounds::new_in(ctx, array, result, index).unwrap();
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntArrayElementBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
	I3: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		self.result.enqueue_when(ctx, IntPropCond::Bounds);
		self.index.enqueue_when(ctx, IntPropCond::Domain);
		for (i, v) in self.vars.iter().enumerate() {
			if self.index.check_in_domain(ctx, i as IntVal) {
				v.enqueue_when(ctx, IntPropCond::Bounds);
			}
		}
	}

	#[tracing::instrument(name = "array_int_element", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// ensure bounds of result and self.vars[self.index] are consistent when
		// self.index is fixed only trigger when self.index is fixed and (1) y is
		// updated or (2) self.vars[self.index] is updated
		if let Some(fixed_index) = self.index.get_val(ctx) {
			let index_val_lit = self.index.get_val_lit(ctx).unwrap();
			let fixed_var = &self.vars[fixed_index as usize];
			self.result.set_lower_bound(
				ctx,
				fixed_var.get_lower_bound(ctx),
				|ctx: &mut E::PropagationCtx<'_>| {
					[index_val_lit.clone(), fixed_var.get_lower_bound_lit(ctx)]
				},
			)?;
			fixed_var.set_lower_bound(
				ctx,
				self.result.get_lower_bound(ctx),
				|ctx: &mut E::PropagationCtx<'_>| {
					[index_val_lit.clone(), self.result.get_lower_bound_lit(ctx)]
				},
			)?;
			self.result.set_upper_bound(
				ctx,
				fixed_var.get_upper_bound(ctx),
				|ctx: &mut E::PropagationCtx<'_>| {
					[index_val_lit.clone(), fixed_var.get_upper_bound_lit(ctx)]
				},
			)?;
			fixed_var.set_upper_bound(
				ctx,
				self.result.get_upper_bound(ctx),
				|ctx: &mut E::PropagationCtx<'_>| {
					[index_val_lit.clone(), self.result.get_upper_bound_lit(ctx)]
				},
			)?;
			return Ok(());
		}

		let (result_lb, result_ub) = self.result.get_bounds(ctx);
		let min_support = ctx.get_trailed_int(self.min_support);
		let max_support = ctx.get_trailed_int(self.max_support);
		let old_min = self.vars[min_support as usize].get_lower_bound(ctx);
		let old_max = self.vars[max_support as usize].get_upper_bound(ctx);
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
			if !self.index.check_in_domain(ctx, i as IntVal) {
				continue;
			}

			let (v_lb, v_ub) = v.get_bounds(ctx);
			if result_ub < v_lb {
				self.index
					.set_not_eq(ctx, i as IntVal, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.result.get_lit(ctx, IntLitMeaning::Less(v_lb)),
							v.get_lower_bound_lit(ctx),
						]
					})?;
			}

			if v_ub < result_lb {
				self.index
					.set_not_eq(ctx, i as IntVal, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.result.get_lit(ctx, IntLitMeaning::GreaterEq(v_ub + 1)),
							v.get_upper_bound_lit(ctx),
						]
					})?;
			}

			// update min_support if i is in the domain of self.index and the lower bound of
			// // v is less than the current min
			if need_min_support && v_lb < new_min {
				new_min_support = i as IntVal;
				new_min = v_lb;
				// stop finding min_support if new_min ≤ y_lb
				need_min_support = new_min > result_lb;
			}

			// update max_support if i is in the domain of self.index and the upper bound of
			// v is greater than the current max
			if need_max_support && v_ub > new_max {
				new_max_support = i as IntVal;
				new_max = v_ub;
				// stop finding max_support if new_max ≥ y_ub
				need_max_support = new_max < result_ub;
			}
		}

		let _ = ctx.set_trailed_int(self.min_support, new_min_support);
		let _ = ctx.set_trailed_int(self.max_support, new_max_support);

		// propagate the lower bound of the selected variable y if min_support is not
		// valid anymore:
		//
		//   result.lower_bound >= min(i in domain(x))(self.vars[i].lower_bound)
		//
		// only trigger when self.vars[min_support] is changed or self.vars[min_support]
		// is out of domain
		if new_min > result_lb {
			self.result
				.set_lower_bound(ctx, new_min, |ctx: &mut E::PropagationCtx<'_>| {
					self.vars
						.iter()
						.enumerate()
						.map(|(i, v)| {
							if self.index.check_in_domain(ctx, i as IntVal) {
								v.get_lit(ctx, IntLitMeaning::GreaterEq(new_min))
							} else {
								self.index.get_lit(ctx, IntLitMeaning::NotEq(i as IntVal))
							}
						})
						.collect_vec()
				})?;
		}

		// propagate the upper bound of the selected variable y if max_support is not
		// valid anymore:
		//
		//   result.upper_bound <= max(i in domain(x))(self.vars[i].upper_bound)
		//
		// only trigger when self.vars[max_support] is changed or self.vars[max_support]
		// is out of domain
		if new_max < result_ub {
			self.result
				.set_upper_bound(ctx, new_max, |ctx: &mut E::PropagationCtx<'_>| {
					self.vars
						.iter()
						.enumerate()
						.map(|(i, v)| {
							if self.index.check_in_domain(ctx, i as IntVal) {
								v.get_lit(ctx, IntLitMeaning::Less(new_max + 1))
							} else {
								self.index.get_lit(ctx, IntLitMeaning::NotEq(i as IntVal))
							}
						})
						.collect_vec()
				})?;
		}

		Ok(())
	}
}

impl<E, I1, I2> Constraint<E> for IntValArrayElement<I1, I2>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	I1: ModelIntView<E>,
	I2: ModelIntView<E>,
	IntVal: ModelIntView<E>,
	IntDecision: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Constrain the index to be within the bounds of the array
		self.0.index.set_lower_bound(ctx, 0, [])?;
		self.0
			.index
			.set_upper_bound(ctx, self.0.vars.len() as IntVal - 1, [])?;

		self.0.propagate(ctx)?;
		if let Some(i) = self.0.index.get_val(ctx) {
			self.0
				.result
				.clone()
				.into()
				.unify(ctx, self.0.vars[i as usize])?;
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let index = slv.get_solver_int(self.0.index.clone().into());
		let result = slv.get_solver_int(self.0.result.clone().into());

		// Make a map from the values of the array to the indexes at which they
		// occur (follows [`Itertools::into_group_map`])
		let mut idx_map = FxHashMap::default();
		self.0.vars.iter().enumerate().for_each(|(idx, &val)| {
			idx_map
				.entry(val)
				.or_insert_with(Vec::new)
				.push(idx as IntVal);
		});

		#[expect(clippy::iter_over_hash_type, reason = "FxHashMap::iter is stable")]
		for (val, idxs) in idx_map {
			let val_eq = result.get_lit(slv, IntLitMeaning::Eq(val));
			let idxs: Vec<_> = idxs
				.iter()
				.map(|&i| index.get_lit(slv, IntLitMeaning::Eq(i)))
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

impl<E, I1, I2> Propagator<E> for IntValArrayElement<I1, I2>
where
	E: ReasoningEngine,
	I1: SolverIntView<E>,
	I2: SolverIntView<E>,
	IntVal: SolverIntView<E>,
{
	fn post(&mut self, ctx: &mut E::PostingCtx<'_>) {
		self.0.post(ctx);
	}

	fn propagate(&mut self, _: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		unreachable!()
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		array_element,
		constraints::int_array_element::IntArrayElementBounds,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		Model,
	};

	#[test]
	#[traced_test]
	fn test_element_bounds_sat() {
		let mut slv = Solver::default();
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

		IntArrayElementBounds::new_in(&mut slv, vec![a, b, c], index, y).unwrap();

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
		let mut slv = Solver::default();
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

		IntArrayElementBounds::new_in(&mut slv, vec![a, b], index, y).unwrap();

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
		let a = prb.new_int_var(3..=5);
		let b = prb.new_int_var(4..=5);
		let c = prb.new_int_var(4..=10);
		let result = prb.new_int_var(1..=2);
		let index = prb.new_int_var(0..=2);

		array_element(&mut prb, vec![a, b, c], index, result);
		prb.assert_unsatisfiable();
	}
}
