//! Structures and algorithms for the integer array element constraint, which
//! enforces that a resulting variable equals an element of an array of integer
//! values or decision variables, chosen by an index variable.

use std::iter::once;

use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	IntSet, IntVal,
	actions::{
		ConstructionActions, InitActions, IntDecisionActions, IntInspectionActions,
		IntSimplificationActions, PostingActions, ReasoningContext, ReasoningEngine,
		SimplificationActions, Trailed, TrailingActions,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds consistent propagator for the `array_element` constraint with an
/// array of integer decision variables.
pub struct IntArrayElementBounds<I1, I2, I3> {
	/// Array of variables from which the element is selected
	vars: Vec<I1>,
	/// Variable that represent the index of the selected variable
	pub(crate) index: I2,
	/// Variable that represent the result of the selection
	result: I3,
	/// The index of the variable that supports the lower bound of the result
	min_support: Trailed<usize>,
	/// The index of the variable that supports the upper bound of the result
	max_support: Trailed<usize>,
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
		E: ConstructionActions + ReasoningContext + ?Sized,
		I1: IntInspectionActions<E>,
		I2: IntInspectionActions<E>,
	{
		// Initialize the min_support and max_support variables
		let mut min_support = None;
		let mut max_support = None;
		let mut min_lb = IntVal::MAX;
		let mut max_ub = IntVal::MIN;
		for i in index
			.domain(engine)
			.iter()
			.flatten()
			.filter(|&v| v >= 0 && v < collection.len() as IntVal)
		{
			let i = i as usize;
			let (lb, ub) = collection[i].bounds(engine);
			if min_support.is_none() || lb < min_lb {
				min_support = Some(i);
				min_lb = lb;
			}
			if max_support.is_none() || ub > max_ub {
				max_support = Some(i);
				max_ub = ub;
			}
		}
		let min_support = engine.new_trailed(min_support.unwrap());
		let max_support = engine.new_trailed(max_support.unwrap());

		Self {
			vars: collection.clone(),
			result,
			index,
			min_support,
			max_support,
		}
	}

	/// Create a new [`IntArrayElementBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(
		solver: &mut E,
		collection: Vec<I1>,
		index: I2,
		result: I3,
	) -> Result<(), E::Conflict>
	where
		E: PostingActions + ?Sized,
		I1: IntSolverActions<Engine> + IntDecisionActions<E>,
		I2: IntSolverActions<Engine> + IntDecisionActions<E>,
		I3: IntSolverActions<Engine>,
	{
		// Remove out-of-bound values from the index variables
		let index_ub = index.lit(solver, IntLitMeaning::Less(collection.len() as IntVal));
		let index_lb = index.lit(solver, IntLitMeaning::GreaterEq(0));
		solver.add_clause([index_ub])?;
		solver.add_clause([index_lb])?;

		let me = Self::new(solver, collection, index, result);
		solver.add_propagator(Box::new(me));

		Ok(())
	}
}

impl<E, I1, I2, I3> Constraint<E> for IntArrayElementBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
	I3: IntModelActions<E>,
	View<IntVal>: IntModelActions<E>,
	IntVal: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Constrain the index to be within the bounds of the array
		self.index.tighten_min(ctx, 0, [])?;
		self.index
			.tighten_max(ctx, self.vars.len() as IntVal - 1, [])?;

		self.propagate(ctx)?;

		if let Some(i) = self.index.val(ctx) {
			self.vars[i as usize]
				.clone()
				.into()
				.unify(ctx, self.result.clone())?;
			return Ok(SimplificationStatus::Subsumed);
		} else if self.vars.iter().all(|v| v.val(ctx).is_some()) {
			let vars = self.vars.iter().map(|v| v.val(ctx).unwrap()).collect_vec();
			let rewrite = IntValArrayElement(IntArrayElementBounds {
				vars,
				index: self.index.clone(),
				result: self.result.clone(),
				min_support: self.min_support,
				max_support: self.max_support,
			});
			ctx.post_constraint(rewrite);
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, ctx: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let array = self
			.vars
			.iter()
			.map(|v| ctx.solver_view(v.clone().into()))
			.collect();
		let result = ctx.solver_view(self.result.clone().into());
		let index = ctx.solver_view(self.index.clone().into());
		IntArrayElementBounds::post(ctx, array, index, result).unwrap();
		Ok(())
	}
}

impl<E, I1, I2, I3> Propagator<E> for IntArrayElementBounds<I1, I2, I3>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
	I3: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		self.result.enqueue_when(ctx, IntPropCond::Bounds);
		self.index.enqueue_when(ctx, IntPropCond::Domain);
		for i in self
			.index
			.domain(ctx)
			.iter()
			.flatten()
			.filter(|&v| v >= 0 && v < self.vars.len() as IntVal)
		{
			self.vars[i as usize].enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	#[tracing::instrument(name = "array_int_element", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// ensure bounds of result and self.vars[self.index] are consistent when
		// self.index is fixed only trigger when self.index is fixed and (1) y is
		// updated or (2) self.vars[self.index] is updated
		if let Some(fixed_index) = self.index.val(ctx) {
			let index_val_lit = self.index.val_lit(ctx).unwrap();
			let fixed_var = &self.vars[fixed_index as usize];
			self.result.tighten_min(
				ctx,
				fixed_var.min(ctx),
				|ctx: &mut E::PropagationCtx<'_>| [index_val_lit.clone(), fixed_var.min_lit(ctx)],
			)?;
			fixed_var.tighten_min(
				ctx,
				self.result.min(ctx),
				|ctx: &mut E::PropagationCtx<'_>| [index_val_lit.clone(), self.result.min_lit(ctx)],
			)?;
			self.result.tighten_max(
				ctx,
				fixed_var.max(ctx),
				|ctx: &mut E::PropagationCtx<'_>| [index_val_lit.clone(), fixed_var.max_lit(ctx)],
			)?;
			fixed_var.tighten_max(
				ctx,
				self.result.max(ctx),
				|ctx: &mut E::PropagationCtx<'_>| [index_val_lit.clone(), self.result.max_lit(ctx)],
			)?;
			return Ok(());
		}

		let (result_lb, result_ub) = self.result.bounds(ctx);
		let min_support = ctx.trailed(self.min_support);
		let max_support = ctx.trailed(self.max_support);
		let old_min = self.vars[min_support].min(ctx);
		let old_max = self.vars[max_support].max(ctx);
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
		let idx_dom: IntSet = self.index.domain(ctx);
		for i in idx_dom.iter().flatten() {
			debug_assert!(i >= 0 && i <= self.vars.len() as IntVal);
			let i = i as usize;
			let v = &self.vars[i];

			let (v_lb, v_ub) = v.bounds(ctx);
			if result_ub < v_lb {
				self.index
					.remove_val(ctx, i as IntVal, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.result.lit(ctx, IntLitMeaning::Less(v_lb)),
							v.min_lit(ctx),
						]
					})?;
			}

			if v_ub < result_lb {
				self.index
					.remove_val(ctx, i as IntVal, |ctx: &mut E::PropagationCtx<'_>| {
						[
							self.result.lit(ctx, IntLitMeaning::GreaterEq(v_ub + 1)),
							v.max_lit(ctx),
						]
					})?;
			}

			// update min_support if i is in the domain of self.index and the lower bound of
			// // v is less than the current min
			if need_min_support && v_lb < new_min {
				new_min_support = i;
				new_min = v_lb;
				// stop finding min_support if new_min ≤ y_lb
				need_min_support = new_min > result_lb;
			}

			// update max_support if i is in the domain of self.index and the upper bound of
			// v is greater than the current max
			if need_max_support && v_ub > new_max {
				new_max_support = i;
				new_max = v_ub;
				// stop finding max_support if new_max ≥ y_ub
				need_max_support = new_max < result_ub;
			}
		}

		ctx.set_trailed(self.min_support, new_min_support);
		ctx.set_trailed(self.max_support, new_max_support);

		// propagate the lower bound of the selected variable y if min_support is not
		// valid anymore:
		//
		//   result.lower_bound >= min(i in domain(x))(self.vars[i].lower_bound)
		//
		// only trigger when self.vars[min_support] is changed or self.vars[min_support]
		// is out of domain
		if new_min > result_lb {
			self.result
				.tighten_min(ctx, new_min, |ctx: &mut E::PropagationCtx<'_>| {
					let mut reason = Vec::with_capacity(self.vars.len());
					let dom = self.index.domain(ctx);
					let mut dom = dom.iter().flatten().peekable();
					for (i, v) in self.vars.iter().enumerate() {
						debug_assert!(dom.peek().is_none() || *dom.peek().unwrap() >= i as IntVal);
						if dom.peek() == Some(&(i as IntVal)) {
							reason.push(v.lit(ctx, IntLitMeaning::GreaterEq(new_min)));
							dom.next();
						} else {
							reason.push(self.index.lit(ctx, IntLitMeaning::NotEq(i as IntVal)));
						}
					}
					reason
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
				.tighten_max(ctx, new_max, |ctx: &mut E::PropagationCtx<'_>| {
					let mut reason = Vec::with_capacity(self.vars.len());
					let dom = self.index.domain(ctx);
					let mut dom = dom.iter().flatten().peekable();
					for (i, v) in self.vars.iter().enumerate() {
						debug_assert!(dom.peek().is_none() || *dom.peek().unwrap() >= i as IntVal);
						if dom.peek() == Some(&(i as IntVal)) {
							reason.push(v.lit(ctx, IntLitMeaning::Less(new_max + 1)));
							dom.next();
						} else {
							reason.push(self.index.lit(ctx, IntLitMeaning::NotEq(i as IntVal)));
						}
					}
					reason
				})?;
		}

		Ok(())
	}
}

impl<E, I1, I2> Constraint<E> for IntValArrayElement<I1, I2>
where
	E: ReasoningEngine,
	for<'a> E::PropagationCtx<'a>: SimplificationActions<Target = E>,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
	IntVal: IntModelActions<E>,
	View<IntVal>: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Constrain the index to be within the bounds of the array
		self.0.index.tighten_min(ctx, 0, [])?;
		self.0
			.index
			.tighten_max(ctx, self.0.vars.len() as IntVal - 1, [])?;

		self.0.propagate(ctx)?;

		if let Some(i) = self.0.index.val(ctx) {
			self.0
				.result
				.clone()
				.into()
				.unify(ctx, self.0.vars[i as usize])?;
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let index = slv.solver_view(self.0.index.clone().into());
		let result = slv.solver_view(self.0.result.clone().into());

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
			let val_eq = result.lit(slv, IntLitMeaning::Eq(val));
			let idxs: Vec<_> = idxs
				.iter()
				.map(|&i| index.lit(slv, IntLitMeaning::Eq(i)))
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
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
	IntVal: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		self.0.initialize(ctx);
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
		Model,
		constraints::int_array_element::IntArrayElementBounds,
		solver::{
			Solver,
			decision::integer::{EncodingType, IntDecision},
		},
	};

	#[test]
	#[traced_test]
	fn test_element_bounds_sat() {
		let mut slv = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([2..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([4..=5]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let y = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let index = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([0..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntArrayElementBounds::post(&mut slv, vec![a, b, c], index, y).unwrap();

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
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let y = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([3..=4]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let index = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 3..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntArrayElementBounds::post(&mut slv, vec![a, b], index, y).unwrap();

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
		let a = prb.new_int_decision(3..=5);
		let b = prb.new_int_decision(4..=5);
		let c = prb.new_int_decision(4..=10);
		let result = prb.new_int_decision(1..=2);
		let index = prb.new_int_decision(0..=2);

		prb.element(vec![a, b, c])
			.index(index)
			.result(result)
			.post();
		prb.assert_unsatisfiable();
	}
}
