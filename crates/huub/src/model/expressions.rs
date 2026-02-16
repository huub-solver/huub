//! Helper types and functions used to build constraints for a [`Model`].

#![allow(
	clippy::missing_docs_in_private_items,
	reason = "unable to document members of generated builders"
)]

pub(crate) mod bool_formula;
pub(crate) mod element;
pub(crate) mod linear;

use std::{cmp, marker::PhantomData};

use bon::bon;
use itertools::{Itertools, MinMaxResult, iproduct};

pub use crate::model::expressions::{
	bool_formula::BoolFormula, element::ElementConstraint, linear::IntLinearExp,
};
use crate::{
	IntSet, IntVal,
	actions::IntInspectionActions,
	constraints::{
		cumulative::CumulativeTimeTable,
		disjunctive::{Disjunctive, DisjunctivePropagator},
		int_abs::IntAbsBounds,
		int_array_minimum::IntArrayMinimumBounds,
		int_div::IntDivBounds,
		int_linear::{IntLinear, LinComparator, Reification},
		int_mul::IntMulBounds,
		int_no_overlap::IntNoOverlapSweep,
		int_pow::IntPowBounds,
		int_set_contains::IntSetContainsReif,
		int_table::IntTable,
		int_unique::{IntUnique, IntUniqueBounds},
		int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
	},
	helpers::overflow::{OverflowImpossible, OverflowPossible},
	model::{Model, View, expressions::linear::Comparator},
};

#[bon]
impl Model {
	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that the second integer decision
	/// variable takes the absolute value of the first integer decision
	/// variable.
	pub fn abs(
		&mut self,
		#[builder(into, start_fn)] origin: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) {
		self.post_constraint(IntAbsBounds {
			origin,
			abs: result,
			origin_positive: origin.geq(0),
		});
	}

	#[builder(finish_fn = post)]
	/// Create constraint that enforces that the given Boolean variable takes
	/// the value `true` if-and-only-if an integer variable is in a given set.
	pub fn contains(
		&mut self,
		#[builder(start_fn, into)] collection: IntSet,
		#[builder(into)] member: View<IntVal>,
		#[builder(into)] result: View<bool>,
	) {
		self.post_constraint(IntSetContainsReif {
			var: member,
			set: collection,
			reif: result,
		});
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that the given a list of integer
	/// decision variables representing the start times of tasks, a list of
	/// integer values representing the durations of tasks, a list of integer
	/// values representing the resource usages of tasks, and a resource
	/// capacity, the sum of the resource usages of all tasks running at any
	/// time does not exceed the resource capacity.
	pub fn cumulative(
		&mut self,
		start_times: Vec<impl Into<View<IntVal>>>,
		durations: Vec<impl Into<View<IntVal>>>,
		usages: Vec<impl Into<View<IntVal>>>,
		capacity: impl Into<View<IntVal>>,
	) {
		assert_eq!(
			start_times.len(),
			durations.len(),
			"cumulative must be given the same number of start times and durations."
		);
		assert_eq!(
			start_times.len(),
			usages.len(),
			"cumulative must be given the same number of start times and usages."
		);
		self.post_constraint(CumulativeTimeTable::new(
			start_times.into_iter().map_into().collect(),
			durations.into_iter().map_into().collect(),
			usages.into_iter().map_into().collect(),
			capacity.into(),
		));
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that the given a list of integer
	/// decision variables representing the start times of tasks and a list of
	/// integer values representing the durations of tasks, the tasks do not
	/// overlap in time.
	///
	/// Note that this constraint is strict, meaning that tasks with a zero
	/// duration cannot occur during another task.
	pub fn disjunctive(
		&mut self,
		start_times: Vec<View<IntVal>>,
		durations: Vec<IntVal>,
		edge_finding_propagation: Option<bool>,
		not_last_propagation: Option<bool>,
		detectable_precedence_propagation: Option<bool>,
	) {
		assert_eq!(
			start_times.len(),
			durations.len(),
			"disjunctive must be given the same number of start times and durations."
		);
		assert!(
			durations.iter().all(|&dur| dur >= 0),
			"disjunctive cannot be given any negative durations."
		);
		let propagator = DisjunctivePropagator::new(self, start_times, durations, true, true, true);
		self.post_constraint(Disjunctive {
			propagator,
			edge_finding_propagation,
			not_last_propagation,
			detectable_precedence_propagation,
		});
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that a numerator decision integer
	/// variable divided by a denominator integer decision variable is equal to
	/// a result integer decision variable.
	pub fn div(
		&mut self,
		#[builder(into, start_fn)] numerator: View<IntVal>,
		#[builder(into, start_fn)] denominator: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) {
		self.post_constraint(IntDivBounds {
			numerator,
			denominator,
			result,
		});
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that a result decision variable takes
	/// the value equal the element of the given array at the given index
	/// decision variable.
	pub fn element<E: ElementConstraint>(
		&mut self,
		#[builder(start_fn)] array: Vec<E>,
		#[builder(getter(name = index_internal, vis = ""), into)] index: View<IntVal>,
		result: <E as ElementConstraint>::Result,
	) {
		<E as ElementConstraint>::element_constraint(self, array, index, result);
	}

	#[builder(finish_fn = post)]
	/// Create a linear equation constraint.
	pub fn linear(
		&mut self,
		#[builder(start_fn, into)] mut expr: IntLinearExp,
		#[builder(setters(name = comparator_internal, vis = ""))] comparator: Comparator,
		#[builder(setters(name = constant_internal, vis = ""))] constant: IntVal,
		#[builder(setters(name = reif_internal, vis = ""))] reif: Option<Reification>,
	) {
		let mut negate_terms = || {
			expr.terms.iter_mut().for_each(|v| {
				*v = v
					.bounding_neg(self)
					.expect("TODO: need to defer failure to propagate");
			});
		};

		let (comparator, rhs) = match comparator {
			Comparator::Less => (LinComparator::LessEq, constant - 1),
			Comparator::LessEqual => (LinComparator::LessEq, constant),
			Comparator::Equal => (LinComparator::Equal, constant),
			Comparator::GreaterEqual => {
				negate_terms();
				(LinComparator::LessEq, -constant)
			}
			Comparator::Greater => {
				negate_terms();
				(LinComparator::LessEq, -constant - 1)
			}
			Comparator::NotEqual => (LinComparator::NotEqual, constant),
		};

		if IntLinear::can_overflow(self, &expr.terms) {
			self.post_constraint(IntLinear::<OverflowPossible> {
				terms: expr.terms,
				rhs: rhs.into(),
				reif,
				comparator,
			});
		} else {
			self.post_constraint(IntLinear::<OverflowImpossible> {
				terms: expr.terms,
				rhs,
				reif,
				comparator,
			});
		}
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that an integer decision variable
	/// takes the minimum value of an array of integer decision variables.
	pub fn maximum(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(into)] result: View<IntVal>,
	) {
		self.minimum(vars.into_iter().map(|v| -v))
			.result(-result)
			.post();
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that an integer decision variable
	/// takes the minimum value of an array of integer decision variables.
	pub fn minimum(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(into)] result: View<IntVal>,
	) {
		self.post_constraint(IntArrayMinimumBounds {
			vars: vars.into_iter().collect(),
			min: result,
		});
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that the product of the two integer
	/// decision variables is equal to a third.
	pub fn mul(
		&mut self,
		#[builder(start_fn)] factor1: View<IntVal>,
		#[builder(start_fn)] factor2: View<IntVal>,
		result: View<IntVal>,
	) {
		if IntMulBounds::<_, _, _, View<IntVal>>::can_overflow(self, &factor1, &factor2) {
			self.post_constraint(IntMulBounds::<OverflowPossible, _, _, _> {
				factor1,
				factor2,
				product: result,
				overflow_mode: PhantomData,
			});
		} else {
			self.post_constraint(IntMulBounds::<OverflowImpossible, _, _, _> {
				factor1,
				factor2,
				product: result,
				overflow_mode: PhantomData,
			});
		}
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that given decision variables of
	/// origin/starting positions and sizes of k-dimensional hyperrectangles,
	/// none of the rectangles overlap.
	///
	/// # Parameters
	///
	/// - `prb`: The [`Model`] instance.
	/// - `origin`: A matrix-like `Vec<Vec<I>>` where `origin[i][d]` is the
	///   origin of object `i` in dimension `d`.
	/// - `size`: A matrix-like `Vec<Vec<I>>` where `size[i][d]` is the size of
	///   object `i` in dimension `d`.
	/// - `strict`: If set to `true` (as it is by default), the constraint
	///   ensures that objects of with 0 size do not occur within other objects.
	///
	/// # Panics
	///
	/// Panics if the dimensions of `origin` and `size` are inconsistent.
	/// Specifically, the number of objects (outer `Vec` length) must be the
	/// same, and the number of dimensions (inner `Vec` length) must be the
	/// same for all objects.
	pub fn no_overlap(
		&mut self,
		origins: Vec<Vec<View<IntVal>>>,
		sizes: Vec<Vec<View<IntVal>>>,
		#[builder(default = true)] strict: bool,
	) {
		if strict {
			let prop = IntNoOverlapSweep::<true, _, _>::new(self, origins, sizes);
			self.post_constraint(prop);
		} else {
			let prop = IntNoOverlapSweep::<false, _, _>::new(self, origins, sizes);
			self.post_constraint(prop);
		}
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that a base integer decision variable
	/// exponentiation by an exponent integer decision variable is equal to a
	/// result integer decision variable.
	pub fn pow(
		&mut self,
		#[builder(start_fn, into)] base: View<IntVal>,
		#[builder(start_fn, into)] exponent: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) {
		if IntPowBounds::<_, _, _, View<IntVal>>::can_overflow(self, &base, &exponent) {
			self.post_constraint(IntPowBounds::<OverflowPossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			});
		} else {
			self.post_constraint(IntPowBounds::<OverflowImpossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			});
		}
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that a propositional logic formula is
	/// true.
	pub fn proposition(
		&mut self,
		#[builder(start_fn, into)] mut formula: BoolFormula,
		#[builder(setters(name = reif_internal, vis = ""))] reif: Option<Reification>,
	) {
		match reif {
			Some(Reification::ReifiedBy(b)) => {
				formula = BoolFormula::Equiv(vec![BoolFormula::Atom(b), formula]);
			}
			Some(Reification::ImpliedBy(b)) => {
				formula = BoolFormula::Implies(BoolFormula::Atom(b).into(), formula.into());
			}
			None => {}
		}
		self.post_constraint(formula);
	}

	#[builder(finish_fn = post)]
	/// Create a `table` constraint that enforces that given list of integer
	/// views take their values according to one of the given lists of integer
	/// values.
	pub fn table(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		values: impl IntoIterator<Item = Vec<IntVal>>,
	) {
		let vars: Vec<_> = vars.into_iter().collect();
		let table: Vec<_> = values.into_iter().collect();
		assert!(
			table.iter().all(|tup| tup.len() == vars.len()),
			"The number of values in each row of the table must be equal to the number of decision variables."
		);
		self.post_constraint(IntTable { vars, table });
	}

	#[builder(finish_fn = post)]
	/// Create a constraint that enforces that all the given integer decisions
	/// take different values.
	pub fn unique(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		bounds_propagation: Option<bool>,
		value_propagation: Option<bool>,
	) {
		self.post_constraint(IntUnique {
			prop: IntUniqueBounds::new(vars.into_iter().map_into().collect()),
			bounds_propagation,
			value_propagation,
		});
	}

	#[builder(finish_fn = post)]
	/// Create a value precede (chain) constraint that enforces that the first
	/// occurrence of each value in `values` among the decisions `vars` happens
	/// in the order of `values`.
	///
	/// If no values are explicitly provided, then the values are assumed to be
	/// consecutive integers starting from 1. This variant of the constraint is
	/// sometimes referred to as a sequential precede chain constraint.
	pub fn value_precede(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(with = |values: impl IntoIterator<Item = IntVal>| values.into_iter().collect())]
		values: Option<Vec<IntVal>>,
	) {
		let mut offset = 0;
		if let Some(values) = values {
			// If the list of values is empty, then the constraint is trivially
			// satisfied.
			if values.is_empty() {
				return;
			}
			// If the values are consecutive, then this is actually a sequential precede
			// chain constraint and we can use the `IntValuePrecedeChainValue` constraint.
			if values.iter().tuple_windows().all(|(&x, &y)| x + 1 == y) {
				let con = IntValuePrecedeChainValue::new(
					self,
					values.into_iter().collect(),
					vars.into_iter().collect(),
				);
				self.post_constraint(con);
				return;
			}
			// The `values` array might not have started at 1, calculate the offset to
			// subtract from the decision variables.
			offset = values[0] - 1;
		}

		let vars = vars
			.into_iter()
			.map(|v| {
				v.bounding_sub(self, offset)
					.expect("TODO: need to defer failure to propagate")
			})
			.collect();
		let con = IntSeqPrecedeChainBounds::new(self, vars);
		self.post_constraint(con);
	}
}

impl<S: model_abs_builder::State> ModelAbsBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the absolute
	/// value of the given integer variable.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_abs_builder::IsUnset,
	{
		let (min, max) = self.origin.bounds(self.self_receiver);
		let res = self
			.self_receiver
			.new_int_decision(0..=cmp::max(min.abs(), max.abs()));
		self.result(res).post();
		res
	}
}

impl<S: model_contains_builder::State> ModelContainsBuilder<'_, S> {
	/// Create a new Boolean decision variable that is defined as `true` if and
	/// only if the set contains the given element.
	pub fn define(self) -> View<bool>
	where
		S::Member: model_contains_builder::IsSet,
		S::Result: model_contains_builder::IsUnset,
	{
		let res = self.self_receiver.new_bool_decision();
		self.result(res).post();
		res
	}
}

impl<S: model_div_builder::State> ModelDivBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// the division of the given two integer variables.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_div_builder::IsUnset,
	{
		let (num_min, num_max) = self.numerator.bounds(self.self_receiver);
		let (den_min, den_max) = self.denominator.bounds(self.self_receiver);
		let mut den_candidates = Vec::new();
		if den_min != 0 {
			den_candidates.push(den_min);
		}
		if den_max != 0 {
			den_candidates.push(den_max);
		}
		if den_min < 1 && 1 < den_max {
			den_candidates.push(1);
		}
		if den_min < -1 && -1 < den_max {
			den_candidates.push(1);
		}

		let range = match iproduct!([num_min, num_max], den_candidates)
			.map(|(num, den)| num / den)
			.minmax()
		{
			MinMaxResult::NoElements => IntVal::MIN..=IntVal::MAX,
			MinMaxResult::OneElement(v) => v..=v,
			MinMaxResult::MinMax(min, max) => min..=max,
		};

		let res = self.self_receiver.new_int_decision(range);
		self.result(res).post();
		res
	}
}

impl<E: ElementConstraint, S: model_element_builder::State> ModelElementBuilder<'_, E, S> {
	/// Create a new decision variable that is defined as the element at the
	/// given index in the collection.
	pub fn define(self) -> E::Result
	where
		S::Index: model_element_builder::IsSet,
		S::Result: model_element_builder::IsUnset,
	{
		let index = self.index_internal();
		let res = E::define_result(self.self_receiver, &self.array, *index);
		self.result(res.clone()).post();
		res
	}
}

impl<'a, S: model_linear_builder::State> ModelLinearBuilder<'a, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// the linear expression.
	pub fn define(mut self) -> View<IntVal>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Reif: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision((IntVal::MIN + 1)..=IntVal::MAX);
		self.expr += -res;
		self.comparator_internal(Comparator::Equal)
			.constant_internal(0)
			.post();
		res
	}

	/// Equate the linear expression to be equal to the given value.
	pub fn eq(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Equal)
			.constant_internal(rhs)
	}

	/// Equate the linear expression to be greater than or equal to the given
	/// value.
	pub fn ge(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::GreaterEqual)
			.constant_internal(rhs)
	}

	/// Equate the linear expression to be greater than the given value.
	pub fn gt(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Greater)
			.constant_internal(rhs)
	}

	/// Require that if the given Boolean view is true that then the linear
	/// constraint is satisfied.
	pub fn implied_by(
		self,
		reif: View<bool>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetReif<S>>
	where
		S::Reif: model_linear_builder::IsUnset,
	{
		self.reif_internal(Reification::ImpliedBy(reif))
	}

	/// Equate the linear expression to be less than or equal to the given
	/// value.
	pub fn le(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::LessEqual)
			.constant_internal(rhs)
	}

	/// Equate the linear expression to be less than the given value.
	pub fn lt(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Less)
			.constant_internal(rhs)
	}

	/// Equate the linear expression to be not equal to the given value.
	pub fn ne(
		self,
		rhs: IntVal,
	) -> ModelLinearBuilder<
		'a,
		model_linear_builder::SetConstant<model_linear_builder::SetComparator<S>>,
	>
	where
		S::Constant: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::NotEqual)
			.constant_internal(rhs)
	}

	/// Require that the given Boolean view is true if-and-only-if the linear
	/// constraint is satisfied.
	pub fn reified_by(
		self,
		reif: View<bool>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetReif<S>>
	where
		S::Reif: model_linear_builder::IsUnset,
	{
		self.reif_internal(Reification::ReifiedBy(reif))
	}

	/// Create a new Boolean decision variable that is defined to be true
	/// if-and-only-if the linear constraint is satisfied.
	pub fn reify(self) -> View<bool>
	where
		S::Reif: model_linear_builder::IsUnset,
		S::Constant: model_linear_builder::IsSet,
		S::Comparator: model_linear_builder::IsSet,
	{
		let res = self.self_receiver.new_bool_decision();
		self.reif_internal(Reification::ReifiedBy(res)).post();
		res
	}
}

impl<I1, S> ModelMaximumBuilder<'_, I1, S>
where
	I1: IntoIterator<Item = View<IntVal>>,
	S: model_maximum_builder::State,
{
	/// Create a new integer decision variable that is defined as the maximum
	/// value in the collection.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_maximum_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision(IntVal::MIN..=IntVal::MAX);
		self.result(res).post();
		res
	}
}

impl<I1, S> ModelMinimumBuilder<'_, I1, S>
where
	I1: IntoIterator<Item = View<IntVal>>,
	S: model_minimum_builder::State,
{
	/// Create a new integer decision variable that is defined as the minimum
	/// value in the collection.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_minimum_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision(IntVal::MIN..=IntVal::MAX);
		self.result(res).post();
		res
	}
}

impl<S: model_mul_builder::State> ModelMulBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// multiplying the two operands.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_mul_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision(IntVal::MIN..=IntVal::MAX);
		self.result(res).post();
		res
	}
}

impl<S: model_pow_builder::State> ModelPowBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// raising the base to the power of the exponent.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_pow_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision(IntVal::MIN..=IntVal::MAX);
		self.result(res).post();
		res
	}
}

impl<'a, S: model_proposition_builder::State> ModelPropositionBuilder<'a, S> {
	/// Require that if the given Boolean view is true that then the linear
	/// constraint is satisfied.
	pub fn implied_by(
		self,
		reif: View<bool>,
	) -> ModelPropositionBuilder<'a, model_proposition_builder::SetReif<S>>
	where
		S::Reif: model_proposition_builder::IsUnset,
	{
		self.reif_internal(Reification::ImpliedBy(reif))
	}

	/// Require that the given Boolean view is true if-and-only-if the linear
	/// constraint is satisfied.
	pub fn reified_by(
		self,
		reif: View<bool>,
	) -> ModelPropositionBuilder<'a, model_proposition_builder::SetReif<S>>
	where
		S::Reif: model_proposition_builder::IsUnset,
	{
		self.reif_internal(Reification::ReifiedBy(reif))
	}

	/// Create a new Boolean decision variable that is defined to be true
	/// if-and-only-if the propositional logic formula is satisfied.
	pub fn reify(self) -> View<bool>
	where
		S::Reif: model_proposition_builder::IsUnset,
	{
		let res = self.self_receiver.new_bool_decision();
		self.reified_by(res).post();
		res
	}
}
