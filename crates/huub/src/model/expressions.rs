//! Helper types and builder methods used to create constraints for a
//! [`Model`].
//!
//! Most modelling methods return a builder. Call `.post()` to add the completed
//! constraint to the model, or use a `.define()` or `.reify()` helper when the
//! builder supports creating the result decision variable for you.

pub(crate) mod bool_formula;
pub(crate) mod element;
pub(crate) mod linear;

use std::{cmp, marker::PhantomData, num::NonZero};

use bon::bon;
use itertools::{Itertools, MinMaxResult, iproduct};
use rangelist::RangeList;

pub use crate::model::expressions::{
	bool_formula::BoolFormula, element::ElementConstraint, linear::IntLinearExp,
};
use crate::{
	IntSet, IntVal,
	actions::{
		BoolPropagationActions, IntInspectionActions, IntPropagationActions,
		IntSimplificationActions,
	},
	constraints::{
		NO_REASON, Nogood,
		circuit::Circuit,
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
		int_unique::{IntUnique, IntUniqueBounds, IntUniqueValue},
		int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
	},
	helpers::overflow::{OverflowImpossible, OverflowPossible},
	model::{Model, View, expressions::linear::Comparator, view::integer::IntView},
};

#[bon]
impl Model {
	/// Create a constraint that enforces that the second integer decision
	/// decision variable takes the absolute value of the first integer decision
	/// decision variable.
	#[builder(finish_fn = post)]
	pub fn abs(
		&mut self,
		#[builder(into, start_fn)] origin: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		self.post_constraint(IntAbsBounds {
			origin,
			abs: result,
			origin_positive: origin.geq(0),
		})
	}

	/// Create a `circuit` constraint that enforces that the values of the given
	/// successor decisions form a single simple cycle.
	///
	/// With `subcircuit` set (the `subcircuit` variant), every node not on the
	/// cycle takes itself as successor (a self-loop) instead of every node
	/// having to lie on a single Hamiltonian cycle.
	#[builder(finish_fn = post)]
	pub fn circuit(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(default = 1)] offset: IntVal,
		#[builder(default = false)] subcircuit: bool,
		no_cycle_propagation: Option<bool>,
		scc_propagation: Option<bool>,
	) -> Result<(), Nogood<View<bool>>> {
		let vars: Vec<View<IntVal>> = vars.into_iter().map_into().collect();
		match vars[..] {
			[x] => return x.fix(self, offset, NO_REASON),
			[] => return Ok(()),
			_ => {}
		}
		// Post a model-level `IntUnique` since all successor values must be distinct
		// (a permutation for `circuit`, a partial permutation for `subcircuit`).
		self.post_constraint(IntUnique {
			bounds_prop: IntUniqueBounds::new(vars.clone()),
			value_prop: IntUniqueValue::new(vars.clone()),
			bounds_propagation: Some(false),
			value_propagation: Some(false),
			domain_propagation: Some(true),
		})?;
		if subcircuit {
			self.post_constraint(Circuit::<true>::new(
				vars,
				offset,
				no_cycle_propagation,
				scc_propagation,
			))
		} else {
			self.post_constraint(Circuit::<false>::new(
				vars,
				offset,
				no_cycle_propagation,
				scc_propagation,
			))
		}
	}

	/// Create constraint that enforces that the given Boolean decision variable
	/// takes the value `true` if-and-only-if an integer decision variable is in
	/// a given set.
	#[builder(finish_fn = post)]
	pub fn contains(
		&mut self,
		#[builder(start_fn, into)] collection: IntSet,
		#[builder(into)] member: View<IntVal>,
		#[builder(into)] result: View<bool>,
	) -> Result<(), Nogood<View<bool>>> {
		self.post_constraint(IntSetContainsReif {
			var: member,
			set: collection,
			reif: result,
		})
	}

	/// Create a constraint that enforces that the given a list of integer
	/// decision variables representing the start times of tasks, a list of
	/// integer values representing the durations of tasks, a list of integer
	/// values representing the resource usages of tasks, and a resource
	/// capacity, the sum of the resource usages of all tasks running at any
	/// time does not exceed the resource capacity.
	#[builder(finish_fn = post)]
	pub fn cumulative(
		&mut self,
		start_times: Vec<impl Into<View<IntVal>>>,
		durations: Vec<impl Into<View<IntVal>>>,
		usages: Vec<impl Into<View<IntVal>>>,
		capacity: impl Into<View<IntVal>>,
	) -> Result<(), Nogood<View<bool>>> {
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
		))
	}

	/// Create a constraint that enforces that the given a list of integer
	/// decision variables representing the start times of tasks and a list of
	/// integer values representing the durations of tasks, the tasks do not
	/// overlap in time.
	///
	/// Note that this constraint is strict, meaning that tasks with a zero
	/// duration cannot occur during another task.
	#[builder(finish_fn = post)]
	pub fn disjunctive(
		&mut self,
		start_times: Vec<View<IntVal>>,
		durations: Vec<IntVal>,
		edge_finding_propagation: Option<bool>,
		not_last_propagation: Option<bool>,
		detectable_precedence_propagation: Option<bool>,
	) -> Result<(), Nogood<View<bool>>> {
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
		})
	}

	/// Create a constraint that enforces that a numerator integer decision
	/// variable divided by a denominator integer decision variable is equal to
	/// a result integer decision variable.
	#[builder(finish_fn = post)]
	pub fn div(
		&mut self,
		#[builder(into, start_fn)] numerator: View<IntVal>,
		#[builder(into, start_fn)] denominator: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		self.post_constraint(IntDivBounds {
			numerator,
			denominator,
			result,
		})
	}

	/// Create a constraint that enforces that a result decision variable takes
	/// the value equal the element of the given array at the given index
	/// decision variable.
	#[builder(finish_fn = post)]
	pub fn element<E: ElementConstraint>(
		&mut self,
		#[builder(start_fn)] array: Vec<E>,
		#[builder(getter(name = index_internal, vis = ""), into)] index: View<IntVal>,
		result: <E as ElementConstraint>::Result,
	) -> Result<(), Nogood<View<bool>>> {
		<E as ElementConstraint>::element_constraint(self, array, index, result)
	}

	/// Create a linear equation constraint.
	///
	/// Linear expressions can be built with ordinary arithmetic on integer
	/// views and constants. The builder is completed with a comparator such as
	/// [`ModelLinearBuilder::eq`], [`ModelLinearBuilder::le`], or
	/// [`ModelLinearBuilder::ge`], and then posted.
	///
	/// # Warning
	///
	/// Each term in the linear expression is required to fit within `i64` after
	/// its coefficient is applied. To guarantee this, the domain of any
	/// variable whose scaled value would overflow `i64` is tightened
	/// automatically when the constraint is posted (using
	/// [`View::bounding_mul`]). This is a current limitation of the
	/// implementation: variables with extreme domains (e.g. an unbounded `var
	/// int` with minimum `i64::MIN` that appears with a negative coefficient)
	/// will have their domains silently narrowed.
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Status, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// let x = model.new_int_decision(0..=10);
	/// let y = model.new_int_decision(0..=10);
	///
	/// model.linear(x * 2 + y).eq(7).post();
	/// # let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// # let x = map.get(&mut solver, x);
	/// # let y = map.get(&mut solver, y);
	/// # let status = solver
	/// # 	.solve()
	/// # 	.on_solution(|solution| {
	/// # 		assert_eq!(x.val(solution) * 2 + y.val(solution), 7);
	/// # 	})
	/// # 	.satisfy();
	/// # assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	#[builder(finish_fn = post)]
	pub fn linear(
		&mut self,
		#[builder(start_fn, into)] mut expr: IntLinearExp,
		#[builder(setters(name = comparator_internal, vis = ""))] comparator: Comparator,
		#[builder(setters(name = rhs_internal, vis = ""))] rhs: IntLinearExp,
		#[builder(setters(name = reif_internal, vis = ""))] reif: Option<Reification>,
	) -> Result<(), Nogood<View<bool>>> {
		// Subtract the RHS from the LHS to get a linear expression with a constant 0 on
		// the RHS
		expr -= rhs;

		// Move the constant offset to the RHS
		let rhs = -expr.offset;
		// Collect the terms as a vector of `View<IntVal>`
		let mut terms: Vec<View<IntVal>> = Vec::with_capacity(expr.terms.len());
		for (&v, &k) in expr.terms.iter() {
			match v.0 {
				IntView::Const(_) => debug_assert!(false),
				IntView::Linear(lin) => {
					debug_assert_eq!(lin.scale, NonZero::new(1).unwrap());
					debug_assert_eq!(lin.offset, 0);
				}
				IntView::Bool(lin) => {
					debug_assert_eq!(lin.scale, NonZero::new(1).unwrap());
					debug_assert_eq!(lin.offset, 0);
				}
			}
			terms.push(v.bounding_mul(self, k)?);
		}

		if terms.is_empty() {
			// All variable terms cancelled out, so the constraint reduces to a
			// comparison between the constant `0` and the (constant) `rhs`. Evaluate
			// it directly, then either enforce it or fix the reification literal.
			let satisfied = match comparator {
				Comparator::NotEqual => 0 != rhs,
				Comparator::Equal => 0 == rhs,
				Comparator::Less => 0 < rhs,
				Comparator::LessEqual => 0 <= rhs,
				Comparator::GreaterEqual => 0 >= rhs,
				Comparator::Greater => 0 > rhs,
			};
			return match reif {
				None => satisfied.require(self, NO_REASON),
				Some(Reification::ReifiedBy(r)) => r.fix(self, satisfied, NO_REASON),
				Some(Reification::ImpliedBy(_)) if satisfied => Ok(()),
				Some(Reification::ImpliedBy(r)) => r.fix(self, false, NO_REASON),
			};
		}

		let mut negate_terms = || -> Result<(), Nogood<View<bool>>> {
			for v in &mut terms {
				*v = v.bounding_neg(self)?;
			}
			Ok(())
		};
		let (comparator, rhs) = match comparator {
			Comparator::Less => (LinComparator::LessEq, rhs - 1),
			Comparator::LessEqual => (LinComparator::LessEq, rhs),
			Comparator::Equal => (LinComparator::Equal, rhs),
			Comparator::GreaterEqual => {
				negate_terms()?;
				(LinComparator::LessEq, -rhs)
			}
			Comparator::Greater => {
				negate_terms()?;
				(LinComparator::LessEq, -rhs - 1)
			}
			Comparator::NotEqual => (LinComparator::NotEqual, rhs),
		};

		if IntLinear::can_overflow(self, &terms) {
			self.post_constraint(IntLinear::<OverflowPossible> {
				terms,
				rhs: rhs.into(),
				reif,
				comparator,
			})
		} else {
			self.post_constraint(IntLinear::<OverflowImpossible> {
				terms,
				rhs,
				reif,
				comparator,
			})
		}
	}

	/// Create a constraint that enforces that an integer decision variable
	/// takes the minimum value of an array of integer decision variables.
	#[builder(finish_fn = post)]
	pub fn maximum(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(into)] result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		self.minimum(vars.into_iter().map(|v| -v))
			.result(-result)
			.post()
	}

	/// Create a constraint that enforces that an integer decision variable
	/// takes the minimum value of an array of integer decision variables.
	#[builder(finish_fn = post)]
	pub fn minimum(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(into)] result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		self.post_constraint(IntArrayMinimumBounds {
			vars: vars.into_iter().collect(),
			min: result,
		})
	}

	/// Create a constraint that enforces that the product of the two integer
	/// decision variables is equal to a third.
	#[builder(finish_fn = post)]
	pub fn mul(
		&mut self,
		#[builder(start_fn)] factor1: View<IntVal>,
		#[builder(start_fn)] factor2: View<IntVal>,
		result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		if IntMulBounds::<_, _, _, View<IntVal>>::can_overflow(self, &factor1, &factor2) {
			self.post_constraint(IntMulBounds::<OverflowPossible, _, _, _> {
				factor1,
				factor2,
				product: result,
				overflow_mode: PhantomData,
			})
		} else {
			self.post_constraint(IntMulBounds::<OverflowImpossible, _, _, _> {
				factor1,
				factor2,
				product: result,
				overflow_mode: PhantomData,
			})
		}
	}

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
	#[builder(finish_fn = post)]
	pub fn no_overlap(
		&mut self,
		origins: Vec<Vec<View<IntVal>>>,
		sizes: Vec<Vec<View<IntVal>>>,
		#[builder(default = true)] strict: bool,
	) -> Result<(), Nogood<View<bool>>> {
		if strict {
			let prop = IntNoOverlapSweep::<true, _, _>::new(self, origins, sizes);
			self.post_constraint(prop)
		} else {
			let prop = IntNoOverlapSweep::<false, _, _>::new(self, origins, sizes);
			self.post_constraint(prop)
		}
	}

	/// Create a constraint that enforces that a base integer decision variable
	/// exponentiation by an exponent integer decision variable is equal to a
	/// result integer decision variable.
	#[builder(finish_fn = post)]
	pub fn pow(
		&mut self,
		#[builder(start_fn, into)] base: View<IntVal>,
		#[builder(start_fn, into)] exponent: View<IntVal>,
		#[builder(into)] result: View<IntVal>,
	) -> Result<(), Nogood<View<bool>>> {
		if IntPowBounds::<_, _, _, View<IntVal>>::can_overflow(self, &base, &exponent) {
			self.post_constraint(IntPowBounds::<OverflowPossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			})
		} else {
			self.post_constraint(IntPowBounds::<OverflowImpossible, _, _, _> {
				base,
				exponent,
				result,
				overflow_mode: PhantomData,
			})
		}
	}

	/// Create a constraint that enforces that a propositional logic formula is
	/// true.
	#[builder(finish_fn = post)]
	pub fn proposition(
		&mut self,
		#[builder(start_fn, into)] mut formula: BoolFormula,
		#[builder(setters(name = reif_internal, vis = ""))] reif: Option<Reification>,
	) -> Result<(), Nogood<View<bool>>> {
		match reif {
			Some(Reification::ReifiedBy(b)) => {
				formula = BoolFormula::Equiv(vec![BoolFormula::Atom(b), formula]);
			}
			Some(Reification::ImpliedBy(b)) => {
				formula = BoolFormula::Implies(BoolFormula::Atom(b).into(), formula.into());
			}
			None => {}
		}
		self.post_constraint(formula)
	}

	/// Create a `table` constraint that enforces that given list of integer
	/// views take their values according to one of the given lists of integer
	/// values.
	#[builder(finish_fn = post)]
	pub fn table(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		values: impl IntoIterator<Item = Vec<IntVal>>,
	) -> Result<(), Nogood<View<bool>>> {
		let vars: Vec<_> = vars.into_iter().collect();
		let table: Vec<_> = values.into_iter().collect();
		assert!(
			table.iter().all(|tup| tup.len() == vars.len()),
			"The number of values in each row of the table must be equal to the number of decision variables."
		);
		self.post_constraint(IntTable { vars, table })
	}

	/// Create a constraint that enforces that all the given integer decisions
	/// take different values.
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Status, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// let x = model.new_int_decisions(3, 1..=3);
	/// # let x_clone = x.clone();
	/// model.unique(x).post();
	/// # let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// # let &[x, y, z] = x_clone
	/// # 	.into_iter()
	/// # 	.map(|var| map.get(&mut solver, var))
	/// # 	.collect::<Vec<_>>()
	/// # 	.as_slice()
	/// # else {
	/// # 	unreachable!()
	/// # };
	/// # let status = solver
	/// # 	.solve()
	/// # 	.on_solution(|solution| {
	/// # 		let values = [x.val(solution), y.val(solution), z.val(solution)];
	/// # 		assert_eq!(values.iter().sum::<i64>(), 6);
	/// # 	})
	/// # 	.satisfy();
	/// # assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	#[builder(finish_fn = post)]
	pub fn unique(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		bounds_propagation: Option<bool>,
		value_propagation: Option<bool>,
		domain_propagation: Option<bool>,
	) -> Result<(), Nogood<View<bool>>> {
		let vars: Vec<_> = vars.into_iter().map_into().collect();
		self.post_constraint(IntUnique {
			bounds_prop: IntUniqueBounds::new(vars.clone()),
			value_prop: IntUniqueValue::new(vars),
			bounds_propagation,
			value_propagation,
			domain_propagation,
		})
	}

	/// Create a value precede (chain) constraint that enforces that the first
	/// occurrence of each value in `values` among the decisions `vars` happens
	/// in the order of `values`.
	///
	/// If no values are explicitly provided, then the values are assumed to be
	/// consecutive integers starting from 1. This variant of the constraint is
	/// sometimes referred to as a sequential precede chain constraint.
	#[builder(finish_fn = post)]
	pub fn value_precede(
		&mut self,
		#[builder(start_fn)] vars: impl IntoIterator<Item = View<IntVal>>,
		#[builder(with = |values: impl IntoIterator<Item = IntVal>| values.into_iter().collect())]
		values: Option<Vec<IntVal>>,
	) -> Result<(), Nogood<View<bool>>> {
		let mut offset = 0;
		let vars: Vec<_> = vars.into_iter().collect();
		// If there are no decision variables, then the constraint is trivially
		// satisfied.
		if vars.is_empty() {
			return Ok(());
		}
		if let Some(values) = values {
			// If the list of values doesn't contain at least two values, then the
			// constraint is trivially satisfied.
			if values.len() <= 1 {
				return Ok(());
			}
			// If the values are not consecutive or if the largest value does not cover the
			// full decision variable domain, then we need the general value
			// precede chain constraint that tracks the explicit values.
			if !values.iter().tuple_windows().all(|(&x, &y)| x + 1 == y)
				|| *values.last().unwrap() < vars.iter().map(|v| v.max(self)).max().unwrap()
			{
				vars[0].exclude(self, &RangeList::from_elements(values.clone()), NO_REASON)?;

				let con = IntValuePrecedeChainValue::new(self, values.into_iter().collect(), vars);
				return self.post_constraint(con);
			}
			// Otherwise this is a sequential precede chain constraint, and we can
			// normalize it to start at 1. The `values` array might not have started
			// at 1, calculate the offset to subtract from the decision variables.
			offset = values[0] - 1;
		}

		let vars = vars
			.into_iter()
			.map(|v| v.bounding_sub(self, offset))
			.collect::<Result<Vec<_>, _>>()?;
		vars[0].tighten_max(self, 1, NO_REASON)?;
		match vars.len() {
			1 => Ok(()),
			_ => {
				let con = IntSeqPrecedeChainBounds::new(self, vars);
				self.post_constraint(con)
			}
		}
	}
}

impl<S: model_abs_builder::State> ModelAbsBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the absolute
	/// value of the given integer decision variable.
	pub fn define(self) -> View<IntVal>
	where
		S::Result: model_abs_builder::IsUnset,
	{
		let (min, max) = self.origin.bounds(self.self_receiver);
		let res = self
			.self_receiver
			.new_int_decision(0..=cmp::max(min.abs(), max.abs()));
		self.result(res).post().unwrap();
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
		self.result(res).post().unwrap();
		res
	}
}

impl<S: model_div_builder::State> ModelDivBuilder<'_, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// the division of the given two integer decision variables.
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
		self.result(res).post().unwrap();
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
		self.result(res.clone()).post().unwrap();
		res
	}
}

impl<'a, S: model_linear_builder::State> ModelLinearBuilder<'a, S> {
	/// Create a new integer decision variable that is defined as the result of
	/// the linear expression.
	pub fn define(self) -> View<IntVal>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Reif: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		let res = self
			.self_receiver
			.new_int_decision((IntVal::MIN + 1)..=IntVal::MAX);
		self.comparator_internal(Comparator::Equal)
			.rhs_internal(res.into())
			.post()
			.unwrap();
		res
	}

	/// Equate the linear expression to be equal to the given value.
	pub fn eq(
		self,
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Equal)
			.rhs_internal(rhs.into())
	}

	/// Equate the linear expression to be greater than or equal to the given
	/// value.
	pub fn ge(
		self,
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::GreaterEqual)
			.rhs_internal(rhs.into())
	}

	/// Equate the linear expression to be greater than the given value.
	pub fn gt(
		self,
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Greater)
			.rhs_internal(rhs.into())
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
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::LessEqual)
			.rhs_internal(rhs.into())
	}

	/// Equate the linear expression to be less than the given value.
	pub fn lt(
		self,
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::Less)
			.rhs_internal(rhs.into())
	}

	/// Equate the linear expression to be not equal to the given value.
	pub fn ne(
		self,
		rhs: impl Into<IntLinearExp>,
	) -> ModelLinearBuilder<'a, model_linear_builder::SetRhs<model_linear_builder::SetComparator<S>>>
	where
		S::Rhs: model_linear_builder::IsUnset,
		S::Comparator: model_linear_builder::IsUnset,
	{
		self.comparator_internal(Comparator::NotEqual)
			.rhs_internal(rhs.into())
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
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Status, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// let x = model.new_int_decision(0..=5);
	/// let y = model.new_int_decision(0..=5);
	///
	/// let at_least_three = model.linear(x - y).ge(3).reify();
	///
	/// # model.proposition(at_least_three).post();
	/// # let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// # let x = map.get(&mut solver, x);
	/// # let at_least_three = map.get(&mut solver, at_least_three);
	/// # let status = solver
	/// # 	.solve()
	/// # 	.on_solution(|solution| {
	/// # 		assert!(at_least_three.val(solution));
	/// # 		assert!(x.val(solution) >= 3);
	/// # 	})
	/// # 	.satisfy();
	/// # assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn reify(self) -> View<bool>
	where
		S::Reif: model_linear_builder::IsUnset,
		S::Rhs: model_linear_builder::IsSet,
		S::Comparator: model_linear_builder::IsSet,
	{
		let res = self.self_receiver.new_bool_decision();
		self.reif_internal(Reification::ReifiedBy(res))
			.post()
			.unwrap();
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
		self.result(res).post().unwrap();
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
		self.result(res).post().unwrap();
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
		self.result(res).post().unwrap();
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
		self.result(res).post().unwrap();
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
		self.reified_by(res).post().unwrap();
		res
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;

	use crate::model::Model;

	#[test]
	fn test_empty_linear_implied_false() {
		// `0 == 5` is false, so the half-reification literal `r` must be fixed to
		// false (the model stays satisfiable).
		let mut prb = Model::default();
		let x = prb.new_int_decision(1..=5);
		let r = prb.new_bool_decision();
		prb.linear(x - x).eq(5).implied_by(r).post().unwrap();
		prb.expect_solutions(&[r], expect!["false"]);
	}

	#[test]
	fn test_empty_linear_reified_false() {
		// `0 == 5` is false, so the reification literal `r` must be fixed to false
		// and the model must remain satisfiable.
		let mut prb = Model::default();
		let x = prb.new_int_decision(1..=5);
		let r = prb.new_bool_decision();
		prb.linear(x - x).eq(5).reified_by(r).post().unwrap();
		prb.expect_solutions(&[r], expect!["false"]);
	}

	#[test]
	fn test_empty_linear_reified_true() {
		// `0 == 0` is true, so the reification literal `r` must be fixed to true.
		let mut prb = Model::default();
		let x = prb.new_int_decision(1..=5);
		let r = prb.new_bool_decision();
		prb.linear(x - x).eq(0).reified_by(r).post().unwrap();
		prb.expect_solutions(&[r], expect!["true"]);
	}
}
