//! Helper trait that allows the definition of [`Model`] level array element
//! constraints in a more generic way.

use itertools::{Itertools, MinMaxResult};
use rangelist::RangeList;

use crate::{
	IntVal,
	actions::IntInspectionActions,
	constraints::{
		bool_array_element::BoolDecisionArrayElement,
		int_array_element::{IntArrayElementBounds, IntValArrayElement},
		int_set_contains::IntSetContainsReif,
	},
	model::{Model, view::View},
};

/// Helper trait used to create array element constraints for on collections of
/// different types.
pub trait ElementConstraint: Sized {
	/// The constraint type created and to be added to a [`Model`].
	type Constraint;
	/// The decision variable type to contain the selected element.
	type Result: Clone;

	/// Create a new decision variable that can contain the resulting element of
	/// the element constraint.
	fn define_result(prb: &mut Model, array: &[Self], index: View<IntVal>) -> Self::Result;

	/// Create and post a constraint that enforces that the `result` decision
	/// variables takes the same value as `array[index]`.
	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: View<IntVal>,
		result: Self::Result,
	);
}

impl ElementConstraint for IntVal {
	type Constraint = IntValArrayElement<View<IntVal>, View<IntVal>>;
	type Result = View<IntVal>;

	fn define_result(prb: &mut Model, array: &[Self], _: View<IntVal>) -> Self::Result {
		let range = match array.iter().minmax() {
			MinMaxResult::NoElements => IntVal::MIN..=IntVal::MAX,
			MinMaxResult::OneElement(&v) => v..=v,
			MinMaxResult::MinMax(&min, &max) => min..=max,
		};
		prb.new_int_decision(range)
	}

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: View<IntVal>,
		result: Self::Result,
	) {
		let con = IntValArrayElement(IntArrayElementBounds::new(prb, array, index, result));
		prb.post_constraint(con);
	}
}

impl ElementConstraint for View<IntVal> {
	type Constraint = IntArrayElementBounds<View<IntVal>, View<IntVal>, View<IntVal>>;
	type Result = View<IntVal>;

	fn define_result(prb: &mut Model, array: &[Self], _: View<IntVal>) -> Self::Result {
		let min = array
			.iter()
			.map(|v| v.min(prb))
			.min()
			.unwrap_or(IntVal::MIN);
		let max = array
			.iter()
			.map(|v| v.max(prb))
			.max()
			.unwrap_or(IntVal::MAX);
		prb.new_int_decision(min..=max)
	}

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: View<IntVal>,
		result: Self::Result,
	) {
		let con = IntArrayElementBounds::new(prb, array, index, result);
		prb.post_constraint(con);
	}
}

impl ElementConstraint for View<bool> {
	type Constraint = BoolDecisionArrayElement;
	type Result = View<bool>;

	fn define_result(prb: &mut Model, _: &[Self], _: View<IntVal>) -> Self::Result {
		prb.new_bool_decision()
	}

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: View<IntVal>,
		result: Self::Result,
	) {
		prb.post_constraint(Self::Constraint {
			index,
			array,
			result,
		});
	}
}

impl ElementConstraint for bool {
	type Constraint = IntSetContainsReif;
	type Result = View<bool>;

	fn define_result(prb: &mut Model, _: &[Self], _: View<IntVal>) -> Self::Result {
		prb.new_bool_decision()
	}

	fn element_constraint(
		prb: &mut Model,
		array: Vec<Self>,
		index: View<IntVal>,
		result: Self::Result,
	) {
		// Convert array of boolean values to a set literals of the indices where
		// the value is true
		let mut ranges = Vec::new();
		let mut start = None;
		for (i, b) in array.iter().enumerate() {
			match (b, start) {
				(true, None) => start = Some(i as IntVal),
				(false, Some(s)) => {
					ranges.push(s..=(i - 1) as IntVal);
					start = None;
				}
				(false, None) | (true, Some(_)) => {}
			}
		}
		if let Some(s) = start {
			ranges.push(s..=array.len() as IntVal);
		}
		assert_ne!(ranges.len(), 0, "unexpected empty range list");

		prb.post_constraint(Self::Constraint {
			var: index,
			set: RangeList::from_iter(ranges),
			reif: result,
		});
	}
}
