//! The central registry of how the constraints of a [`Model`] are written in
//! the `.fzt` model language.
//!
//! Most constraints are written as a single predicate applied to their fields,
//! in the spelling in which Huub receives them from FlatZinc. Those are listed
//! here, so that the spellings are kept together. A constraint whose
//! representation requires more logic implements
//! [`Constraint::to_fzt`](crate::constraints::Constraint::to_fzt) instead.
//!
//! The registry recognizes constraints by their concrete type, so each
//! instantiation of a generic constraint that a [`Model`] can contain is listed
//! separately. A constraint that is neither listed here nor implements
//! [`Constraint::to_fzt`](crate::constraints::Constraint::to_fzt) fails the
//! trace with [`FztError::UnsupportedConstraint`].

/// Try each listed type in turn, returning the representation given by the
/// first one that `$c` is an instance of.
macro_rules! registry {
	($c:expr, { $($ty:ty => |$x:ident| $body:expr),* $(,)? }) => {
		$(
			if let Some($x) = $c.downcast_ref::<$ty>() {
				return Some($body);
			}
		)*
	};
}

use std::any::Any;

use crate::{
	IntVal,
	constraints::{
		Constraint,
		bool_array_element::BoolDecisionArrayElement,
		circuit::Circuit,
		cumulative::Cumulative,
		disjunctive::Disjunctive,
		int_abs::IntAbsBounds,
		int_array_element::{IntArrayElementBounds, IntValArrayElement},
		int_array_minimum::IntArrayMinimumBounds,
		int_div::IntDivBounds,
		int_linear::IntEq,
		int_mul::IntMulBounds,
		int_pow::IntPowBounds,
		int_set_contains::IntSetContainsReif,
		int_table::IntTable,
		int_unique::IntUnique,
		int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
	},
	helpers::overflow::{OverflowImpossible, OverflowPossible},
	model::{
		Model, View,
		preprocess::{FztArg, FztConstraint, FztContext, FztError, spelling},
	},
};

/// An integer view of a [`Model`].
type IntView = View<IntVal>;

/// Create the constraint that applies the predicate `name` to `args`.
fn call(name: &'static str, args: impl Into<Vec<FztArg>>) -> FztConstraint {
	FztConstraint::new(name, args.into())
}

/// Write an array of integer constants.
fn int_vals(vals: impl IntoIterator<Item = IntVal>) -> FztArg {
	FztArg::Array(vals.into_iter().map(FztArg::from).collect())
}

/// The representation of `c` if its type is listed in the registry.
///
/// FlatZinc arrays are indexed from 1, while the element constraints of the
/// model index from 0, so their index is written shifted by one.
fn standard(c: &dyn Any, ctx: &FztContext<'_>) -> Option<FztConstraint> {
	registry!(c, {
		BoolDecisionArrayElement => |x| call("array_var_bool_element", [
			ctx.int(x.index + 1),
			ctx.bools(x.array.iter().copied()),
			ctx.bool(x.result),
		]),
		Circuit<false> => |x| call(spelling::CIRCUIT, [
			ctx.ints(x.graph().vars.iter().copied()),
			x.graph().offset.into(),
		]),
		Circuit<true> => |x| call(spelling::SUBCIRCUIT, [
			ctx.ints(x.graph().vars.iter().copied()),
			x.graph().offset.into(),
		]),
		Cumulative => |x| {
			let p = x.parameters();
			call(spelling::CUMULATIVE, [
				ctx.ints(p.start_times.iter().copied()),
				ctx.ints(p.durations.iter().copied()),
				ctx.ints(p.usages.iter().copied()),
				ctx.int(p.capacity),
			])
		},
		Disjunctive => |x| {
			let p = x.parameters();
			call(spelling::DISJUNCTIVE_STRICT, [
				ctx.ints(p.start_times.iter().copied()),
				int_vals(p.durations.iter().copied()),
			])
		},
		IntAbsBounds<IntView, IntView, View<bool>> => |x| call("int_abs", [
			ctx.int(x.origin),
			ctx.int(x.abs),
		]),
		IntArrayElementBounds<IntView, IntView, IntView> => |x| {
			let p = x.parameters();
			call("array_var_int_element", [
				ctx.int(*p.index + 1),
				ctx.ints(p.collection.iter().copied()),
				ctx.int(*p.result),
			])
		},
		IntArrayMinimumBounds<IntView, IntView> => |x| call(spelling::ARRAY_INT_MINIMUM, [
			ctx.int(x.min),
			ctx.ints(x.vars.iter().copied()),
		]),
		IntDivBounds<IntView, IntView, IntView> => |x| call("int_div", [
			ctx.int(x.numerator),
			ctx.int(x.denominator),
			ctx.int(x.result),
		]),
		IntEq => |x| call("int_eq", [ctx.int(x.vars[0]), ctx.int(x.vars[1])]),
		IntMulBounds<OverflowImpossible, IntView, IntView, IntView> => |x| call("int_times", [
			ctx.int(x.factor1),
			ctx.int(x.factor2),
			ctx.int(x.product),
		]),
		IntMulBounds<OverflowPossible, IntView, IntView, IntView> => |x| call("int_times", [
			ctx.int(x.factor1),
			ctx.int(x.factor2),
			ctx.int(x.product),
		]),
		IntPowBounds<OverflowImpossible, IntView, IntView, IntView> => |x| call("int_pow", [
			ctx.int(x.base),
			ctx.int(x.exponent),
			ctx.int(x.result),
		]),
		IntPowBounds<OverflowPossible, IntView, IntView, IntView> => |x| call("int_pow", [
			ctx.int(x.base),
			ctx.int(x.exponent),
			ctx.int(x.result),
		]),
		IntSeqPrecedeChainBounds<IntView> => |x| call(spelling::SEQ_PRECEDE_CHAIN_INT, [
			ctx.ints(x.vars().iter().copied()),
		]),
		IntSetContainsReif => |x| call("set_in_reif", [
			ctx.int(x.var),
			ctx.set(&x.set),
			ctx.bool(x.reif),
		]),
		IntTable => |x| call(spelling::TABLE_INT, [
			ctx.ints(x.vars.iter().copied()),
			int_vals(x.table.iter().flatten().copied()),
		]),
		IntUnique => |x| call(spelling::ALL_DIFFERENT_INT, [
			ctx.ints(x.vars().iter().copied()),
		]),
		IntValArrayElement<IntView, IntView> => |x| {
			let p = x.0.parameters();
			call("array_int_element", [
				ctx.int(*p.index + 1),
				int_vals(p.collection.iter().copied()),
				ctx.int(*p.result),
			])
		},
		IntValuePrecedeChainValue<IntView> => |x| {
			let p = x.parameters();
			call(spelling::VALUE_PRECEDE_CHAIN_INT, [
				int_vals(p.values.iter().copied()),
				ctx.ints(p.vars.iter().copied()),
			])
		},
	});
	None
}

/// Write the constraint `c` in the `.fzt` model language, using the registry
/// if it lists the type of `c`, and [`Constraint::to_fzt`] otherwise.
pub(crate) fn to_fzt(
	c: &dyn Constraint<Model>,
	ctx: &FztContext<'_>,
) -> Result<FztConstraint, FztError> {
	let any: &dyn Any = c;
	match standard(any, ctx) {
		Some(item) => Ok(item),
		None => c.to_fzt(ctx),
	}
}
