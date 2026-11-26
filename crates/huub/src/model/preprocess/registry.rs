//! The central registry of how the constraints of a [`Model`] are written in
//! the `.fzt` model language.
//!
//! Constraints are written as a single predicate applied to their fields, in
//! the spelling in which Huub receives them from FlatZinc where there is one.
//! They are all listed here, so that the spellings are kept together, and the
//! [`Constraint`] trait does not need to know about the trace.
//!
//! The registry recognizes constraints by their concrete type, so each
//! instantiation of a generic constraint that a [`Model`] can contain is listed
//! separately. A constraint that is not listed here fails the trace with
//! [`FztError::UnsupportedConstraint`]. Every instance of the corpus of the
//! integration tests is run with a trace, so a new constraint that the corpus
//! uses is found by the tests.

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

use pindakaas::constraint::propositional_logic::Formula;

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
		int_linear::{IntEq, IntLinear, LinComparator, Reification},
		int_mul::IntMulBounds,
		int_no_overlap::IntNoOverlapSweep,
		int_pow::IntPowBounds,
		int_set_contains::IntSetContainsReif,
		int_table::IntTable,
		int_unique::IntUnique,
		int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
	},
	helpers::{
		matrix::Matrix,
		overflow::{OverflowImpossible, OverflowPossible},
	},
	model::{
		Model, View,
		expressions::PropositionConstraint,
		preprocess::{FztArg, FztConstraint, FztContext, fzt::FztError, spelling},
		view::boolean::BoolView as ModelBoolView,
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

/// The atoms of `fs`, if all of them are atoms.
fn fzt_atoms(fs: &[Formula<View<bool>>]) -> Option<Vec<View<bool>>> {
	fs.iter()
		.map(|f| match f {
			Formula::Atom(a) => Some(*a),
			_ => None,
		})
		.collect()
}

/// The positive literals and (the negations of) the negative literals of a
/// clause.
fn fzt_clause(ctx: &FztContext<'_>, lits: Vec<View<bool>>) -> (FztArg, FztArg) {
	let (neg, pos): (Vec<_>, Vec<_>) = lits.into_iter().partition(
		|&l| matches!(ctx.resolve_bool(l).0, ModelBoolView::Decision(d) if d.is_negated()),
	);
	(ctx.bools(pos), ctx.bools(neg.into_iter().map(|l| !l)))
}

/// Write `formula` using the FlatZinc spelling of its shape, if it has one of
/// the shapes that Huub receives from FlatZinc.
fn fzt_shape(ctx: &FztContext<'_>, formula: &Formula<View<bool>>) -> Option<FztConstraint> {
	match formula {
		Formula::Or(fs) => {
			let (pos, neg) = fzt_clause(ctx, fzt_atoms(fs)?);
			Some(FztConstraint::new("bool_clause", vec![pos, neg]))
		}
		Formula::Xor(fs) => {
			let lits = fzt_atoms(fs)?;
			Some(match lits.as_slice() {
				&[a, b] => FztConstraint::new("bool_xor", vec![ctx.bool(a), ctx.bool(b)]),
				_ => FztConstraint::new("array_bool_xor", vec![ctx.bools(lits)]),
			})
		}
		Formula::Equiv(fs) => match fs.as_slice() {
			[Formula::Atom(a), Formula::Atom(b)] => Some(FztConstraint::new(
				"bool_eq",
				vec![ctx.bool(*a), ctx.bool(*b)],
			)),
			[Formula::Atom(r), Formula::And(g)] => Some(FztConstraint::new(
				"array_bool_and",
				vec![ctx.bools(fzt_atoms(g)?), ctx.bool(*r)],
			)),
			[Formula::Atom(r), Formula::Or(g)] => {
				let (pos, neg) = fzt_clause(ctx, fzt_atoms(g)?);
				Some(FztConstraint::new(
					spelling::BOOL_CLAUSE_REIF,
					vec![pos, neg, ctx.bool(*r)],
				))
			}
			[Formula::Atom(r), Formula::Equiv(g)] => match fzt_atoms(g)?.as_slice() {
				&[a, b] => Some(FztConstraint::new(
					"bool_eq_reif",
					vec![ctx.bool(a), ctx.bool(b), ctx.bool(*r)],
				)),
				_ => None,
			},
			[Formula::Atom(r), Formula::Xor(g)] => match fzt_atoms(g)?.as_slice() {
				&[a, b] => Some(FztConstraint::new(
					"bool_xor",
					vec![ctx.bool(a), ctx.bool(b), ctx.bool(*r)],
				)),
				_ => None,
			},
			_ => None,
		},
		_ => None,
	}
}

/// The `int_lin_*` constraint over `terms` compared to `rhs`.
fn int_linear(
	ctx: &FztContext<'_>,
	terms: &[IntView],
	rhs: i128,
	comparator: LinComparator,
	reif: Option<Reification>,
) -> FztConstraint {
	let op = match comparator {
		LinComparator::Equal => "eq",
		LinComparator::LessEq => "le",
		LinComparator::NotEqual => "ne",
	};
	let (suffix, reif) = match reif {
		None => ("", None),
		Some(Reification::ImpliedBy(r)) => ("_imp", Some(r)),
		Some(Reification::ReifiedBy(r)) => ("_reif", Some(r)),
	};
	let (coeffs, vars, rhs) = ctx.linear(terms.iter().copied(), rhs);
	let mut args = vec![coeffs, vars, rhs];
	if let Some(r) = reif {
		args.push(ctx.bool(r));
	}
	FztConstraint::new(format!("int_lin_{op}{suffix}"), args)
}

/// The two-dimensional `diffn` constraint, or its `k`-dimensional version.
fn no_overlap<const STRICT: bool>(
	ctx: &FztContext<'_>,
	origin: &Matrix<2, IntView>,
	size: &Matrix<2, IntView>,
) -> FztConstraint {
	let dims = origin.len(1);
	if dims == 2 {
		// Use the spelling of the two-dimensional constraint, which is how it
		// is usually received.
		/// The `d`-th column of `m`.
		fn column(m: &Matrix<2, IntView>, d: usize) -> Vec<IntView> {
			m.row_iter().map(|r| r[d]).collect()
		}
		FztConstraint::new(
			if STRICT {
				spelling::DIFFN_INT
			} else {
				spelling::DIFFN_NONSTRICT_INT
			},
			vec![
				ctx.ints(column(origin, 0)),
				ctx.ints(column(origin, 1)),
				ctx.ints(column(size, 0)),
				ctx.ints(column(size, 1)),
			],
		)
	} else {
		FztConstraint::new(
			if STRICT {
				spelling::DIFFN_K_INT
			} else {
				spelling::DIFFN_NONSTRICT_K_INT
			},
			vec![
				ctx.ints(origin.iter_elem().cloned()),
				ctx.ints(size.iter_elem().cloned()),
				(dims as IntVal).into(),
			],
		)
	}
}

/// The proposition `formula`, in the spelling of its shape if it has one that
/// Huub receives from FlatZinc, and in the encoding of the `huub_formula`
/// predicate otherwise.
fn proposition(ctx: &FztContext<'_>, formula: &Formula<View<bool>>) -> FztConstraint {
	fzt_shape(ctx, formula).unwrap_or_else(|| {
		let (ops, atoms) = ctx.formula_encoding(formula);
		FztConstraint::new(spelling::FORMULA, vec![ops, atoms])
	})
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
		IntLinear<OverflowImpossible> => |x| int_linear(ctx, &x.terms, x.rhs.into(), x.comparator, x.reif),
		IntLinear<OverflowPossible> => |x| int_linear(ctx, &x.terms, x.rhs, x.comparator, x.reif),
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
		IntNoOverlapSweep<true, IntView, IntView> => |x| no_overlap::<true>(ctx, &x.origin, &x.size),
		IntNoOverlapSweep<false, IntView, IntView> => |x| no_overlap::<false>(ctx, &x.origin, &x.size),
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
		PropositionConstraint => |x| proposition(ctx, &x.0),
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

/// Write the constraint `c` in the `.fzt` model language.
pub(crate) fn to_fzt(
	c: &dyn Constraint<Model>,
	ctx: &FztContext<'_>,
) -> Result<FztConstraint, FztError> {
	let any: &dyn Any = c;
	standard(any, ctx).ok_or_else(|| {
		// The name of the type is the start of its `Debug` representation.
		let debug = format!("{c:?}");
		let name = debug
			.split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
			.next()
			.unwrap_or_default();
		FztError::UnsupportedConstraint {
			constraint: name.to_owned(),
		}
	})
}
