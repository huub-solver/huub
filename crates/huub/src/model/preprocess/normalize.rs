//! The normalization of `.fzt` constraints, used to check the claims of
//! tailored rules before they are made.
//!
//! The normal form follows the checker's normal form `N` of linear constraints:
//! terms are expanded into atoms, merged, and folded into the right-hand side,
//! a constant reification is folded, and the sign of an (in)equality is fixed.
//! There is no gcd step, since the checker has none either.

use std::collections::BTreeMap;

use crate::model::preprocess::fzt::{FztArg, FztConstraint};

/// The linear normal form of a linear constraint in the `.fzt` model language.
#[derive(Debug, Eq, PartialEq)]
pub(super) enum LinForm {
	/// `terms op rhs`, reified by the given literal, if any.
	Lin {
		/// The comparison between the sum of the terms and the right-hand side.
		op: LinOp,
		/// The (non-zero) coefficient of each atom.
		terms: BTreeMap<String, i128>,
		/// The right-hand side.
		rhs: i128,
		/// The reification of the constraint and its literal, if any.
		reif: Option<(Reification, String)>,
	},
	/// A constraint that cannot hold.
	Unsat,
	/// A constraint that always holds.
	Valid,
}

/// The comparison of a linear constraint between the sum of its terms and its
/// right-hand side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LinOp {
	/// The sum is equal to the right-hand side (`int_lin_eq`).
	Eq,
	/// The sum is at most the right-hand side (`int_lin_le`).
	Le,
	/// The sum differs from the right-hand side (`int_lin_ne`).
	Ne,
}

/// How a linear constraint is reified by a literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Reification {
	/// The literal holds if and only if the constraint holds (`_reif`).
	Full,
	/// The constraint holds if the literal holds (`_imp`).
	Half,
}

/// Split a term written by
/// [`affine`](crate::model::preprocess::fzt::affine) into `(c, atom, a)` such
/// that the term is `c*atom + a`, where a negated Boolean atom `!b` is read as
/// `1 - b`.
pub(super) fn affine_parts(term: &str) -> (i128, String, i128) {
	// A literal view contains spaces of its own, so only a trailing ` + a` or
	// ` - a` with an integer `a` is an offset.
	let offset = term.rsplit_once(' ').and_then(|(rest, a)| {
		let a = a.parse::<i128>().ok()?;
		rest.strip_suffix(" +")
			.map(|b| (b, a))
			.or_else(|| rest.strip_suffix(" -").map(|b| (b, -a)))
	});
	let (body, offset) = offset.unwrap_or((term, 0));
	let (scale, atom) = match body.split_once('*') {
		Some((c, atom)) if c.parse::<i128>().is_ok() => (c.parse().unwrap(), atom),
		_ => match body.strip_prefix('-') {
			Some(atom) => (-1, atom),
			None => (1, body),
		},
	};
	match atom.strip_prefix('!') {
		Some(b) => (-scale, b.to_owned(), offset + scale),
		None => (scale, atom.to_owned(), offset),
	}
}

/// The linear normal form of `c`, if it is an `int_lin_*` constraint.
pub(super) fn lin_form(c: &FztConstraint) -> Option<LinForm> {
	let rest = c.name().strip_prefix("int_lin_")?;
	let (op, suffix) = [("le", LinOp::Le), ("eq", LinOp::Eq), ("ne", LinOp::Ne)]
		.into_iter()
		.find_map(|(name, op)| Some((op, rest.strip_prefix(name)?)))?;
	let reif_kind = match suffix {
		"" => None,
		"_reif" => Some(Reification::Full),
		"_imp" => Some(Reification::Half),
		_ => return None,
	};
	let (coeffs, vars, rhs, reif) = match (c.args.as_slice(), reif_kind) {
		([FztArg::Array(c), FztArg::Array(v), FztArg::Int(r)], None) => (c, v, *r, None),
		([FztArg::Array(c), FztArg::Array(v), FztArg::Int(r), b], Some(kind)) => {
			(c, v, *r, Some((kind, b)))
		}
		_ => return None,
	};
	if coeffs.len() != vars.len() {
		return None;
	}
	let mut terms = BTreeMap::new();
	let mut rhs = rhs;
	for (c, v) in coeffs.iter().zip(vars) {
		let FztArg::Int(c) = c else { return None };
		match v {
			FztArg::Term(t) => {
				let (scale, atom, offset) = affine_parts(&t.0);
				*terms.entry(atom).or_insert(0) += c * scale;
				rhs -= c * offset;
			}
			FztArg::Int(k) => rhs -= c * k,
			FztArg::Bool(b) => rhs -= c * i128::from(*b),
			FztArg::Array(_) | FztArg::Set(_) => return None,
		}
	}
	terms.retain(|_, c| *c != 0);

	let mut op = op;
	let reif = match reif {
		None | Some((_, FztArg::Bool(true))) => None,
		Some((Reification::Half, FztArg::Bool(false))) => return Some(LinForm::Valid),
		Some((Reification::Full, FztArg::Bool(false))) => {
			// The negation of the body.
			match op {
				LinOp::Le => {
					terms.values_mut().for_each(|c| *c = -*c);
					rhs = -rhs - 1;
				}
				LinOp::Eq => op = LinOp::Ne,
				LinOp::Ne => op = LinOp::Eq,
			}
			None
		}
		Some((kind, FztArg::Term(t))) => Some((kind, t.0.clone())),
		Some((_, FztArg::Int(_) | FztArg::Array(_) | FztArg::Set(_))) => return None,
	};

	if terms.is_empty() && reif.is_none() {
		let holds = match op {
			LinOp::Le => 0 <= rhs,
			LinOp::Eq => 0 == rhs,
			LinOp::Ne => 0 != rhs,
		};
		return Some(if holds {
			LinForm::Valid
		} else {
			LinForm::Unsat
		});
	}
	if op != LinOp::Le && terms.values().next().is_some_and(|c| *c < 0) {
		terms.values_mut().for_each(|c| *c = -*c);
		rhs = -rhs;
	}
	Some(LinForm::Lin {
		op,
		terms,
		rhs,
		reif,
	})
}

/// Whether the linear constraints `a` and `b` have the same linear normal form,
/// or `None` if either is not a linear constraint.
pub(crate) fn lin_norm_equal(a: &FztConstraint, b: &FztConstraint) -> Option<bool> {
	Some(lin_form(a)? == lin_form(b)?)
}

#[cfg(test)]
mod tests {
	use crate::model::preprocess::{
		fzt::{FztArg, FztConstraint, FztTerm},
		normalize::{LinForm, affine_parts, lin_form, lin_norm_equal},
	};

	/// An argument of a linear constraint: an integer constant, or a term.
	enum Arg {
		/// An integer constant.
		Int(i128),
		/// A term, as written by the trace.
		Term(&'static str),
	}

	#[test]
	fn affine_parts_of_terms() {
		assert_eq!(affine_parts("x"), (1, "x".to_owned(), 0));
		assert_eq!(affine_parts("-x"), (-1, "x".to_owned(), 0));
		assert_eq!(affine_parts("3*x + 1"), (3, "x".to_owned(), 1));
		assert_eq!(affine_parts("-2*y - 4"), (-2, "y".to_owned(), -4));
		// A negated Boolean is `1 - b`.
		assert_eq!(affine_parts("1*!b"), (-1, "b".to_owned(), 1));
		assert_eq!(affine_parts("2*!b + 3"), (-2, "b".to_owned(), 5));
		// The spaces and signs of a literal view are part of the atom.
		assert_eq!(affine_parts("[x >= -3]"), (1, "[x >= -3]".to_owned(), 0));
		assert_eq!(
			affine_parts("2*[x <= 3] + 5"),
			(2, "[x <= 3]".to_owned(), 5)
		);
	}

	#[test]
	fn constant_reification_is_folded() {
		let body = lin("int_lin_le", &[1, 1], vec![t("x"), t("y")], 3, None);
		// A true literal leaves the body.
		let reif_true = lin(
			"int_lin_le_reif",
			&[1, 1],
			vec![t("x"), t("y")],
			3,
			Some(FztArg::Bool(true)),
		);
		let imp_true = lin(
			"int_lin_le_imp",
			&[1, 1],
			vec![t("x"), t("y")],
			3,
			Some(FztArg::Bool(true)),
		);
		assert_eq!(lin_norm_equal(&reif_true, &body), Some(true));
		assert_eq!(lin_norm_equal(&imp_true, &body), Some(true));
		// A false full reification negates the body: `-x - y <= -4`.
		let reif_false = lin(
			"int_lin_le_reif",
			&[1, 1],
			vec![t("x"), t("y")],
			3,
			Some(FztArg::Bool(false)),
		);
		let negated = lin("int_lin_le", &[-1, -1], vec![t("x"), t("y")], -4, None);
		assert_eq!(lin_norm_equal(&reif_false, &negated), Some(true));
		let eq_false = lin(
			"int_lin_eq_reif",
			&[1],
			vec![t("x")],
			3,
			Some(FztArg::Bool(false)),
		);
		let ne = lin("int_lin_ne", &[1], vec![t("x")], 3, None);
		assert_eq!(lin_norm_equal(&eq_false, &ne), Some(true));
		// A false half reification always holds.
		let imp_false = lin(
			"int_lin_le_imp",
			&[1],
			vec![t("x")],
			3,
			Some(FztArg::Bool(false)),
		);
		assert_eq!(lin_form(&imp_false), Some(LinForm::Valid));
	}

	#[test]
	fn ground_constraints_are_evaluated() {
		let valid = lin("int_lin_le", &[1], vec![Arg::Int(2)], 3, None);
		let unsat = lin("int_lin_eq", &[], vec![], 1, None);
		assert_eq!(lin_form(&valid), Some(LinForm::Valid));
		assert_eq!(lin_form(&unsat), Some(LinForm::Unsat));
		let also_unsat = lin("int_lin_le", &[1], vec![Arg::Int(5)], 3, None);
		assert_eq!(lin_norm_equal(&unsat, &also_unsat), Some(true));
	}

	/// The constraint `name(coeffs, vars, rhs[, reif])`.
	fn lin(
		name: &str,
		coeffs: &[i128],
		vars: Vec<Arg>,
		rhs: i128,
		reif: Option<FztArg>,
	) -> FztConstraint {
		let vars = vars
			.into_iter()
			.map(|v| match v {
				Arg::Int(k) => FztArg::Int(k),
				Arg::Term(s) => FztArg::Term(FztTerm(s.to_owned())),
			})
			.collect();
		let mut args = vec![
			FztArg::Array(coeffs.iter().map(|&c| FztArg::Int(c)).collect()),
			FztArg::Array(vars),
			FztArg::Int(rhs),
		];
		args.extend(reif);
		FztConstraint::new(name.to_owned(), args)
	}

	/// A literal argument.
	fn lit(name: &'static str) -> Option<FztArg> {
		Some(FztArg::Term(FztTerm(name.to_owned())))
	}

	#[test]
	fn literal_reification_is_kept() {
		let reif = lin(
			"int_lin_le_reif",
			&[1, 1],
			vec![t("x"), t("y")],
			3,
			lit("r"),
		);
		let reordered = lin(
			"int_lin_le_reif",
			&[1, 1],
			vec![t("y"), t("x")],
			3,
			lit("r"),
		);
		let imp = lin("int_lin_le_imp", &[1, 1], vec![t("x"), t("y")], 3, lit("r"));
		let other = lin(
			"int_lin_le_reif",
			&[1, 1],
			vec![t("x"), t("y")],
			3,
			lit("s"),
		);
		assert_eq!(lin_norm_equal(&reif, &reordered), Some(true));
		assert_eq!(lin_norm_equal(&reif, &imp), Some(false));
		assert_eq!(lin_norm_equal(&reif, &other), Some(false));
	}

	#[test]
	fn non_linear_constraints_have_no_form() {
		let clause = FztConstraint::new(
			"bool_clause",
			vec![FztArg::Array(vec![]), FztArg::Array(vec![])],
		);
		let body = lin("int_lin_le", &[1], vec![t("x")], 3, None);
		assert_eq!(lin_form(&clause), None);
		assert_eq!(lin_norm_equal(&clause, &body), None);
		// A reification literal that is an integer is not a linear constraint.
		let bad_reif = lin(
			"int_lin_le_reif",
			&[1],
			vec![t("x")],
			3,
			Some(FztArg::Int(1)),
		);
		assert_eq!(lin_form(&bad_reif), None);
	}

	#[test]
	fn sign_is_fixed_for_equalities_only() {
		let eq = lin("int_lin_eq", &[-1, 2], vec![t("x"), t("y")], 3, None);
		let eq_flipped = lin("int_lin_eq", &[1, -2], vec![t("x"), t("y")], -3, None);
		assert_eq!(lin_norm_equal(&eq, &eq_flipped), Some(true));
		let le = lin("int_lin_le", &[-1], vec![t("x")], 3, None);
		let le_flipped = lin("int_lin_le", &[1], vec![t("x")], -3, None);
		assert_eq!(lin_norm_equal(&le, &le_flipped), Some(false));
	}

	/// A term argument.
	fn t(term: &'static str) -> Arg {
		Arg::Term(term)
	}

	#[test]
	fn terms_are_merged_and_folded() {
		// `x + x + 2*(3*y + 1) <= 5` is `2*x + 6*y <= 3`.
		let unfolded = lin(
			"int_lin_le",
			&[1, 1, 2],
			vec![t("x"), t("x"), t("3*y + 1")],
			5,
			None,
		);
		let folded = lin("int_lin_le", &[2, 6], vec![t("x"), t("y")], 3, None);
		assert_eq!(lin_norm_equal(&unfolded, &folded), Some(true));
		// `1*!b <= 0` is `-b <= -1`.
		let negated = lin("int_lin_le", &[1], vec![t("1*!b")], 0, None);
		let flipped = lin("int_lin_le", &[-1], vec![t("b")], -1, None);
		assert_eq!(lin_norm_equal(&negated, &flipped), Some(true));
		// Cancelling terms disappear.
		let cancelled = lin(
			"int_lin_le",
			&[1, -1, 1],
			vec![t("x"), t("x"), t("y")],
			2,
			None,
		);
		let simple = lin("int_lin_le", &[1], vec![t("y")], 2, None);
		assert_eq!(lin_norm_equal(&cancelled, &simple), Some(true));
	}
}
