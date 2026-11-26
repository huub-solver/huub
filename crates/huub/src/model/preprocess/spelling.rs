//! The spellings of the `huub_*` predicates that can be emitted.
//!
//! Every one of them must be given a definition in
//! `share/huub-semantics.mzn`, which the checker uses to reason about them.

/// All `huub_*` spellings that can be emitted.
#[cfg(test)]
pub(crate) const ALL: &[&str] = &[
	ALL_DIFFERENT_INT,
	ARRAY_INT_MINIMUM,
	ASSUME,
	BOOL_CLAUSE_REIF,
	CIRCUIT,
	CUMULATIVE,
	DIFFN_INT,
	DIFFN_K_INT,
	DIFFN_NONSTRICT_INT,
	DIFFN_NONSTRICT_K_INT,
	DISJUNCTIVE_STRICT,
	FORMULA,
	SEQ_PRECEDE_CHAIN_INT,
	SUBCIRCUIT,
	TABLE_INT,
	VALUE_PRECEDE_CHAIN_INT,
];

/// `huub_all_different_int(array[int] of var int: x)`.
pub(crate) const ALL_DIFFERENT_INT: &str = "huub_all_different_int";
/// `huub_array_int_minimum(var int: m, array[int] of var int: x)`.
pub(crate) const ARRAY_INT_MINIMUM: &str = "huub_array_int_minimum";
/// `huub_assume(array[int] of var bool: b)`, the literals that search
/// assumes to hold.
pub(crate) const ASSUME: &str = "huub_assume";
/// `huub_bool_clause_reif(array[int] of var bool: as, array[int] of var
/// bool: bs, var bool: r)`.
pub(crate) const BOOL_CLAUSE_REIF: &str = "huub_bool_clause_reif";
/// `huub_circuit(array[int] of var int: x, int: offset)`.
pub(crate) const CIRCUIT: &str = "huub_circuit";
/// `huub_cumulative(array[int] of var int: s, array[int] of var int: d,
/// array[int] of var int: r, var int: b)`.
pub(crate) const CUMULATIVE: &str = "huub_cumulative";
/// `huub_diffn_int(array[int] of var int: x, array[int] of var int: y,
/// array[int] of var int: dx, array[int] of var int: dy)`.
pub(crate) const DIFFN_INT: &str = "huub_diffn_int";
/// `huub_diffn_k_int(array[int] of var int: box_posn, array[int] of var
/// int: box_size, int: dimensions)`.
pub(crate) const DIFFN_K_INT: &str = "huub_diffn_k_int";
/// `huub_diffn_nonstrict_int(array[int] of var int: x, array[int] of var
/// int: y, array[int] of var int: dx, array[int] of var int: dy)`.
pub(crate) const DIFFN_NONSTRICT_INT: &str = "huub_diffn_nonstrict_int";
/// `huub_diffn_nonstrict_k_int(array[int] of var int: box_posn, array[int]
/// of var int: box_size, int: dimensions)`.
pub(crate) const DIFFN_NONSTRICT_K_INT: &str = "huub_diffn_nonstrict_k_int";
/// `huub_disjunctive_strict(array[int] of var int: s, array[int] of int:
/// d)`.
pub(crate) const DISJUNCTIVE_STRICT: &str = "huub_disjunctive_strict";
/// `huub_formula(array[int] of int: ops, array[int] of var bool: atoms)`, a
/// propositional formula in the encoding of
/// [`FztContext::formula_encoding`](crate::model::preprocess::FztContext).
pub(crate) const FORMULA: &str = "huub_formula";
/// `huub_seq_precede_chain_int(array[int] of var int: x)`.
pub(crate) const SEQ_PRECEDE_CHAIN_INT: &str = "huub_seq_precede_chain_int";
/// `huub_subcircuit(array[int] of var int: x, int: offset)`.
pub(crate) const SUBCIRCUIT: &str = "huub_subcircuit";
/// `huub_table_int(array[int] of var int: x, array[int] of int: t)`.
pub(crate) const TABLE_INT: &str = "huub_table_int";
/// `huub_value_precede_chain_int(array[int] of int: t, array[int] of var
/// int: x)`.
pub(crate) const VALUE_PRECEDE_CHAIN_INT: &str = "huub_value_precede_chain_int";

#[cfg(test)]
mod tests {
	use crate::model::preprocess::spelling;

	/// Every `huub_*` spelling that can be emitted has a definition that the
	/// checker can use.
	#[test]
	fn huub_spellings_have_semantics() {
		let semantics = include_str!("../../../../../share/huub-semantics.mzn");
		for name in spelling::ALL {
			assert!(
				semantics.contains(&format!("predicate {name}(")),
				"`{name}` has no definition in `share/huub-semantics.mzn`"
			);
		}
	}
}
