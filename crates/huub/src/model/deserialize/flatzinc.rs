//! Module for the creation of a [`Model`] from a [`FlatZinc`] instance.

use std::{
	cell::RefCell,
	collections::hash_map::Entry,
	error::Error,
	fmt::{self, Debug, Display},
	hash::Hash,
	num::NonZero,
	ops::{Not, RangeInclusive},
	rc::Rc,
	sync::Arc,
};

use flatzinc_serde::{
	Annotation, AnnotationArgument, AnnotationCall, AnnotationLiteral, Argument, FlatZinc, Literal,
	NamedRef, Type, Variable, helpers::ArcKey,
};
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::IntervalIterator;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::warn;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolPropagationActions, BoolSimplificationActions, IntSimplificationActions,
		PropagationActions, ReasoningEngine,
	},
	lower::{Lowerer, LowererComplete, LoweringError},
	model::{
		Model,
		deserialize::{AnyView, Branching, Goal},
		expressions::{BoolFormula, linear::IntLinearExp},
		view::{View, boolean::BoolView},
	},
	solver::{
		self,
		branchers::{DecisionSelection, DomainSelection},
	},
};

/// Domain assumed for integer decision variables that do not have a domain
/// definition.
const FULL_INT_DOMAIN: RangeInclusive<IntVal> = IntVal::MIN..=IntVal::MAX;

/// Annotation identifiers that are known to the FlatZinc deserializer.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum AnnotationIdent {
	/// "bool_search" annotation for Boolean search strategies.
	BoolSearch,
	/// "bounds" consistency annotation.
	ConsistencyBounds,
	/// "domain" consistency annotation.
	ConsistencyDomain,
	/// "value_propagation" consistency annotation.
	ConsistencyValue,
	/// "edge_finding" annotation to enable edge finding propagation within a
	/// disjunctive propagator.
	DisjEdgeFinding,
	/// "not_last" annotation to enable not last propagation within the
	/// disjunctive propagator.
	DisjNotLast,
	/// "detectable_precedence" annotation to detectable precedence propagation
	/// within the disjunctive propagator.
	DisjDetectPrec,
	/// "int_search" annotation for integer search strategies.
	IntSearch,
	/// "seq_search" annotation for sequential search strategies.
	SeqSearch,
	/// "indomain" value selection annotation.
	ValSelIndomain,
	/// "indomain_min" value selection annotation.
	ValSelIndomainMin,
	/// "indomain_max" value selection annotation.
	ValSelIndomainMax,
	/// "indomain_median" value selection annotation.
	ValSelIndomainMedian,
	/// "indomain_middle" value selection annotation.
	ValSelIndomainMiddle,
	/// "indomain_interval" value selection annotation.
	ValSelIndomainInterval,
	/// "indomain_reverse_split" value selection annotation.
	ValSelIndomainReverseSplit,
	/// "indomain_split" value selection annotation.
	ValSelIndomainSplit,
	/// "outdomain_max" value selection annotation.
	ValSelOutdomainMax,
	/// "outdomain_median" value selection annotation.
	ValSelOutdomainMedian,
	/// "outdomain_min" value selection annotation.
	ValSelOutdomainMin,
	/// "anti_first_fail" variable selection annotation.
	VarSelAntiFirstFail,
	/// "dom_w_deg" variable selection annotation.
	VarSelDomWDeg,
	/// "first_fail" variable selection annotation.
	VarSelFirstFail,
	/// "input_order" variable selection annotation.
	VarSelInputOrder,
	/// "largest" variable selection annotation.
	VarSelLargest,
	/// "max_regret" variable selection annotation.
	VarSelMaxRegret,
	/// "most_constrained" variable selection annotation.
	VarSelMostConstrained,
	/// "occurrence" variable selection annotation.
	VarSelOccurrence,
	/// "smallest" variable selection annotation.
	VarSelSmallest,
	/// "warm_start_array" annotation for grouped warm start directives.
	WarmStartArray,
	/// "warm_start_bool" annotation for Boolean warm start directives.
	WarmStartBool,
	/// "warm_start_int" annotation for integer warm start directives.
	WarmStartInt,
}

/// Represents the identifier of a constraint as used in the MiniZinc standard
/// library or Huub's MiniZinc library.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum ConstraintIdent {
	/// "huub_all_different_int"
	AllDifferentInt,
	/// "array_bool_and"
	ArrayBoolAnd,
	/// "array_bool_element"
	ArrayBoolElement,
	/// "array_bool_xor"
	ArrayBoolXor,
	/// "array_int_element"
	ArrayIntElement,
	/// "array_int_maximum"
	ArrayIntMaximum,
	/// "array_int_minimum"
	ArrayIntMinimum,
	/// "array_var_bool_element"
	ArrayVarBoolElement,
	/// "array_var_int_element"
	ArrayVarIntElement,
	/// "huub_assume"
	Assume,
	/// "bool2int"
	Bool2Int,
	/// "bool_clause"
	BoolClause,
	/// "huub_bool_clause_reif"
	BoolClauseReif,
	/// "bool_eq"
	BoolEq,
	/// "bool_eq_reif"
	BoolEqReif,
	/// "bool_lin_eq"
	BoolLinEq,
	/// "bool_not"
	BoolNot,
	/// "bool_xor"
	BoolXor,
	/// "cumulative"
	Cumulative,
	/// "huub_diffn_int" and "huub_diffn_nonstrict_int"
	DiffnInt {
		/// Whether the constraint is strict or non-strict.
		strict: bool,
	},
	/// "huub_diffn_k_int" and "huub_diffn_nonstrict_k_int"
	DiffnKInt {
		/// Whether the constraint is strict or non-strict.
		strict: bool,
	},
	/// "huub_disjunctive_strict"
	DisjuctiveStrict,
	/// "int_abs"
	IntAbs,
	/// "int_abs"
	IntDiv,
	/// "int_eq"
	IntEq,
	/// "int_eq_imp"
	IntEqImp,
	/// "int_eq_reif"
	IntEqReif,
	/// "int_le"
	IntLe,
	/// "int_le_imp"
	IntLeImp,
	/// "int_le_reif"
	IntLeReif,
	/// "int_lin_eq"
	IntLinEq,
	/// "int_lin_eq_imp"
	IntLinEqImp,
	/// "int_lin_eq_reif"
	IntLinEqReif,
	/// "int_lin_le"
	IntLinLe,
	/// "int_lin_le_imp"
	IntLinLeImp,
	/// "int_lin_le_reif"
	IntLinLeReif,
	/// "int_lin_ne"
	IntLinNe,
	/// "int_lin_ne_imp"
	IntLinNeImp,
	/// "int_lin_ne_reif"
	IntLinNeReif,
	/// "int_max"
	IntMax,
	/// "int_min"
	IntMin,
	/// "int_ne"
	IntNe,
	/// "int_ne_imp"
	IntNeImp,
	/// "int_ne_reif"
	IntNeReif,
	/// "int_pow"
	IntPow,
	/// "int_times"
	IntTimes,
	/// "huub_regular"
	Regular,
	/// "huub_seq_precede_chain_int"
	SeqPrecedeChainInt,
	/// "set_in"
	SetIn,
	/// "set_in_reif"
	SetInReif,
	/// "huub_table_int"
	TableInt,
	/// "huub_value_precede_chain_int"
	ValuePrecedeChain,
}

/// Errors that can occur when converting a [`FlatZinc`] instance to a [`Model`]
/// or [`Solver`](crate::solver::Solver) object.
#[derive(Debug)]
#[non_exhaustive]
pub enum FlatZincError {
	/// FlatZinc instance contained a decision variable with an unsupported
	/// type.
	UnsupportedType(Type),
	/// FlatZinc instance contained a constraint with an unknown identifier.
	UnknownConstraint(String),
	/// FlatZinc instance contained a constraint with an invalid number of
	/// arguments.
	InvalidNumArgs {
		/// Identifier of the constraint.
		name: &'static str,
		/// Number of arguments found.
		found: usize,
		/// Number of arguments expected.
		expected: usize,
	},
	/// FlatZinc instance used an identifier that was not defined.
	UnknownIdentifier(String),
	/// FlatZinc constraint or annotation used an argument of the wrong type.
	InvalidArgumentType {
		/// Expected type of the argument.
		expected: &'static str,
		/// Type of the argument found.
		found: String,
	},
	/// Error that occurred when constructing the [`Model`] object or
	/// translating it to a [`Solver`](crate::solver::Solver) object.
	ReformulationError(LoweringError),
}

#[derive(Clone, Debug)]
/// Intermediate data structure used during the lowering of a FlatZinc instance.
pub struct FlatZincLowerData {
	/// Metadata produced when building the model from the FlatZinc instance.
	pub(crate) meta: FlatZincModelMeta,
	/// The [`Model`] instance created from the FlatZinc instance.
	pub(crate) model: Model,
}

/// Metadata produced when building a model from a FlatZinc instance.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct FlatZincModelMeta {
	/// Mapping from FlatZinc identifiers to model views.
	pub names: FxHashMap<ArcKey<Variable<FznIdent>>, AnyView>,
	/// Statistics gathered during FlatZinc extraction.
	pub stats: FlatZincStatistics,
	/// Optional branching annotation extracted from the instance.
	pub branching: Option<Branching>,
	/// Optional optimization goal extracted from the instance.
	pub goal: Option<Goal<View<IntVal>>>,
	/// Boolean assumptions collected from `huub_assume` constraints.
	///
	/// Each entry pairs a human-readable label (the FlatZinc identifier of the
	/// variable, or the literal string `"false"` for static constants) with the
	/// model-level Boolean view that the solver should treat as an assumption.
	/// The list preserves the order in which the `huub_assume` constraints (and
	/// elements within each constraint) appeared in the FlatZinc instance.
	pub assumptions: Vec<(String, View<bool>)>,
}

/// Metadata produced when building a solver from a FlatZinc instance.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct FlatZincSolverMeta {
	/// Mapping from FlatZinc identifiers to solver views.
	pub names: FxHashMap<ArcKey<Variable<FznIdent>>, solver::AnyView>,
	/// Statistics gathered during FlatZinc extraction.
	pub stats: FlatZincStatistics,
	/// Optional optimization goal extracted from the instance.
	pub goal: Option<Goal<solver::View<IntVal>>>,
	/// Boolean assumptions collected from `huub_assume` constraints, lowered
	/// to solver-level Boolean views.
	///
	/// See [`FlatZincModelMeta::assumptions`] for the semantics of the label
	/// associated with each view.
	pub assumptions: Vec<(String, solver::View<bool>)>,
}

/// Statistical information about the extraction process that creates a
/// [`Model`] from a [`FlatZinc`] instance.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct FlatZincStatistics {
	/// Number of views extracted from the FlatZinc specification
	///
	/// Views currently creates the following types of views:
	/// - literal views (i.e., direct use of literals used to as part of
	///   variable representation instead of reified constraints)
	/// - linear views (i.e., scaled and offset views of integer variables)
	/// - Boolean linear views (i.e., scaled and offset views of Boolean
	///   variables, able to represent any integer value with two values)
	pub extracted_views: u32,
	/// Number of decisions removed through unification
	pub unified_decisions: u32,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
/// Representation of a FlatZinc identifier for Huub specific constraints and
/// annotations.
///
/// Note that it has a `Unknown` variant for identifiers that are not known to
/// Huub for reporting error messages.
pub enum FznIdent {
	/// An identifier for a known constraint or annotation.
	Known(KnownIdent),
	/// An unknown identifier that was not recognized by Huub.
	Unknown(Box<str>),
}

/// Builder for creating a model from a FlatZinc instance
pub(crate) struct FznModelBuilder<'a> {
	/// The FlatZinc instance to build the model from
	fzn: &'a FlatZinc<FznIdent>,
	/// A mapping from FlatZinc identifiers to model views
	map: FxHashMap<ArcKey<Variable<FznIdent>>, AnyView>,
	/// The incumbent model
	prb: Model,
	/// Flags indicating which constraints have been processed
	processed: Vec<bool>,
	/// Statistics about the extraction process
	stats: FlatZincStatistics,
	/// Boolean assumptions collected from `huub_assume` constraints, in the
	/// order in which they were encountered in the FlatZinc instance.
	assumptions: Vec<(String, View<bool>)>,
}

/// Trait that extends [`FlatZinc`] with Huub-specific functionality.
///
/// This trait provides the [`lower()`](HuubFlatZinc::lower) method, which is
/// the recommended way to convert a FlatZinc instance into a Huub [`Model`] or
/// [`Solver`](crate::solver::Solver).
///
/// ```rust,ignore
/// use huub::model::deserialize::flatzinc::HuubFlatZinc;
///
/// // Lower to a model
/// let (model, meta) = fzn.lower().to_model()?;
///
/// // Lower to a solver with custom configuration
/// let (solver, meta) = fzn.lower()
///     .preprocessing(2)
///     .to_solver()?;
/// ```
pub trait HuubFlatZinc {
	/// Returns a builder that can be used to lower the [`FlatZinc`] instance
	/// to a [`Model`] (via [`to_model()`](Lowerer::to_model)) or directly to
	/// a [`Solver`](crate::solver::Solver) (via
	/// [`to_solver()`](Lowerer::to_solver)).
	fn lower(&self) -> Lowerer<Result<FlatZincLowerData, FlatZincError>>;
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// Identifiers that are known to the FlatZinc deserializer.
pub enum KnownIdent {
	/// Annotation identifiers.
	Annotation(AnnotationIdent),
	/// Constraint identifiers.
	Constraint(ConstraintIdent),
}

impl AnnotationIdent {
	/// Returns the string representation of the annotation identifier as used
	/// in the MiniZinc standard library or Huub's MiniZinc library.
	pub fn as_str(&self) -> &'static str {
		match self {
			Self::BoolSearch => "bool_search",
			Self::ConsistencyBounds => "bounds",
			Self::ConsistencyDomain => "domain",
			Self::ConsistencyValue => "value_propagation",
			Self::DisjDetectPrec => "detectable_precedence",
			Self::DisjEdgeFinding => "edge_finding",
			Self::DisjNotLast => "not_last",
			Self::IntSearch => "int_search",
			Self::SeqSearch => "seq_search",
			Self::ValSelIndomain => "indomain",
			Self::ValSelIndomainInterval => "indomain_interval",
			Self::ValSelIndomainMax => "indomain_max",
			Self::ValSelIndomainMedian => "indomain_median",
			Self::ValSelIndomainMiddle => "indomain_middle",
			Self::ValSelIndomainMin => "indomain_min",
			Self::ValSelIndomainReverseSplit => "indomain_reverse_split",
			Self::ValSelIndomainSplit => "indomain_split",
			Self::ValSelOutdomainMax => "outdomain_max",
			Self::ValSelOutdomainMedian => "outdomain_median",
			Self::ValSelOutdomainMin => "outdomain_min",
			Self::VarSelAntiFirstFail => "anti_first_fail",
			Self::VarSelDomWDeg => "dom_w_deg",
			Self::VarSelFirstFail => "first_fail",
			Self::VarSelInputOrder => "input_order",
			Self::VarSelLargest => "largest",
			Self::VarSelMaxRegret => "max_regret",
			Self::VarSelMostConstrained => "most_constrained",
			Self::VarSelOccurrence => "occurrence",
			Self::VarSelSmallest => "smallest",
			Self::WarmStartArray => "warm_start_array",
			Self::WarmStartBool => "warm_start_bool",
			Self::WarmStartInt => "warm_start_int",
		}
	}
}

impl Display for AnnotationIdent {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(self.as_str())
	}
}

impl TryFrom<&str> for AnnotationIdent {
	type Error = ();

	fn try_from(value: &str) -> Result<Self, Self::Error> {
		match value {
			"anti_first_fail" => Ok(Self::VarSelAntiFirstFail),
			"bool_search" => Ok(Self::BoolSearch),
			"bounds" => Ok(Self::ConsistencyBounds),
			"detectable_precedence" => Ok(Self::DisjDetectPrec),
			"dom_w_deg" => Ok(Self::VarSelDomWDeg),
			"domain" => Ok(Self::ConsistencyDomain),
			"edge_finding" => Ok(Self::DisjEdgeFinding),
			"first_fail" => Ok(Self::VarSelFirstFail),
			"indomain" => Ok(Self::ValSelIndomain),
			"indomain_interval" => Ok(Self::ValSelIndomainInterval),
			"indomain_max" => Ok(Self::ValSelIndomainMax),
			"indomain_median" => Ok(Self::ValSelIndomainMedian),
			"indomain_middle" => Ok(Self::ValSelIndomainMiddle),
			"indomain_min" => Ok(Self::ValSelIndomainMin),
			"indomain_reverse_split" => Ok(Self::ValSelIndomainReverseSplit),
			"indomain_split" => Ok(Self::ValSelIndomainSplit),
			"input_order" => Ok(Self::VarSelInputOrder),
			"int_search" => Ok(Self::IntSearch),
			"largest" => Ok(Self::VarSelLargest),
			"max_regret" => Ok(Self::VarSelMaxRegret),
			"most_constrained" => Ok(Self::VarSelMostConstrained),
			"not_last" => Ok(Self::DisjNotLast),
			"occurrence" => Ok(Self::VarSelOccurrence),
			"outdomain_max" => Ok(Self::ValSelOutdomainMax),
			"outdomain_median" => Ok(Self::ValSelOutdomainMedian),
			"outdomain_min" => Ok(Self::ValSelOutdomainMin),
			"seq_search" => Ok(Self::SeqSearch),
			"smallest" => Ok(Self::VarSelSmallest),
			"value_propagation" => Ok(Self::ConsistencyValue),
			"warm_start_array" => Ok(Self::WarmStartArray),
			"warm_start_bool" => Ok(Self::WarmStartBool),
			"warm_start_int" => Ok(Self::WarmStartInt),
			_ => Err(()),
		}
	}
}

impl ConstraintIdent {
	/// Returns the string representation of the constraint identifier as used
	/// in the MiniZinc standard library or Huub's MiniZinc library.
	pub fn as_str(&self) -> &'static str {
		match self {
			Self::AllDifferentInt => "huub_all_different_int",
			Self::ArrayBoolAnd => "array_bool_and",
			Self::ArrayBoolElement => "array_bool_element",
			Self::ArrayBoolXor => "array_bool_xor",
			Self::ArrayIntElement => "array_int_element",
			Self::ArrayIntMaximum => "huub_array_int_maximum",
			Self::ArrayIntMinimum => "huub_array_int_minimum",
			Self::ArrayVarBoolElement => "array_var_bool_element",
			Self::ArrayVarIntElement => "array_var_int_element",
			Self::Assume => "huub_assume",
			Self::Bool2Int => "bool2int",
			Self::BoolClause => "bool_clause",
			Self::BoolClauseReif => "huub_bool_clause_reif",
			Self::BoolEq => "bool_eq",
			Self::BoolEqReif => "bool_eq_reif",
			Self::BoolLinEq => "bool_lin_eq",
			Self::BoolNot => "bool_not",
			Self::BoolXor => "bool_xor",
			Self::Cumulative => "huub_cumulative",
			Self::DiffnInt { strict: false } => "huub_diffn_nonstrict_int",
			Self::DiffnInt { strict: true } => "huub_diffn_int",
			Self::DiffnKInt { strict: false } => "huub_diffn_nonstrict_k_int",
			Self::DiffnKInt { strict: true } => "huub_diffn_k_int",
			Self::DisjuctiveStrict => "huub_disjunctive_strict",
			Self::IntAbs => "int_abs",
			Self::IntDiv => "int_div",
			Self::IntEq => "int_eq",
			Self::IntEqImp => "int_eq_imp",
			Self::IntEqReif => "int_eq_reif",
			Self::IntLe => "int_le",
			Self::IntLeImp => "int_le_imp",
			Self::IntLeReif => "int_le_reif",
			Self::IntLinEq => "int_lin_eq",
			Self::IntLinEqImp => "int_lin_eq_imp",
			Self::IntLinEqReif => "int_lin_eq_reif",
			Self::IntLinLe => "int_lin_le",
			Self::IntLinLeImp => "int_lin_le_imp",
			Self::IntLinLeReif => "int_lin_le_reif",
			Self::IntLinNe => "int_lin_ne",
			Self::IntLinNeImp => "int_lin_ne_imp",
			Self::IntLinNeReif => "int_lin_ne_reif",
			Self::IntMax => "int_max",
			Self::IntMin => "int_min",
			Self::IntNe => "int_ne",
			Self::IntNeImp => "int_ne_imp",
			Self::IntNeReif => "int_ne_reif",
			Self::IntPow => "int_pow",
			Self::IntTimes => "int_times",
			Self::Regular => "huub_regular",
			Self::SeqPrecedeChainInt => "huub_seq_precede_chain_int",
			Self::SetIn => "set_in",
			Self::SetInReif => "set_in_reif",
			Self::TableInt => "huub_table_int",
			Self::ValuePrecedeChain => "huub_value_precede_chain_int",
		}
	}
}

impl Display for ConstraintIdent {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(self.as_str())
	}
}

impl TryFrom<&str> for ConstraintIdent {
	type Error = ();

	fn try_from(value: &str) -> Result<Self, Self::Error> {
		match value {
			"array_bool_and" => Ok(Self::ArrayBoolAnd),
			"array_bool_element" => Ok(Self::ArrayBoolElement),
			"array_bool_xor" => Ok(Self::ArrayBoolXor),
			"array_int_element" => Ok(Self::ArrayIntElement),
			"array_var_bool_element" => Ok(Self::ArrayVarBoolElement),
			"array_var_int_element" => Ok(Self::ArrayVarIntElement),
			"bool2int" => Ok(Self::Bool2Int),
			"bool_clause" => Ok(Self::BoolClause),
			"bool_eq" => Ok(Self::BoolEq),
			"bool_eq_reif" => Ok(Self::BoolEqReif),
			"bool_lin_eq" => Ok(Self::BoolLinEq),
			"bool_not" => Ok(Self::BoolNot),
			"bool_xor" => Ok(Self::BoolXor),
			"huub_all_different_int" => Ok(Self::AllDifferentInt),
			"huub_array_int_maximum" => Ok(Self::ArrayIntMaximum),
			"huub_array_int_minimum" => Ok(Self::ArrayIntMinimum),
			"huub_assume" => Ok(Self::Assume),
			"huub_bool_clause_reif" => Ok(Self::BoolClauseReif),
			"huub_cumulative" => Ok(Self::Cumulative),
			"huub_diffn_int" => Ok(Self::DiffnInt { strict: true }),
			"huub_diffn_k_int" => Ok(Self::DiffnKInt { strict: true }),
			"huub_diffn_nonstrict_k_int" => Ok(Self::DiffnKInt { strict: false }),
			"huub_diffn_nonstrict_int" => Ok(Self::DiffnInt { strict: false }),
			"huub_disjunctive_strict" => Ok(Self::DisjuctiveStrict),
			"huub_regular" => Ok(Self::Regular),
			"huub_seq_precede_chain_int" => Ok(Self::SeqPrecedeChainInt),
			"huub_table_int" => Ok(Self::TableInt),
			"huub_value_precede_chain_int" => Ok(Self::ValuePrecedeChain),
			"int_abs" => Ok(Self::IntAbs),
			"int_div" => Ok(Self::IntDiv),
			"int_eq" => Ok(Self::IntEq),
			"int_eq_imp" => Ok(Self::IntEqImp),
			"int_eq_reif" => Ok(Self::IntEqReif),
			"int_le" => Ok(Self::IntLe),
			"int_le_imp" => Ok(Self::IntLeImp),
			"int_le_reif" => Ok(Self::IntLeReif),
			"int_lin_eq" => Ok(Self::IntLinEq),
			"int_lin_eq_imp" => Ok(Self::IntLinEqImp),
			"int_lin_eq_reif" => Ok(Self::IntLinEqReif),
			"int_lin_le" => Ok(Self::IntLinLe),
			"int_lin_le_imp" => Ok(Self::IntLinLeImp),
			"int_lin_le_reif" => Ok(Self::IntLinLeReif),
			"int_lin_ne" => Ok(Self::IntLinNe),
			"int_lin_ne_imp" => Ok(Self::IntLinNeImp),
			"int_lin_ne_reif" => Ok(Self::IntLinNeReif),
			"int_max" => Ok(Self::IntMax),
			"int_min" => Ok(Self::IntMin),
			"int_ne" => Ok(Self::IntNe),
			"int_ne_imp" => Ok(Self::IntNeImp),
			"int_ne_reif" => Ok(Self::IntNeReif),
			"int_pow" => Ok(Self::IntPow),
			"int_times" => Ok(Self::IntTimes),
			"set_in" => Ok(Self::SetIn),
			"set_in_reif" => Ok(Self::SetInReif),
			_ => Err(()),
		}
	}
}

impl HuubFlatZinc for FlatZinc<FznIdent> {
	fn lower(&self) -> Lowerer<Result<FlatZincLowerData, FlatZincError>> {
		let deserialize_model = |fzn: &FlatZinc<FznIdent>| {
			let mut builder = FznModelBuilder::new(fzn);
			builder.unify_variables()?;
			builder.extract_views()?;
			builder.post_constraints()?;
			builder.ensure_output()?;

			builder.finalize()
		};

		LowererComplete::builder_internal(
			deserialize_model(self).map(|(model, meta)| FlatZincLowerData { meta, model }),
		)
	}
}

impl Display for FlatZincError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::UnsupportedType(t) => write!(f, "{t:?} type variables are not supported by huub"),
			Self::UnknownConstraint(c) => write!(
				f,
				"constraint cannot be constructed using unknown identifier `{c}'"
			),
			Self::InvalidNumArgs {
				name,
				found,
				expected,
			} => write!(
				f,
				"constraints with identifiers `{name}' must have {expected} arguments, found {found}"
			),
			Self::UnknownIdentifier(ident) => write!(f, "could not find identifier `{ident}'"),
			Self::InvalidArgumentType { expected, found } => {
				write!(f, "argument found of type `{found}', expected `{expected}'")
			}
			Self::ReformulationError(err) => {
				write!(f, "error reformulating generated model `{err}'")
			}
		}
	}
}

impl Error for FlatZincError {}

impl From<<Model as ReasoningEngine>::Conflict> for FlatZincError {
	fn from(conflict: <Model as ReasoningEngine>::Conflict) -> Self {
		Self::ReformulationError(LoweringError::from(conflict))
	}
}

impl From<LoweringError> for FlatZincError {
	fn from(reformulation_error: LoweringError) -> Self {
		Self::ReformulationError(reformulation_error)
	}
}

impl Display for FznIdent {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Known(ident) => Display::fmt(&ident, f),
			Self::Unknown(ident) => f.write_str(ident),
		}
	}
}

impl From<&str> for FznIdent {
	fn from(value: &str) -> Self {
		if let Ok(ident) = ConstraintIdent::try_from(value) {
			Self::Known(KnownIdent::Constraint(ident))
		} else if let Ok(ident) = AnnotationIdent::try_from(value) {
			Self::Known(KnownIdent::Annotation(ident))
		} else {
			Self::Unknown(value.into())
		}
	}
}

impl<'a> FznModelBuilder<'a> {
	/// Extract a [`Vec<Literal>`] from an [`AnnotationArgument`].
	fn ann_arg_var_array(
		&self,
		arg: &AnnotationArgument<FznIdent>,
	) -> Result<Vec<Literal<FznIdent>>, FlatZincError> {
		let arr = match arg {
			AnnotationArgument::Array(x) => x.clone(),
			AnnotationArgument::ArrayNamed(x) => x
				.upgrade()
				.unwrap()
				.contents
				.iter()
				.cloned()
				.map_into()
				.collect(),
			_ => {
				return Err(FlatZincError::InvalidArgumentType {
					expected: "array of literals",
					found: format!("{arg:?}"),
				});
			}
		};
		arr.into_iter()
			.map(|l| {
				Ok(match l {
					AnnotationLiteral::Int(x) => Literal::Int(x),
					AnnotationLiteral::Float(x) => Literal::Float(x),
					AnnotationLiteral::Variable(x) => Literal::Variable(x.upgrade().unwrap()),
					AnnotationLiteral::Bool(x) => Literal::Bool(x),
					AnnotationLiteral::IntSet(x) => Literal::IntSet(x),
					AnnotationLiteral::FloatSet(x) => Literal::FloatSet(x),
					AnnotationLiteral::String(x) => Literal::String(x),
					AnnotationLiteral::Annotation(x) => {
						return Err(FlatZincError::InvalidArgumentType {
							expected: "literal",
							found: format!("{x:?}"),
						});
					}
				})
			})
			.collect()
	}

	/// Extract an [`DecisionSelection`] from an [`AnnotationArgument`] in a
	/// [`FlatZinc`] instance, or return a
	/// [`FlatZincError::InvalidArgumentType`] if an invalid type.
	fn ann_dcn_sel(arg: &AnnotationArgument<FznIdent>) -> Result<DecisionSelection, FlatZincError> {
		let AnnotationArgument::Literal(AnnotationLiteral::Annotation(ann)) = arg else {
			return Err(FlatZincError::InvalidArgumentType {
				expected: "ann",
				found: format!("{arg:?}"),
			});
		};
		if let Annotation::Atom(FznIdent::Known(KnownIdent::Annotation(ann))) = ann {
			match ann {
				AnnotationIdent::VarSelAntiFirstFail => {
					return Ok(DecisionSelection::AntiFirstFail);
				}
				AnnotationIdent::VarSelDomWDeg => return Ok(DecisionSelection::DomWDeg),
				AnnotationIdent::VarSelFirstFail => return Ok(DecisionSelection::FirstFail),
				AnnotationIdent::VarSelInputOrder => return Ok(DecisionSelection::InputOrder),
				AnnotationIdent::VarSelLargest => return Ok(DecisionSelection::Largest),
				AnnotationIdent::VarSelMaxRegret => return Ok(DecisionSelection::MaxRegret),
				AnnotationIdent::VarSelMostConstrained => {
					return Ok(DecisionSelection::MostConstrained);
				}
				AnnotationIdent::VarSelOccurrence => return Ok(DecisionSelection::Occurrence),
				AnnotationIdent::VarSelSmallest => return Ok(DecisionSelection::Smallest),
				_ => {}
			}
		}
		warn!(
			target: "flatzinc",
			selection = %ann,
			fallback = "first_fail",
			"unsupported value selection"
		);
		Ok(DecisionSelection::FirstFail)
	}

	/// Extract an [`DomainSelection`] from an [`AnnotationArgument`] in a
	/// [`FlatZinc`] instance, or return a
	/// [`FlatZincError::InvalidArgumentType`] if an invalid type.
	fn ann_dom_sel(arg: &AnnotationArgument<FznIdent>) -> Result<DomainSelection, FlatZincError> {
		let AnnotationArgument::Literal(AnnotationLiteral::Annotation(ann)) = arg else {
			return Err(FlatZincError::InvalidArgumentType {
				expected: "ann",
				found: format!("{arg:?}"),
			});
		};
		if let Annotation::Atom(FznIdent::Known(KnownIdent::Annotation(ann))) = ann {
			match ann {
				AnnotationIdent::ValSelIndomain | AnnotationIdent::ValSelIndomainMin => {
					return Ok(DomainSelection::IndomainMin);
				}
				AnnotationIdent::ValSelIndomainMax => return Ok(DomainSelection::IndomainMax),
				AnnotationIdent::ValSelIndomainMedian => {
					return Ok(DomainSelection::IndomainMedian);
				}
				AnnotationIdent::ValSelIndomainMiddle => {
					return Ok(DomainSelection::IndomainMiddle);
				}
				AnnotationIdent::ValSelIndomainInterval => {
					return Ok(DomainSelection::IndomainInterval);
				}
				AnnotationIdent::ValSelIndomainSplit => return Ok(DomainSelection::IndomainSplit),
				AnnotationIdent::ValSelIndomainReverseSplit => {
					return Ok(DomainSelection::IndomainReverseSplit);
				}
				AnnotationIdent::ValSelOutdomainMax => return Ok(DomainSelection::OutdomainMax),
				AnnotationIdent::ValSelOutdomainMedian => {
					return Ok(DomainSelection::OutdomainMedian);
				}
				AnnotationIdent::ValSelOutdomainMin => return Ok(DomainSelection::OutdomainMin),
				_ => {}
			}
		}
		warn!(
			target: "flatzinc",
			selection = %ann,
			fallback = "indomain_min",
			"unsupported value selection"
		);
		Ok(DomainSelection::IndomainMin)
	}

	/// Process a [`AnnotationCall`] expected to contain a search selection
	/// strategy, and return a tuple containing (1) the general search strategy,
	/// and (2) the warm start instructions.
	fn ann_to_branchings(
		&mut self,
		c: &AnnotationCall<FznIdent>,
	) -> Result<(Vec<View<bool>>, Vec<Branching>), FlatZincError> {
		if let FznIdent::Known(KnownIdent::Annotation(ann)) = c.id {
			match ann {
				AnnotationIdent::BoolSearch => {
					return if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
						let vars = self
							.ann_arg_var_array(vars)?
							.iter()
							.map(|l| self.lit_bool(l))
							.try_collect()?;
						let var_sel = Self::ann_dcn_sel(var_sel)?;
						let val_sel = Self::ann_dom_sel(val_sel)?;
						Ok((Vec::new(), vec![Branching::Bool(vars, var_sel, val_sel)]))
					} else {
						Err(FlatZincError::InvalidNumArgs {
							name: ann.as_str(),
							found: c.args.len(),
							expected: 4,
						})
					};
				}
				AnnotationIdent::IntSearch => {
					return if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
						let vars = self
							.ann_arg_var_array(vars)?
							.iter()
							.map(|l| self.lit_int(l))
							.try_collect()?;
						let var_sel = Self::ann_dcn_sel(var_sel)?;
						let val_sel = Self::ann_dom_sel(val_sel)?;

						Ok((Vec::new(), vec![Branching::Int(vars, var_sel, val_sel)]))
					} else {
						Err(FlatZincError::InvalidNumArgs {
							name: ann.as_str(),
							found: c.args.len(),
							expected: 4,
						})
					};
				}
				AnnotationIdent::SeqSearch | AnnotationIdent::WarmStartArray => {
					return if let [AnnotationArgument::Array(searches)] = c.args.as_slice() {
						let mut warm_start = Vec::new();
						let mut branchings = Vec::new();
						for ann in searches {
							match ann {
								AnnotationLiteral::Annotation(Annotation::Call(sub_call)) => {
									let (w, b) = self.ann_to_branchings(sub_call)?;
									warm_start.extend(w);
									branchings.extend(b);
								}
								_ => warn!(
									target: "flatzinc",
									annotation = %ann,
									"unsupported search annotation"
								),
							}
						}
						Ok((warm_start, branchings))
					} else {
						Err(FlatZincError::InvalidNumArgs {
							name: ann.as_str(),
							found: c.args.len(),
							expected: 1,
						})
					};
				}
				AnnotationIdent::WarmStartBool => {
					return if let [vars, vals] = c.args.as_slice() {
						let vars: Vec<_> = self
							.ann_arg_var_array(vars)?
							.iter()
							.map(|l| self.lit_bool(l))
							.try_collect()?;
						let vals: Vec<_> = self
							.ann_arg_var_array(vals)?
							.iter()
							.map(|l| self.par_bool(l))
							.try_collect()?;

						Ok((
							vars.into_iter()
								.zip(vals)
								.map(|(v, b)| if b { v } else { !v })
								.collect(),
							Vec::new(),
						))
					} else {
						Err(FlatZincError::InvalidNumArgs {
							name: ann.as_str(),
							found: c.args.len(),
							expected: 2,
						})
					};
				}
				AnnotationIdent::WarmStartInt => {
					return if let [vars, vals] = c.args.as_slice() {
						let vars: Vec<_> = self
							.ann_arg_var_array(vars)?
							.iter()
							.map(|l| self.lit_int(l))
							.try_collect()?;
						let vals: Vec<_> = self
							.ann_arg_var_array(vals)?
							.iter()
							.map(|l| self.par_int(l))
							.try_collect()?;

						Ok((
							vars.into_iter()
								.zip(vals)
								.map(|(var, val)| var.eq(val))
								.collect(),
							Vec::new(),
						))
					} else {
						Err(FlatZincError::InvalidNumArgs {
							name: ann.as_str(),
							found: c.args.len(),
							expected: 2,
						})
					};
				}
				_ => {}
			}
		}
		warn!(
			target: "flatzinc",
			annotation = %c.id,
			"ignore unsupported search annotation"
		);
		Ok((Vec::new(), Vec::new()))
	}

	/// Check whether an annotation atom is present in the given list of
	/// annotations, marking it as used if found.
	fn anns_contains(
		ann: &[Annotation<FznIdent>],
		ann_used: &mut [bool],
		ident: AnnotationIdent,
	) -> bool {
		for (i, a) in ann.iter().enumerate() {
			if let Annotation::Atom(FznIdent::Known(KnownIdent::Annotation(x))) = a
				&& *x == ident
			{
				ann_used[i] = true;
				return true;
			}
		}
		false
	}

	/// Extract a [`Vec<Literal>`] from an [`Argument`].
	fn arg_array(
		&self,
		arg: &'a Argument<FznIdent>,
	) -> Result<&'a [Literal<FznIdent>], FlatZincError> {
		match arg {
			Argument::Array(x) => Ok(x),
			Argument::ArrayNamed(x) => Ok(&x.contents),
			Argument::Literal(x) => Err(FlatZincError::InvalidArgumentType {
				expected: "array",
				found: format!("{x:?}"),
			}),
		}
	}

	/// Extract a Boolean decision variable from an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a Boolean decision variable.
	fn arg_bool(&mut self, arg: &Argument<FznIdent>) -> Result<View<bool>, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_bool(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "boolean literal",
				found: format!("{arg:?}"),
			}),
		}
	}

	/// Check whether the given [`Argument`] is an array of length `len`.
	fn arg_has_length(&self, arg: &Argument<FznIdent>, len: usize) -> bool {
		match arg {
			Argument::Array(x) => x.len() == len,
			Argument::ArrayNamed(x) => x.contents.len() == len,
			_ => false,
		}
	}

	/// Extract an integer decision variable from an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not an integer decision variable.
	fn arg_int(&mut self, arg: &Argument<FznIdent>) -> Result<View<IntVal>, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "integer literal",
				found: format!("{arg:?}"),
			}),
		}
	}

	/// Extract a parameter integer value from an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not an integer parameter.
	fn arg_par_int(&self, arg: &Argument<FznIdent>) -> Result<IntVal, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.par_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par integer literal",
				found: format!("{arg:?}"),
			}),
		}
	}

	/// Extract a parameter integer set value from an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a parameter set.
	fn arg_par_set(&self, arg: &Argument<FznIdent>) -> Result<IntSet, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.par_set(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par set literal",
				found: format!("{arg:?}"),
			}),
		}
	}

	/// Convert a Flatzinc `regular_int` constraint to a set of
	/// [`Constraint::TableInt`] constraints.
	fn convert_regular_to_tables(
		&mut self,
		vars: Vec<View<IntVal>>,
		transitions: Vec<Vec<IntVal>>,
		init_state: IntVal,
		accept_states: FxHashSet<IntVal>,
	) -> Result<(), LoweringError> {
		// TODO: Add the regular checking

		let mut start: Vec<Vec<IntVal>> = Vec::new();
		let mut middle: Vec<Vec<IntVal>> = Vec::new();
		let mut end: Vec<Vec<IntVal>> = Vec::new();

		for (i, state_trans) in transitions.iter().enumerate() {
			let cur_state = i as IntVal + 1;
			for (j, &next_state) in state_trans.iter().enumerate() {
				let input_read = j as IntVal + 1;

				// Skip transitions to the "invalid" state
				if next_state == 0 {
					continue;
				}
				// If the current state is the initial state, add the transition to start
				// table
				if cur_state == init_state {
					start.push(vec![input_read, next_state]);
				}
				// Add transition to the middle table (all valid transitions are allowed
				// here)
				middle.push(vec![cur_state, input_read, next_state]);
				// If the resulting state is an accepting state, add the transition to the
				// end table
				if accept_states.contains(&next_state) {
					end.push(vec![cur_state, input_read]);
				}
			}
		}

		let state_vars = self
			.prb
			.new_int_decisions(vars.len() - 1, 1..=transitions.len() as IntVal)
			.into_iter()
			.collect_vec();

		// Add table constraint to force a transition for the starting state
		let sx: Vec<View<IntVal>> = vec![vars[0], state_vars[0]];
		self.prb.table(sx).values(start).post()?;

		// Add table constraint to force valid transition for the intermediate
		// states
		for i in 1..vars.len() - 1 {
			let mx: Vec<View<IntVal>> = vec![state_vars[i - 1], vars[i], state_vars[i]];
			self.prb.table(mx).values(middle.clone()).post()?;
		}

		// Add table constraint to force ending in an accepting state
		let ex: Vec<View<IntVal>> = vec![*state_vars.last().unwrap(), *vars.last().unwrap()];
		self.prb.table(ex).values(end).post()?;
		Ok(())
	}

	/// Ensure all variables in the FlatZinc instance output are in the model
	pub(crate) fn ensure_output(&mut self) -> Result<(), FlatZincError> {
		for out in self.fzn.output.iter() {
			match out {
				NamedRef::Variable(var) => {
					self.lookup_or_create_var(var)?;
				}
				NamedRef::Array(arr) => {
					for x in &arr.contents {
						if let Literal::Variable(var) = x {
							self.lookup_or_create_var(var)?;
						}
					}
				}
			}
		}
		Ok(())
	}

	/// Create branching specification according to the search annotations in
	/// the FlatZinc instance
	pub(crate) fn extract_branchings(&mut self) -> Result<Option<Branching>, FlatZincError> {
		let mut branchings = Vec::new();
		let mut warm_start = Vec::new();
		for ann in self.fzn.solve.ann.iter() {
			match ann {
				Annotation::Call(c) => {
					let (w, b) = self.ann_to_branchings(c)?;
					warm_start.extend(w);
					branchings.extend(b);
				}
				_ => warn!(
					target: "flatzinc",
					annotation = %ann,
					"ignore unsupported search annotation"
				),
			}
		}
		branchings.insert(0, Branching::WarmStart(warm_start));

		Ok(match branchings.len() {
			0 => None,
			1 => Some(branchings.pop().unwrap()),
			_ => Some(Branching::Seq(branchings)),
		})
	}

	/// Create branching specification according to the search annotations in
	/// the FlatZinc instance
	pub(crate) fn extract_goal(&mut self) -> Result<Option<Goal<View<IntVal>>>, FlatZincError> {
		Ok(match &self.fzn.solve.method {
			flatzinc_serde::Method::Satisfy => None,
			flatzinc_serde::Method::Minimize(lit) => Some(Goal::Minimize(self.lit_int(lit)?)),
			flatzinc_serde::Method::Maximize(lit) => Some(Goal::Maximize(self.lit_int(lit)?)),
		})
	}

	/// Preprocess a constraint in the [`FlatZinc`] instance to find variables
	/// that can be seen as views of other variables.
	///
	/// This allows us to avoid creating multiple variables that have to be kept
	/// consistent using propagators.
	fn extract_view(
		&mut self,
		defined_by: &FxHashMap<ArcKey<Variable<FznIdent>>, usize>,
		con: usize,
	) -> Result<(), FlatZincError> {
		debug_assert!(!self.processed[con]);
		let c = &self.fzn.constraints[con];

		let add_view = |me: &mut Self,
		                var: &'a Arc<Variable<FznIdent>>,
		                view: AnyView|
		 -> Result<(), FlatZincError> {
			match me.map.entry(var.cloned_key()) {
				Entry::Occupied(e) => match *e.get() {
					AnyView::Bool(bv) => {
						let AnyView::Bool(view) = view else {
							unreachable!()
						};
						bv.unify(&mut me.prb, view)?;
					}
					AnyView::Int(iv) => {
						let AnyView::Int(view) = view else {
							unreachable!()
						};
						iv.unify(&mut me.prb, view)?;
					}
				},
				Entry::Vacant(e) => {
					// Enforce the domain of the named (uncreated) variable on the view
					if let Type::Int(Some(dom)) = &var.ty {
						let AnyView::Int(view) = view else {
							unreachable!()
						};
						view.restrict_domain(&mut me.prb, dom, vec![])?;
					}
					// Insert the view to use instead of a new variable for the name
					e.insert(view);
				}
			}
			me.stats.extracted_views += 1;
			me.processed[con] = true;
			Ok(())
		};
		let arg_bool_view =
			|me: &mut Self, arg: &Argument<FznIdent>| -> Result<View<bool>, FlatZincError> {
				if let Argument::Literal(Literal::Variable(x)) = arg {
					let key = x.cloned_key();
					if !me.map.contains_key(&key)
						&& defined_by.contains_key(&key)
						&& defined_by[&key] != con
					{
						me.extract_view(defined_by, defined_by[&key])?;
					}
				}
				me.arg_bool(arg)
			};
		let lit_int_view =
			|me: &mut Self, lit: &'a Literal<FznIdent>| -> Result<View<IntVal>, FlatZincError> {
				if let Literal::Variable(x) = lit {
					let key = x.cloned_key();
					if !me.map.contains_key(&key)
						&& defined_by.contains_key(&key)
						&& defined_by[&key] != con
					{
						me.extract_view(defined_by, defined_by[&key])?;
					}
				}
				me.lit_int(lit)
			};

		let FznIdent::Known(KnownIdent::Constraint(ident)) = &c.id else {
			return Ok(()); // Bad identifier is signaled during post_constraints
		};

		match ident {
			ConstraintIdent::Bool2Int => {
				if let [b, Argument::Literal(Literal::Variable(x))] = c.args.as_slice() {
					let b = arg_bool_view(self, b)?;
					add_view(self, x, View::<IntVal>::from(b).into())?;
				}
			}
			ConstraintIdent::BoolNot => match c.args.as_slice() {
				[b, Argument::Literal(Literal::Variable(x))]
				| [Argument::Literal(Literal::Variable(x)), b] => {
					let b = arg_bool_view(self, b)?;
					add_view(self, x, (!b).into())?;
				}
				_ => {}
			},
			ConstraintIdent::IntEqReif => match c.args.as_slice() {
				[
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(x),
					Argument::Literal(Literal::Variable(r)),
				]
				| [
					Argument::Literal(x),
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(Literal::Variable(r)),
				] => {
					let x = lit_int_view(self, x)?;
					add_view(self, r, x.eq(*i).into())?;
				}
				_ => {}
			},
			ConstraintIdent::IntLeReif => match c.args.as_slice() {
				[
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(x),
					Argument::Literal(Literal::Variable(r)),
				] => {
					let x = lit_int_view(self, x)?;
					add_view(self, r, x.geq(*i).into())?;
				}
				[
					Argument::Literal(x),
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(Literal::Variable(r)),
				] => {
					let x = lit_int_view(self, x)?;
					add_view(self, r, x.leq(*i).into())?;
				}
				_ => {}
			},
			ConstraintIdent::IntNeReif => match c.args.as_slice() {
				[
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(x),
					Argument::Literal(Literal::Variable(r)),
				]
				| [
					Argument::Literal(x),
					Argument::Literal(Literal::Int(i)),
					Argument::Literal(Literal::Variable(r)),
				] => {
					let x = lit_int_view(self, x)?;
					add_view(self, r, x.ne(*i).into())?;
				}
				_ => {}
			},
			ConstraintIdent::IntLinEq
				if c.args
					.get(1)
					.map(|v| self.arg_has_length(v, 2))
					.unwrap_or(false) =>
			'int_lin_eq: {
				let [coeff, vars, sum] = c.args.as_slice() else {
					break 'int_lin_eq;
				};
				let Some(NamedRef::Variable(l)) = &c.defines else {
					break 'int_lin_eq;
				};

				let coeff = self.arg_array(coeff)?;
				let vars = self.arg_array(vars)?;
				let (c, (cy, vy)) = match vars {
					[Literal::Variable(v), y] if v.name == l.name => {
						(self.par_int(&coeff[0])?, (self.par_int(&coeff[1])?, y))
					}
					[y, Literal::Variable(v)] if v.name == l.name => {
						(self.par_int(&coeff[1])?, (self.par_int(&coeff[0])?, y))
					}
					_ => break 'int_lin_eq,
				};
				let sum = self.arg_par_int(sum)?;
				// c * l + cy * y = sum === l = (sum - cy * y) / c
				if cy % c != 0 || sum % c != 0 {
					break 'int_lin_eq;
				}
				let offset = sum / c;
				let view = if let Some(scale) = NonZero::new(-cy / c) {
					let y = lit_int_view(self, vy)?;
					y.bounding_mul(&mut self.prb, scale.get())?
						.bounding_add(&mut self.prb, offset)?
				} else {
					offset.into()
				};
				add_view(self, l, view.into())?;
			}
			_ => {}
		}
		Ok(())
	}

	/// Preprocess the [`FlatZinc`] instance to find variables that can be seen
	/// as views of other variables.
	pub(crate) fn extract_views(&mut self) -> Result<(), FlatZincError> {
		// Create a mapping from identifiers to the constraint that defines them
		let defined_by: FxHashMap<ArcKey<Variable<FznIdent>>, usize> = self
			.fzn
			.constraints
			.iter()
			.enumerate()
			.filter_map(|(i, c)| {
				if let Some(NamedRef::Variable(var)) = c.defines.as_ref() {
					Some((var.cloned_key(), i))
				} else {
					None
				}
			})
			.collect();

		// Extract views for all constraints that define an identifier
		for (i, _) in self.fzn.constraints.iter().enumerate() {
			if !self.processed[i] {
				self.extract_view(&defined_by, i)?;
			}
		}
		Ok(())
	}

	/// Finalize the builder and return the model
	pub(crate) fn finalize(mut self) -> Result<(Model, FlatZincModelMeta), FlatZincError> {
		let branching = self.extract_branchings()?;
		let goal = self.extract_goal()?;
		Ok((
			self.prb,
			FlatZincModelMeta {
				names: self.map,
				stats: self.stats,
				branching,
				goal,
				assumptions: self.assumptions,
			},
		))
	}

	/// Extract a Boolean decision variable from a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a Boolean decision variable.
	fn lit_bool(&mut self, lit: &Literal<FznIdent>) -> Result<View<bool>, FlatZincError> {
		match lit {
			Literal::Variable(var) => self.lookup_or_create_var(var).map(|mv| match mv {
				AnyView::Bool(bv) => Ok(bv.resolve_alias(&self.prb).into_inner()),
				AnyView::Int(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "bool",
					found: "int".to_owned(),
				}),
			})?,
			&Literal::Bool(v) => Ok(v.into()),
			other => Err(FlatZincError::InvalidArgumentType {
				expected: "bool",
				found: format!("{:?}", other).to_owned(),
			}),
		}
	}

	/// Extract an integer decision variable from a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not an integer decision variable.
	fn lit_int(&mut self, lit: &Literal<FznIdent>) -> Result<View<IntVal>, FlatZincError> {
		match lit {
			Literal::Variable(var) => self.lookup_or_create_var(var).map(|mv| match mv {
				AnyView::Int(iv) => Ok(iv.resolve_alias(&self.prb).into_inner()),
				AnyView::Bool(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "int",
					found: "bool".to_owned(),
				}),
			})?,
			&Literal::Bool(v) => Ok((v as IntVal).into()),
			&Literal::Int(v) => Ok(v.into()),
			other => Err(FlatZincError::InvalidArgumentType {
				expected: "int",
				found: format!("{:?}", other).to_owned(),
			}),
		}
	}

	/// Find the decision variable associated with the
	/// given identifier, or create a new one if it doesn't yet exist.
	fn lookup_or_create_var(
		&mut self,
		var: &Arc<Variable<FznIdent>>,
	) -> Result<AnyView, FlatZincError> {
		match self.map.entry(var.cloned_key()) {
			Entry::Vacant(e) => {
				let view = match &var.ty {
					Type::Bool => AnyView::Bool(self.prb.new_bool_decision()),
					Type::Int(dom) => match dom {
						Some(dom) => AnyView::Int(self.prb.new_int_decision(dom.clone())),
						None => {
							warn!(
								target: "flatzinc",
								variable = %var.name,
								min = FULL_INT_DOMAIN.start(),
								max = FULL_INT_DOMAIN.end(),
								"assume full integer domain for unbounded decision variable"
							);
							self.prb.new_int_decision(FULL_INT_DOMAIN).into()
						}
					},
					ty => panic!("Variables of {:?} are not supported", ty),
				};
				Ok(e.insert(view).clone())
			}
			Entry::Occupied(e) => Ok(e.get().clone()),
		}
	}
	/// Create a new builder to create a model from a FlatZinc instance.
	pub(crate) fn new(fzn: &'a FlatZinc<FznIdent>) -> Self {
		Self {
			fzn,
			map: FxHashMap::default(),
			prb: Model::default(),
			processed: vec![false; fzn.constraints.len()],
			stats: FlatZincStatistics::default(),
			assumptions: Vec::new(),
		}
	}

	/// Extract a Boolean parameter from a [`Literal`] in a [`FlatZinc`]
	/// instance. A [`FlatZincError::InvalidArgumentType`] will be returned if
	/// the argument was not a Boolean parameter.
	fn par_bool(&self, lit: &Literal<FznIdent>) -> Result<bool, FlatZincError> {
		match lit {
			Literal::Bool(v) => Ok(*v),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par bool",
				found: format!("{:?}", lit),
			}),
		}
	}

	/// Extract a parameter integer value from a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not an integer parameter.
	fn par_int(&self, lit: &Literal<FznIdent>) -> Result<IntVal, FlatZincError> {
		match lit {
			Literal::Bool(v) => Ok(if *v { 1 } else { 0 }),
			Literal::Int(v) => Ok(*v),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par int",
				found: format!("{:?}", lit),
			}),
		}
	}

	/// Extract a parameter integer set value from a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a parameter set.
	fn par_set(&self, lit: &Literal<FznIdent>) -> Result<IntSet, FlatZincError> {
		match lit {
			Literal::IntSet(v) => Ok(v.iter().collect()),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par set of int",
				found: format!("{:?}", lit),
			}),
		}
	}

	/// Process the [`FlatZinc::constraints`] field and add [`Constraint`] items
	/// to the [`Model`] to enforce the constraints.
	pub(crate) fn post_constraints(&mut self) -> Result<(), FlatZincError> {
		// Traditional relational constraints
		for (i, c) in self.fzn.constraints.iter().enumerate() {
			if self.processed[i] {
				continue;
			}
			let mut ann_used = vec![false; c.ann.len()];

			let FznIdent::Known(KnownIdent::Constraint(ident)) = c.id else {
				return Err(FlatZincError::UnknownConstraint(c.id.to_string()));
			};

			let num_args_err = |expected: usize| {
				Err(FlatZincError::InvalidNumArgs {
					name: ident.as_str(),
					found: c.args.len(),
					expected,
				})
			};

			match ident {
				ConstraintIdent::ArrayBoolAnd => {
					let [es, r] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let es = self.arg_array(es)?;
					let r = self.arg_bool(r)?;
					let es: Vec<_> = es
						.iter()
						.map(|l| self.lit_bool(l).map(Into::into))
						.try_collect()?;
					self.prb
						.proposition(Formula::And(es))
						.reified_by(r)
						.post()?;
				}
				ConstraintIdent::ArrayBoolXor => {
					let [es] = c.args.as_slice() else {
						return num_args_err(1);
					};
					let es = self.arg_array(es)?;
					let es: Vec<BoolFormula> = es
						.iter()
						.map(|l| self.lit_bool(l).map(Into::into))
						.try_collect()?;
					self.prb.proposition(Formula::Xor(es)).post()?;
				}
				ConstraintIdent::ArrayBoolElement => {
					let [idx, arr, val] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let arr: Vec<_> = self
						.arg_array(arr)?
						.iter()
						.map(|l| self.par_bool(l))
						.try_collect()?;
					let idx = self.arg_int(idx)?;
					let idx = idx.bounding_sub(&mut self.prb, 1)?;
					let val = self.arg_bool(val)?;
					self.prb.element(arr).index(idx).result(val).post()?;
				}
				ConstraintIdent::ArrayIntElement => {
					let [idx, arr, val] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let arr: Vec<_> = self
						.arg_array(arr)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					let idx = self.arg_int(idx)?;
					let idx = idx.bounding_sub(&mut self.prb, 1)?;
					let val = self.arg_int(val)?;

					self.prb.element(arr).index(idx).result(val).post()?;
				}
				ConstraintIdent::ArrayVarBoolElement => {
					let [idx, arr, val] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let arr = self
						.arg_array(arr)?
						.iter()
						.map(|l| self.lit_bool(l))
						.try_collect()?;
					let idx = self.arg_int(idx)?;
					let idx = idx.bounding_sub(&mut self.prb, 1)?;
					let val = self.arg_bool(val)?;

					self.prb.element(arr).index(idx).result(val).post()?;
				}
				ConstraintIdent::ArrayVarIntElement => {
					let [idx, arr, val] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let arr: Vec<_> = self
						.arg_array(arr)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let idx = self.arg_int(idx)?;
					let idx = idx.bounding_sub(&mut self.prb, 1)?;
					let val = self.arg_int(val)?;

					self.prb.element(arr).index(idx).result(val).post()?;
				}
				ConstraintIdent::Assume => {
					let [arr] = c.args.as_slice() else {
						return num_args_err(1);
					};
					// Resolve every element to a model-level Boolean view, pairing
					// each view with a human-readable label that the CLI can print
					// when the assumption ends up in an UNSAT core.
					//
					// For variables we use the FlatZinc identifier. For static `false`
					// literals we keep the textual constant, so the user can see when a
					// static `false` was passed in. `true` literals are ignored.
					let arr = self.arg_array(arr)?;
					self.assumptions.reserve(arr.len());
					for l in arr {
						let label = match l {
							Literal::Variable(v) => v.name.clone(),
							Literal::Bool(true) => continue,
							Literal::Bool(false) => "false".to_owned(),
							l => {
								return Err(FlatZincError::InvalidArgumentType {
									expected: "bool",
									found: format!("{:?}", l),
								});
							}
						};
						let view = self.lit_bool(l)?;
						self.assumptions.push((label, view));
					}
				}
				ConstraintIdent::Bool2Int => {
					let [b, i] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let b = self.arg_bool(b)?;
					let i = self.arg_int(i)?;
					i.unify(&mut self.prb, b)?;
				}
				ConstraintIdent::BoolLinEq => {
					let [coeffs, vars, sum] = c.args.as_slice() else {
						return num_args_err(3);
					};

					let coeffs: Vec<_> = self
						.arg_array(coeffs)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					let vars: Vec<_> = self
						.arg_array(vars)?
						.iter()
						.map(|l| self.lit_bool(l))
						.try_collect()?;
					let sum = self.arg_int(sum)?;

					let mut terms = Vec::with_capacity(vars.len() + 1);
					for (x, c) in vars.into_iter().zip(coeffs) {
						if let Some(c) = NonZero::new(c) {
							terms.push(View::from(x).bounding_mul(&mut self.prb, c.get())?);
						}
					}
					terms.push(-sum);
					let lin_exp: IntLinearExp = terms.into_iter().sum();

					self.prb.linear(lin_exp).eq(0).post()?;
				}
				ConstraintIdent::BoolClause => {
					let [pos, neg] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let pos = self.arg_array(pos)?;
					let neg = self.arg_array(neg)?;
					let mut lits = Vec::with_capacity(pos.len() + neg.len());
					let mut satisfied = false;
					for lit in pos
						.iter()
						.map(|l| self.lit_bool(l))
						.collect_vec()
						.into_iter()
						.chain(neg.iter().map(|l| self.lit_bool(l).map(Not::not)))
					{
						match lit?.0 {
							BoolView::Const(true) => {
								satisfied = true;
								break;
							}
							BoolView::Const(false) => {}
							x => lits.push(View(x)),
						}
					}
					if !satisfied {
						match lits.len() {
							0 => {
								return Err(FlatZincError::ReformulationError(
									LoweringError::Simplification(self.prb.declare_conflict([])),
								));
							}
							1 => lits[0].require(&mut self.prb, vec![])?,
							_ => {
								self.prb
									.proposition(Formula::Or(lits.into_iter().map_into().collect()))
									.post()?;
							}
						}
					}
				}
				ConstraintIdent::BoolEqReif => {
					let [a, b, r] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let a = self.arg_bool(a)?;
					let b = self.arg_bool(b)?;
					let r = self.arg_bool(r)?;
					self.prb
						.proposition(Formula::Equiv(vec![a.into(), b.into()]))
						.reified_by(r)
						.post()?;
				}
				ConstraintIdent::BoolNot => {
					let [a, b] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let a = self.arg_bool(a)?;
					let b = self.arg_bool(b)?;
					a.unify(&mut self.prb, !b)?;
				}
				ConstraintIdent::BoolXor => {
					let [a, b, rest @ ..] = c.args.as_slice() else {
						return num_args_err(2);
					};
					if rest.len() > 1 {
						return num_args_err(3);
					}
					let a = self.arg_bool(a)?;
					let b = self.arg_bool(b)?;
					let mut f = Formula::Xor(vec![a.into(), b.into()]);
					if let [r] = rest {
						let r = self.arg_bool(r)?;
						f = Formula::Equiv(vec![r.into(), f]);
					}
					self.prb.proposition(f).post()?;
				}
				ConstraintIdent::DiffnInt { strict } => {
					let [x, y, dx, dy] = c.args.as_slice() else {
						return num_args_err(4);
					};
					let origins: Result<_, FlatZincError> = self
						.arg_array(x)?
						.iter()
						.zip(self.arg_array(y)?)
						.map(|(x, y)| Ok(vec![self.lit_int(x)?, self.lit_int(y)?]))
						.try_collect();
					let sizes: Result<_, FlatZincError> = self
						.arg_array(dx)?
						.iter()
						.zip(self.arg_array(dy)?)
						.map(|(dx, dy)| Ok(vec![self.lit_int(dx)?, self.lit_int(dy)?]))
						.try_collect();

					self.prb
						.no_overlap()
						.origins(origins?)
						.sizes(sizes?)
						.strict(strict)
						.post()?;
				}
				ConstraintIdent::DiffnKInt { strict } => {
					let [box_posn, box_size, d] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let dimensions = usize::try_from(self.arg_par_int(d)?).map_err(|_| {
						FlatZincError::InvalidArgumentType {
							expected: "positive integer",
							found: d.to_string(),
						}
					})?;
					let flat_start_pos = self.arg_array(box_posn)?;
					let flat_start_pos: Vec<_> = flat_start_pos
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let flat_sizes = self.arg_array(box_size)?;
					let flat_sizes: Vec<_> =
						flat_sizes.iter().map(|l| self.lit_int(l)).try_collect()?;

					if dimensions == 0
						|| flat_start_pos.len() != flat_sizes.len()
						|| flat_start_pos.len() % dimensions != 0
					{
						return Err(FlatZincError::InvalidArgumentType {
							expected: "flattened object-major arrays with a positive number of dimensions",
							found: format!(
								"box_posn length {}, box_size length {}, dimensions {}",
								flat_start_pos.len(),
								flat_sizes.len(),
								dimensions
							),
						});
					}
					let origins: Vec<Vec<_>> = flat_start_pos
						.chunks_exact(dimensions)
						.map(|chunk| chunk.to_vec())
						.collect();
					let sizes: Vec<Vec<_>> = flat_sizes
						.chunks_exact(dimensions)
						.map(|chunk| chunk.to_vec())
						.collect();

					self.prb
						.no_overlap()
						.origins(origins)
						.sizes(sizes)
						.strict(strict)
						.post()?;
				}
				ConstraintIdent::AllDifferentInt => {
					let [args] = c.args.as_slice() else {
						return num_args_err(1);
					};
					let args = self.arg_array(args)?;
					let args: Vec<_> = args.iter().map(|l| self.lit_int(l)).try_collect()?;
					let (bounds, value, domain) = match (
						Self::anns_contains(
							&c.ann,
							&mut ann_used,
							AnnotationIdent::ConsistencyBounds,
						),
						Self::anns_contains(
							&c.ann,
							&mut ann_used,
							AnnotationIdent::ConsistencyValue,
						),
						Self::anns_contains(
							&c.ann,
							&mut ann_used,
							AnnotationIdent::ConsistencyDomain,
						),
					) {
						(false, false, false) => (None, None, None),
						(bounds, value, domain) => (Some(bounds), Some(value), Some(domain)),
					};
					self.prb
						.unique(args)
						.maybe_bounds_propagation(bounds)
						.maybe_value_propagation(value)
						.maybe_domain_propagation(domain)
						.post()?;
				}
				ConstraintIdent::ArrayIntMaximum | ConstraintIdent::ArrayIntMinimum => {
					let [m, args] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let args: Vec<_> = self
						.arg_array(args)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let m = self.arg_int(m)?;
					match ident {
						ConstraintIdent::ArrayIntMaximum => self.prb.maximum(args).result(m).post(),
						ConstraintIdent::ArrayIntMinimum => self.prb.minimum(args).result(m).post(),
						_ => unreachable!(),
					}?;
				}
				ConstraintIdent::BoolClauseReif => {
					let [pos, neg, r] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let pos = self.arg_array(pos)?;
					let neg = self.arg_array(neg)?;
					let r = self.arg_bool(r)?;
					let mut lits = Vec::with_capacity(pos.len() + neg.len());
					for l in pos {
						let e = self.lit_bool(l)?;
						lits.push(e.into());
					}
					for l in neg {
						let e = self.lit_bool(l)?;
						lits.push((!e).into());
					}
					self.prb
						.proposition(Formula::Or(lits))
						.reified_by(r)
						.post()?;
				}
				ConstraintIdent::Cumulative => {
					let [starts, durations, heights, r] = c.args.as_slice() else {
						return num_args_err(4);
					};
					let starts = self
						.arg_array(starts)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let durations = self
						.arg_array(durations)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let heights = self
						.arg_array(heights)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let r = self.arg_int(r)?;
					self.prb
						.cumulative()
						.start_times(starts)
						.durations(durations)
						.usages(heights)
						.capacity(r)
						.maybe_ttef_check_propagation(Some(true))
						.maybe_ttef_filtering_propagation(Some(false))
						.maybe_ttef_opportunistic_propagation(Some(false))
						.post()?;
				}
				ConstraintIdent::DisjuctiveStrict => {
					let [starts, durations] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let start_times = self
						.arg_array(starts)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let durations = self
						.arg_array(durations)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;

					let (edge_finding, not_last, detectable_precedence) = match (
						Self::anns_contains(
							&c.ann,
							&mut ann_used,
							AnnotationIdent::DisjEdgeFinding,
						),
						Self::anns_contains(&c.ann, &mut ann_used, AnnotationIdent::DisjNotLast),
						Self::anns_contains(&c.ann, &mut ann_used, AnnotationIdent::DisjDetectPrec),
					) {
						// No annotations found, so we assume the user wants the default
						// configuration
						(false, false, false) => (None, None, None),
						// At least one annotation was found, so we assume missing annotations
						// disable certain propagation options.
						(ef, nl, dp) => (Some(ef), Some(nl), Some(dp)),
					};

					self.prb
						.disjunctive()
						.start_times(start_times)
						.durations(durations)
						.maybe_edge_finding_propagation(edge_finding)
						.maybe_not_last_propagation(not_last)
						.maybe_detectable_precedence_propagation(detectable_precedence)
						.post()?;
				}
				ConstraintIdent::Regular => {
					let [x, q, s, d, q0, f] = c.args.as_slice() else {
						return num_args_err(6);
					};
					let x: Vec<_> = self
						.arg_array(x)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;

					let q = self.arg_par_int(q)?;
					let s = self.arg_par_int(s)?;
					let d: Vec<_> = self
						.arg_array(d)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					if d.len() != (q * s) as usize {
						return Err(FlatZincError::InvalidArgumentType {
							expected: "array with an element for each combination of state and input value",
							found: format!(
								"array of size {}, for {q} states and {s} input values",
								d.len()
							),
						});
					}
					let d: Vec<Vec<_>> = d
						.into_iter()
						.chunks(s as usize)
						.into_iter()
						.map(|c| c.collect())
						.collect();
					debug_assert!(d.last().map(|t| t.len() == s as usize).unwrap_or(true));

					let q0 = self.arg_par_int(q0)?;
					let f = self.arg_par_set(f)?;
					let f: FxHashSet<IntVal> = f.iter().flat_map(|r| r.into_iter()).collect();

					// Convert regular constraint in to table constraints and add them to the
					// model
					self.convert_regular_to_tables(x, d, q0, f)
						.map_err(FlatZincError::from)?;
				}
				ConstraintIdent::TableInt => {
					let [args, table] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let args = self.arg_array(args)?;
					let args: Vec<_> = args.iter().map(|l| self.lit_int(l)).try_collect()?;
					let table = self.arg_array(table)?;
					let table: Vec<_> = table.iter().map(|l| self.par_int(l)).try_collect()?;
					if args.is_empty() || (table.len() % args.len()) != 0 {
						return Err(FlatZincError::InvalidArgumentType {
							expected: "array of n integers, where n is divisible by the number of variables",
							found: format!(
								"array of {} integers, to give values to {} variables",
								table.len(),
								args.len()
							),
						});
					}
					if table.is_empty() {
						return Err(FlatZincError::ReformulationError(
							LoweringError::Simplification(self.prb.declare_conflict([])),
						));
					}
					let table: Vec<Vec<_>> = table
						.into_iter()
						.chunks(args.len())
						.into_iter()
						.map(|c| c.collect())
						.collect();
					self.prb.table(args).values(table).post()?;
				}
				ConstraintIdent::SeqPrecedeChainInt => {
					let [args] = c.args.as_slice() else {
						return num_args_err(1);
					};
					let args = self.arg_array(args)?;
					let args: Vec<_> = args.iter().map(|l| self.lit_int(l)).try_collect()?;
					self.prb.value_precede(args).post()?;
				}
				ConstraintIdent::ValuePrecedeChain => {
					let [values, variables] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let values: Vec<_> = self
						.arg_array(values)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					let variables: Vec<_> = self
						.arg_array(variables)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					self.prb.value_precede(variables).values(values).post()?;
				}
				ConstraintIdent::IntAbs => {
					let [origin, abs] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let origin = self.arg_int(origin)?;
					let abs = self.arg_int(abs)?;
					self.prb.abs(origin).result(abs).post()?;
				}
				ConstraintIdent::IntDiv => {
					let [num, denom, res] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let num = self.arg_int(num)?;
					let denom = self.arg_int(denom)?;
					let res = self.arg_int(res)?;
					self.prb.div(num, denom).result(res).post()?;
				}
				ConstraintIdent::IntLe | ConstraintIdent::IntNe => {
					let [a, b] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let a = self.arg_int(a)?;
					let b = self.arg_int(b)?;
					let lin = self.prb.linear(a);
					match ident {
						ConstraintIdent::IntLe => lin.le(b),
						ConstraintIdent::IntNe => lin.ne(b),
						_ => unreachable!(),
					}
					.post()?;
				}
				ConstraintIdent::IntEqImp
				| ConstraintIdent::IntEqReif
				| ConstraintIdent::IntLeImp
				| ConstraintIdent::IntLeReif
				| ConstraintIdent::IntNeImp
				| ConstraintIdent::IntNeReif => {
					let [a, b, r] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let a = self.arg_int(a)?;
					let b = self.arg_int(b)?;
					let r = self.arg_bool(r)?;

					let lin = self.prb.linear(a);
					let lin = match ident {
						ConstraintIdent::IntEqImp | ConstraintIdent::IntEqReif => lin.eq(b),
						ConstraintIdent::IntLeImp | ConstraintIdent::IntLeReif => lin.le(b),
						ConstraintIdent::IntNeImp | ConstraintIdent::IntNeReif => lin.ne(b),
						_ => unreachable!(),
					};
					match ident {
						ConstraintIdent::IntEqImp
						| ConstraintIdent::IntLeImp
						| ConstraintIdent::IntNeImp => lin.implied_by(r),
						ConstraintIdent::IntEqReif
						| ConstraintIdent::IntLeReif
						| ConstraintIdent::IntNeReif => lin.reified_by(r),
						_ => unreachable!(),
					}
					.post()?;
				}
				ConstraintIdent::IntLinEq
				| ConstraintIdent::IntLinLe
				| ConstraintIdent::IntLinNe => {
					let [coeffs, vars, rhs] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let coeffs: Vec<_> = self
						.arg_array(coeffs)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					let vars: Vec<_> = self
						.arg_array(vars)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let rhs = self.arg_par_int(rhs)?;
					let mut terms = Vec::with_capacity(vars.len());
					for (x, c) in vars.into_iter().zip(coeffs) {
						terms.push(x.bounding_mul(&mut self.prb, c)?);
					}
					let lin_exp: IntLinearExp = terms.into_iter().sum();
					let lin = self.prb.linear(lin_exp);

					match ident {
						ConstraintIdent::IntLinEq => lin.eq(rhs),
						ConstraintIdent::IntLinLe => lin.le(rhs),
						ConstraintIdent::IntLinNe => lin.ne(rhs),
						_ => unreachable!(),
					}
					.post()?;
				}
				ConstraintIdent::IntLinEqImp
				| ConstraintIdent::IntLinEqReif
				| ConstraintIdent::IntLinLeImp
				| ConstraintIdent::IntLinLeReif
				| ConstraintIdent::IntLinNeImp
				| ConstraintIdent::IntLinNeReif => {
					let [coeffs, vars, rhs, reified] = c.args.as_slice() else {
						return num_args_err(4);
					};
					let coeffs: Vec<_> = self
						.arg_array(coeffs)?
						.iter()
						.map(|l| self.par_int(l))
						.try_collect()?;
					let vars: Vec<_> = self
						.arg_array(vars)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let rhs = self.arg_par_int(rhs)?;
					let reified = self.arg_bool(reified)?;
					let mut terms = Vec::with_capacity(vars.len());
					for (x, c) in vars.into_iter().zip(coeffs) {
						terms.push(x.bounding_mul(&mut self.prb, c)?);
					}

					let lin = self.prb.linear(terms.into_iter().sum::<IntLinearExp>());
					let lin = match ident {
						ConstraintIdent::IntLinEqImp | ConstraintIdent::IntLinEqReif => lin.eq(rhs),
						ConstraintIdent::IntLinLeImp | ConstraintIdent::IntLinLeReif => lin.le(rhs),
						ConstraintIdent::IntLinNeImp | ConstraintIdent::IntLinNeReif => lin.ne(rhs),
						_ => unreachable!(),
					};
					match ident {
						ConstraintIdent::IntLinEqImp
						| ConstraintIdent::IntLinLeImp
						| ConstraintIdent::IntLinNeImp => lin.implied_by(reified),
						ConstraintIdent::IntLinEqReif
						| ConstraintIdent::IntLinLeReif
						| ConstraintIdent::IntLinNeReif => lin.reified_by(reified),
						_ => unreachable!(),
					}
					.post()?;
				}
				ConstraintIdent::IntMax | ConstraintIdent::IntMin => {
					let [a, b, m] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let a = self.arg_int(a)?;
					let b = self.arg_int(b)?;
					let m = self.arg_int(m)?;
					match ident {
						ConstraintIdent::IntMax => self.prb.maximum([a, b]).result(m).post(),
						ConstraintIdent::IntMin => self.prb.minimum([a, b]).result(m).post(),
						_ => unreachable!(),
					}?;
				}
				ConstraintIdent::IntPow => {
					let [base, exponent, res] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let base = self.arg_int(base)?;
					let exponent = self.arg_int(exponent)?;
					let res = self.arg_int(res)?;

					self.prb.pow(base, exponent).result(res).post()?;
				}
				ConstraintIdent::IntTimes => {
					let [x, y, z] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let a = self.arg_int(x)?;
					let b = self.arg_int(y)?;
					let m = self.arg_int(z)?;
					self.prb.mul(a, b).result(m).post()?;
				}
				ConstraintIdent::SetIn => {
					let [x, s] = c.args.as_slice() else {
						return num_args_err(2);
					};
					let x = self.arg_int(x)?;
					let s = self.arg_par_set(s)?;

					x.restrict_domain(&mut self.prb, &s, vec![])?;
				}
				ConstraintIdent::SetInReif => {
					let [x, s, r] = c.args.as_slice() else {
						return num_args_err(3);
					};
					let x = self.arg_int(x)?;
					let s = self.arg_par_set(s)?;
					let r = self.arg_bool(r)?;

					self.prb.contains(s).member(x).result(r).post()?;
				}
				ConstraintIdent::IntEq | ConstraintIdent::BoolEq => unreachable!(),
			}
			for (i, used) in ann_used.iter().enumerate() {
				if !used {
					warn!(
						target: "flatzinc",
						annotation = %c.ann[i],
						constraint = %c.id,
						"ignore unsupported constraint annotation"
					);
				}
			}
		}

		Ok(())
	}

	/// Unify variables in the [`Model`] that are know to be equivalent.
	///
	/// This can happen because of `bool_eq` and `int_eq` constraints in the
	/// [`FlatZinc`] instance, or because of the `rhs` property of a variable.
	pub(crate) fn unify_variables(&mut self) -> Result<(), FlatZincError> {
		let mut unify_map =
			FxHashMap::<ArcKey<Variable<FznIdent>>, Rc<RefCell<Vec<Literal<FznIdent>>>>>::default();
		let unify_map_find =
			|map: &FxHashMap<ArcKey<Variable<FznIdent>>, Rc<RefCell<Vec<Literal<FznIdent>>>>>,
			 a: &Literal<FznIdent>| {
				if let Literal::Variable(x) = a {
					map.get(&x.cloned_key()).map(Rc::clone)
				} else {
					None
				}
			};

		let record_unify = |map: &mut FxHashMap<
			ArcKey<Variable<FznIdent>>,
			Rc<RefCell<Vec<Literal<FznIdent>>>>,
		>,
		                    a: &Literal<FznIdent>,
		                    b: &Literal<FznIdent>| {
			let a_set = unify_map_find(map, a);
			let b_set = unify_map_find(map, b);
			match (a_set, b_set) {
				(Some(a_set), Some(b_set)) => {
					if Rc::ptr_eq(&a_set, &b_set) {
						return;
					}
					let mut members = (*a_set).borrow_mut();
					members.extend(b_set.take());
					for b in members.iter() {
						if let Literal::Variable(b) = b {
							map.insert(b.cloned_key(), Rc::clone(&a_set));
						}
					}
				}
				(Some(a_set), None) => {
					let mut members = (*a_set).borrow_mut();
					members.push(b.clone());
					if let Literal::Variable(b) = b {
						map.insert(b.cloned_key(), Rc::clone(&a_set));
					}
				}
				(None, Some(b_set)) => {
					let mut members = (*b_set).borrow_mut();
					members.push(a.clone());
					if let Literal::Variable(a) = a {
						map.insert(a.cloned_key(), Rc::clone(&b_set));
					}
				}
				(None, None) => {
					let n_set = Rc::new(RefCell::new(vec![a.clone(), b.clone()]));
					if let Literal::Variable(a) = a {
						map.insert(a.cloned_key(), Rc::clone(&n_set));
					}
					if let Literal::Variable(b) = b {
						map.insert(b.cloned_key(), n_set);
					}
				}
			};
		};

		// Unify variables based on constraints
		for (i, c) in self.fzn.constraints.iter().enumerate() {
			if self.processed[i] {
				continue;
			}
			let FznIdent::Known(KnownIdent::Constraint(ident)) = c.id else {
				continue;
			};
			let mark_processed = |me: &mut Self| me.processed[i] = true;
			match ident {
				ConstraintIdent::BoolEq => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed(self);
					}
				}
				ConstraintIdent::IntEq => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed(self);
					}
				}
				ConstraintIdent::ArrayBoolElement
				| ConstraintIdent::ArrayIntElement
				| ConstraintIdent::ArrayVarBoolElement
				| ConstraintIdent::ArrayVarIntElement => {
					if let [idx, arr, Argument::Literal(b)] = c.args.as_slice() {
						let arr = self.arg_array(arr)?;
						// unify if the index is constants
						if let Argument::Literal(Literal::Int(idx)) = idx {
							let a = &arr[(idx - 1) as usize];
							record_unify(&mut unify_map, a, b);
							mark_processed(self);
						}
						// unify if all values in arr are equal
						if !arr.is_empty() && arr.iter().all_equal() {
							record_unify(&mut unify_map, &arr[0], b);
							mark_processed(self);
						}
					}
				}
				_ => {}
			}
		}

		#[expect(clippy::iter_over_hash_type, reason = "FxHashMap::iter is stable")]
		for (k, li) in unify_map.iter() {
			let li = li.borrow();
			if self.map.contains_key(k) {
				continue;
			}
			let is_bool = li.first().is_some_and(|l| match l {
				Literal::Variable(var) => var.ty == Type::Bool,
				Literal::Bool(_) => true,
				_ => false,
			});
			// Determine the domain of the list of literals
			let domain: Option<Literal<()>> = if is_bool {
				let mut domain = None;
				for lit in li.iter() {
					match lit {
						Literal::Bool(b) => {
							if domain == Some(!b) {
								return Err(FlatZincError::ReformulationError(
									LoweringError::Simplification(self.prb.declare_conflict([])),
								));
							} else {
								domain = Some(*b);
							}
						}
						Literal::Variable(_) => {}
						_ => unreachable!(),
					};
				}
				domain.map(Literal::Bool)
			} else {
				let mut domain = None::<IntSet>;
				for lit in li.iter() {
					match lit {
						Literal::Int(i) => {
							let rl = (*i..=*i).into();
							if let Some(dom) = domain {
								domain = Some(dom.intersect(&rl));
							} else {
								domain = Some(rl);
							}
						}
						Literal::Variable(var) => {
							if let Type::Int(Some(d)) = &var.ty {
								if let Some(dom) = domain {
									domain = Some(dom.intersect(d));
								} else {
									domain = Some(d.clone());
								}
							}
						}
						_ => unreachable!(),
					};
				}
				domain.map(Literal::IntSet)
			};
			// Find any view that is part of a unified group
			let var = li
				.iter()
				.find_map(|lit| -> Option<AnyView> {
					if let Literal::Variable(v) = lit {
						self.map.get(&v.cloned_key()).cloned()
					} else {
						None
					}
				})
				// Create a new variable if no view is found
				.unwrap_or_else(|| match domain {
					Some(Literal::Bool(b)) => View::<bool>::from(b).into(),
					Some(Literal::IntSet(dom)) => self.prb.new_int_decision(dom).into(),
					Some(_) => unreachable!(),
					None => {
						if is_bool {
							self.prb.new_bool_decision().into()
						} else {
							let var = li
								.iter()
								.find_map(|lit| {
									if let Literal::Variable(var) = lit {
										Some(var)
									} else {
										None
									}
								})
								.unwrap();
							warn!(
								target: "flatzinc",
								variable = %var.name,
								min = FULL_INT_DOMAIN.start(),
								max = FULL_INT_DOMAIN.end(),
								"assume full integer domain for unbounded decision variable"
							);
							self.prb.new_int_decision(FULL_INT_DOMAIN).into()
						}
					}
				});

			// Map (or equate) all names in the group to the new variable
			for lit in li.iter() {
				if let Literal::Variable(v) = lit {
					let prev = self.map.insert(v.cloned_key(), var.clone());
					debug_assert_eq!(prev, None);
				}
			}
		}
		Ok(())
	}
}

impl Display for KnownIdent {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Annotation(ident) => Display::fmt(ident, f),
			Self::Constraint(ident) => Display::fmt(ident, f),
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::model::deserialize::flatzinc::{
		AnnotationIdent, ConstraintIdent, FznIdent, KnownIdent,
	};

	#[test]
	fn annotation_ident_display_roundtrips() {
		let ident = AnnotationIdent::DisjDetectPrec;
		assert_eq!(ident.to_string(), "detectable_precedence");
		assert_eq!(
			AnnotationIdent::try_from(ident.to_string().as_str()),
			Ok(AnnotationIdent::DisjDetectPrec)
		);
		let ident = AnnotationIdent::WarmStartInt;
		assert_eq!(ident.to_string(), "warm_start_int");
		assert_eq!(
			AnnotationIdent::try_from(ident.to_string().as_str()),
			Ok(AnnotationIdent::WarmStartInt)
		);
	}

	#[test]
	fn annotation_ident_try_from() {
		assert_eq!(
			AnnotationIdent::try_from("bounds"),
			Ok(AnnotationIdent::ConsistencyBounds)
		);
		assert_eq!(
			AnnotationIdent::try_from("bool_search"),
			Ok(AnnotationIdent::BoolSearch)
		);
		assert_eq!(
			AnnotationIdent::try_from("input_order"),
			Ok(AnnotationIdent::VarSelInputOrder)
		);
		assert_eq!(
			AnnotationIdent::try_from("indomain_max"),
			Ok(AnnotationIdent::ValSelIndomainMax)
		);
		assert_eq!(AnnotationIdent::try_from("unknown_annotation"), Err(()));
	}

	#[test]
	fn constraint_ident_display_roundtrips() {
		let ident = ConstraintIdent::DiffnKInt { strict: false };
		assert_eq!(ident.to_string(), "huub_diffn_nonstrict_k_int");
		assert_eq!(
			ConstraintIdent::try_from(ident.to_string().as_str()),
			Ok(ConstraintIdent::DiffnKInt { strict: false })
		);
	}

	#[test]
	fn constraint_ident_try_from() {
		assert_eq!(
			ConstraintIdent::try_from("int_div"),
			Ok(ConstraintIdent::IntDiv)
		);
		assert_eq!(ConstraintIdent::try_from("unknown_constraint"), Err(()));
	}

	#[test]
	fn fzn_ident_display_roundtrips() {
		let known = FznIdent::from("int_div");
		assert_eq!(known.to_string(), "int_div");
		let unknown = FznIdent::from("not_a_known_identifier");
		assert_eq!(unknown.to_string(), "not_a_known_identifier");
	}

	#[test]
	fn ident_size() {
		assert_eq!(size_of::<FznIdent>(), size_of::<Box<str>>());
	}

	#[test]
	fn parses_known_identifiers() {
		assert_eq!(
			FznIdent::from("int_div"),
			FznIdent::Known(KnownIdent::Constraint(ConstraintIdent::IntDiv))
		);
		assert_eq!(
			FznIdent::from("value_propagation"),
			FznIdent::Known(KnownIdent::Annotation(AnnotationIdent::ConsistencyValue))
		);
		assert_eq!(
			FznIdent::from("huub_diffn_k_int"),
			FznIdent::Known(KnownIdent::Constraint(ConstraintIdent::DiffnKInt {
				strict: true
			}))
		);
		assert_eq!(
			FznIdent::from("huub_diffn_nonstrict_k_int"),
			FznIdent::Known(KnownIdent::Constraint(ConstraintIdent::DiffnKInt {
				strict: false
			}))
		);
		assert_eq!(
			FznIdent::from("bool_search"),
			FznIdent::Known(KnownIdent::Annotation(AnnotationIdent::BoolSearch))
		);
		assert_eq!(
			FznIdent::from("outdomain_min"),
			FznIdent::Known(KnownIdent::Annotation(AnnotationIdent::ValSelOutdomainMin))
		);
	}

	#[test]
	fn preserves_unknown_identifiers() {
		let FznIdent::Unknown(ident) = FznIdent::from("not_a_known_identifier") else {
			unreachable!()
		};
		assert_eq!(&*ident, "not_a_known_identifier");
	}
}
