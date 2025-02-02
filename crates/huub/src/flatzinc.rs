//! Module for the creation of a [`Model`] from a [`FlatZinc`] instance.

use std::{
	cell::RefCell,
	collections::{hash_map::Entry, HashMap, HashSet},
	fmt::{Debug, Display},
	hash::Hash,
	iter::once,
	ops::Deref,
	rc::Rc,
};

use flatzinc_serde::{
	Annotation, AnnotationArgument, AnnotationCall, AnnotationLiteral, Argument, Domain, FlatZinc,
	Literal, Type,
};
use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::IntervalIterator;
use thiserror::Error;
use tracing::warn;

use crate::{
	abs_int, actions::SimplificationActions, all_different_int, array_element, array_maximum_int,
	array_minimum_int, constraints::int_table::IntTable, disjunctive_strict, div_int,
	int_in_set_reif, pow_int, reformulate::ReformulationError, table_int, times_int, BoolDecision,
	Branching, Decision, IntDecision, IntDecisionInner, IntLinExpr, IntSetVal, IntVal, Model,
	NonZeroIntVal, ValueSelection, VariableSelection,
};

#[derive(Error, Debug)]
/// Errors that can occur when converting a [`FlatZinc`] instance to a [`Model`]
/// or [`Solver`] object.
pub enum FlatZincError {
	#[error("{0:?} type variables are not supported by huub")]
	/// FlatZinc instance contained a decision variable with an unsupported type.
	UnsupportedType(Type),
	#[error("constraint cannot be constructed using unknown identifier `{0}'")]
	/// FlatZinc instance contained a constraint with an unknown identifier.
	UnknownConstraint(String),
	#[error("constraints with identifiers `{name}' must have {expected} arguments, found {found}")]
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
	#[error("could not find identifier `{0}'")]
	/// FlatZinc instance used an identifier that was not defined.
	UnknownIdentifier(String),
	#[error("argument found of type `{found}', expected `{expected}'")]
	/// FlatZinc constraint or annotation used an argument of the wrong type.
	InvalidArgumentType {
		/// Expected type of the argument.
		expected: &'static str,
		/// Type of the argument found.
		found: String,
	},
	#[error("error reformulating generated model `{0}'")]
	/// Error that occorred when converting a generated [`Model`] to a [`Solver`]
	/// object.
	ReformulationError(#[from] ReformulationError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// Statistical information about the extraction process that creates a
/// [`Model`] from a [`FlatZinc`] instance.
pub struct FlatZincStatistics {
	/// Number of literal views extracted from the FlatZinc specification
	extracted_views: u32,
	/// Number of variables removed by unification
	vars_unified: u32,
}

/// Builder for creating a model from a FlatZinc instance
pub(crate) struct FznModelBuilder<'a, S: Eq + Hash + Ord> {
	/// The FlatZinc instance to build the model from
	fzn: &'a FlatZinc<S>,
	/// A mapping from FlatZinc identifiers to model views
	map: HashMap<S, Decision>,
	/// The incumbent model
	prb: Model,
	/// Flags indicating which constraints have been processed
	processed: Vec<bool>,
	/// Statistics about the extraction process
	stats: FlatZincStatistics,
}

impl FlatZincStatistics {
	/// Returns the number of views extracted from the FlatZinc instance
	///
	/// Views currently creates the following types of views:
	/// - literal views (i.e., direct use of literals used to as part of variable
	///   representation instead of reified constraints)
	/// - linear views (i.e., scaled and offset views of integer variables)
	/// - Boolean linear views (i.e., scaled and offset views of Boolean
	///   variables, able to represent any integer value with two values)
	pub fn extracted_views(&self) -> u32 {
		self.extracted_views
	}

	/// Returns the number of variables removed by unification
	pub fn unified_variables(&self) -> u32 {
		self.vars_unified
	}
}

impl<'a, S> FznModelBuilder<'a, S>
where
	S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
{
	/// Extract a [`Vec<Literal>`] from an [`AnnotationArgument`].
	fn ann_arg_var_array(
		&self,
		arg: &'a AnnotationArgument<S>,
	) -> Result<Vec<Literal<S>>, FlatZincError> {
		match arg {
			AnnotationArgument::Array(x) => Ok(x
				.iter()
				.filter_map(|l| {
					if let AnnotationLiteral::BaseLiteral(l) = l {
						Some(l.clone())
					} else {
						None
					}
				})
				.collect()),
			AnnotationArgument::Literal(AnnotationLiteral::BaseLiteral(Literal::Identifier(
				ident,
			))) => {
				if let Some(arr) = self.fzn.arrays.get(ident) {
					Ok(arr.contents.clone())
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "identifier",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Process a [`AnnotationCall`] expected to contain a search selection
	/// strategy, and return a tuple containing (1) the general search strategy,
	/// and (2) the warm start instructions.
	fn ann_to_branchings(
		&mut self,
		c: &'a AnnotationCall<S>,
	) -> Result<(Vec<BoolDecision>, Vec<Branching>), FlatZincError> {
		match c.id.deref() {
			"bool_search" => {
				if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
					let vars = self
						.ann_arg_var_array(vars)?
						.iter()
						.map(|l| self.lit_bool(l))
						.try_collect()?;
					let var_sel = Self::ann_var_sel(var_sel)?;
					let val_sel = Self::ann_val_sel(val_sel)?;

					Ok((Vec::new(), vec![Branching::Bool(vars, var_sel, val_sel)]))
				} else {
					Err(FlatZincError::InvalidNumArgs {
						name: "bool_search",
						found: c.args.len(),
						expected: 4,
					})
				}
			}
			"int_search" => {
				if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
					let vars = self
						.ann_arg_var_array(vars)?
						.iter()
						.map(|l| self.lit_int(l))
						.try_collect()?;
					let var_sel = Self::ann_var_sel(var_sel)?;
					let val_sel = Self::ann_val_sel(val_sel)?;

					Ok((Vec::new(), vec![Branching::Int(vars, var_sel, val_sel)]))
				} else {
					Err(FlatZincError::InvalidNumArgs {
						name: "int_search",
						found: c.args.len(),
						expected: 4,
					})
				}
			}
			"seq_search" | "warm_start_array" => {
				if let [AnnotationArgument::Array(searches)] = c.args.as_slice() {
					let mut warm_start = Vec::new();
					let mut branchings = Vec::new();
					for ann in searches {
						match ann {
							AnnotationLiteral::Annotation(Annotation::Call(sub_call)) => {
								let (w, b) = self.ann_to_branchings(sub_call)?;
								warm_start.extend(w);
								branchings.extend(b);
							}
							_ => warn!("unsupported search annotation: {}", ann),
						}
					}
					Ok((warm_start, branchings))
				} else {
					Err(FlatZincError::InvalidNumArgs {
						name: if c.id.deref() == "seq_search" {
							"seq_search"
						} else {
							"warm_start_array"
						},
						found: c.args.len(),
						expected: 1,
					})
				}
			}
			"warm_start_bool" => {
				if let [vars, vals] = c.args.as_slice() {
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
						name: "warm_start_bool",
						found: c.args.len(),
						expected: 2,
					})
				}
			}
			"warm_start_int" => {
				if let [vars, vals] = c.args.as_slice() {
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
						name: "warm_start_int",
						found: c.args.len(),
						expected: 2,
					})
				}
			}
			other => {
				warn!("ignoring unsupported search annotation: {}", other);
				Ok((Vec::new(), Vec::new()))
			}
		}
	}

	/// Extract an [`ValueSelection`] from an [`AnnotationArgument`] in a
	/// [`FlatZinc`] instance, or return a [`FlatZincError::InvalidArgumentType`]
	/// if an invalid type.
	fn ann_val_sel(arg: &AnnotationArgument<S>) -> Result<ValueSelection, FlatZincError> {
		match arg {
			AnnotationArgument::Literal(AnnotationLiteral::BaseLiteral(Literal::Identifier(s))) => {
				match s.deref() {
					"indomain" | "indomain_min" => Ok(ValueSelection::IndomainMin),
					"indomain_max" => Ok(ValueSelection::IndomainMax),
					// "indomain_median" => Ok(ValueSelection::IndomainMedian),
					// "indomain_random" => Ok(ValueSelection::IndomainRandom),
					// "indomain_split" => Ok(ValueSelection::IndomainSplit),
					// "indomain_split_random" => Ok(ValueSelection::IndomainSplitRandom),
					// "indomain_reverse_split" => Ok(ValueSelection::IndomainReverseSplit),
					"outdomain_max" => Ok(ValueSelection::OutdomainMax),
					"outdomain_min" => Ok(ValueSelection::OutdomainMin),
					// "outdomain_median" => Ok(ValueSelection::OutdomainMedian),
					// "outdomain_random" => Ok(ValueSelection::OutdomainRandom),
					_ => {
						warn!("unsupported value selection `{}', using `indomain_min'", s);
						Ok(ValueSelection::IndomainMin)
					}
				}
			}
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "string",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Extract an [`VariableSelection`] from an [`AnnotationArgument`] in a
	/// [`FlatZinc`] instance, or return a [`FlatZincError::InvalidArgumentType`]
	/// if an invalid type.
	fn ann_var_sel(arg: &AnnotationArgument<S>) -> Result<VariableSelection, FlatZincError> {
		match arg {
			AnnotationArgument::Literal(AnnotationLiteral::BaseLiteral(Literal::Identifier(s))) => {
				match s.deref() {
					"anti_first_fail" => Ok(VariableSelection::AntiFirstFail),
					// "dom_w_deg" => Ok(VariableSelection::DomWDeg),
					"first_fail" => Ok(VariableSelection::FirstFail),
					"input_order" => Ok(VariableSelection::InputOrder),
					"largest" => Ok(VariableSelection::Largest),
					// "max_regret" => Ok(VariableSelection::MaxRegret),
					// "most_constrained" => Ok(VariableSelection::MostConstrained),
					// "occurrence" => Ok(VariableSelection::Occurrence),
					"smallest" => Ok(VariableSelection::Smallest),
					_ => {
						warn!(
							"unsupported variable selection `{}', using `input_order'",
							s
						);
						Ok(VariableSelection::InputOrder)
					}
				}
			}
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "string",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Extract a [`Vec<Literal>`] from an [`Argument`].
	fn arg_array(&self, arg: &'a Argument<S>) -> Result<&'a Vec<Literal<S>>, FlatZincError> {
		match arg {
			Argument::Array(x) => Ok(x),
			Argument::Literal(Literal::Identifier(ident)) => {
				if let Some(arr) = self.fzn.arrays.get(ident) {
					Ok(&arr.contents)
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			Argument::Literal(x) => Err(FlatZincError::InvalidArgumentType {
				expected: "array",
				found: format!("{:?}", x),
			}),
		}
	}

	/// Extract a Boolean decision variable from the an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a Boolean decision variable.
	fn arg_bool(&mut self, arg: &Argument<S>) -> Result<BoolDecision, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_bool(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "boolean literal",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Check whether the given [`Argument`] is an array of length `len`.
	fn arg_has_length(&self, arg: &Argument<S>, len: usize) -> bool {
		match arg {
			Argument::Array(x) => x.len() == len,
			Argument::Literal(Literal::Identifier(ident)) => {
				if let Some(arr) = self.fzn.arrays.get(ident) {
					arr.contents.len() == len
				} else {
					false
				}
			}
			_ => false,
		}
	}

	/// Extract a integer decision variable from the an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a integer decision variable.
	fn arg_int(&mut self, arg: &Argument<S>) -> Result<IntDecision, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "integer literal",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Extract a parameter integer value from the an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not an integer parameter.
	fn arg_par_int(&self, arg: &Argument<S>) -> Result<IntVal, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.par_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par integer literal",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Extract a parameter integer set value from the an [`Argument`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a parameter set.
	fn arg_par_set(&self, arg: &Argument<S>) -> Result<IntSetVal, FlatZincError>
	where
		S: Deref<Target = str> + Clone + Debug,
	{
		match arg {
			Argument::Literal(l) => self.par_set(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par set literal",
				found: format!("{:?}", arg),
			}),
		}
	}

	/// Convert a Flatzinc `regular_int` constraint to a set of
	/// [`Constraint::TableInt`] constraints.
	fn convert_regular_to_tables(
		&mut self,
		vars: Vec<IntDecision>,
		transitions: Vec<Vec<IntVal>>,
		init_state: IntVal,
		accept_states: HashSet<IntVal>,
	) -> Vec<IntTable> {
		// TODO: Add the regular checking

		let mut table_constraints = Vec::new();
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
			.new_int_vars(vars.len() - 1, (1..=transitions.len() as IntVal).into())
			.into_iter()
			.collect_vec();

		// Add table constraint to force a transition for the starting state
		let sx: Vec<IntDecision> = vec![vars[0], state_vars[0]];
		table_constraints.push(table_int(sx, start));

		// Add table constraint to force valid transition for the intermediate
		// states
		for i in 1..vars.len() - 1 {
			let mx: Vec<IntDecision> = vec![state_vars[i - 1], vars[i], state_vars[i]];
			table_constraints.push(table_int(mx, middle.clone()));
		}

		// Add table constraint to force ending in an accepting state
		let ex: Vec<IntDecision> = vec![*state_vars.last().unwrap(), *vars.last().unwrap()];
		table_constraints.push(table_int(ex, end));
		table_constraints
	}

	/// Create branchers according to the search annotations in the FlatZinc instance
	pub(crate) fn create_branchers(&mut self) -> Result<(), FlatZincError> {
		let mut branchings = Vec::new();
		let mut warm_start = Vec::new();
		for ann in self.fzn.solve.ann.iter() {
			match ann {
				Annotation::Call(c) => {
					let (w, b) = self.ann_to_branchings(c)?;
					warm_start.extend(w);
					branchings.extend(b);
				}
				_ => warn!("ignoring unsupported search annotation: {}", ann),
			}
		}
		if !warm_start.is_empty() {
			self.prb += Branching::WarmStart(warm_start);
		}
		for b in branchings {
			self.prb += b;
		}
		Ok(())
	}

	/// Ensure all variables in the FlatZinc instance output are in the model
	pub(crate) fn ensure_output(&mut self) -> Result<(), FlatZincError> {
		for ident in self.fzn.output.iter() {
			if self.fzn.variables.contains_key(ident) {
				let _ = self.lookup_or_create_var(ident)?;
			} else if let Some(arr) = self.fzn.arrays.get(ident) {
				for x in &arr.contents {
					if let Literal::Identifier(ident) = x {
						let _ = self.lookup_or_create_var(ident)?;
					}
				}
			} else {
				return Err(FlatZincError::UnknownIdentifier(ident.to_string()));
			}
		}
		Ok(())
	}

	/// Preprocess a constraint in the [`FlatZinc`] instance to find variables
	/// that can be seen as views of other variables.
	///
	/// This allows us to avoid creating multiple variables that have to be kept
	/// consistent using propagators.
	fn extract_view(
		&mut self,
		defined_by: &HashMap<&S, usize>,
		con: usize,
	) -> Result<(), FlatZincError> {
		debug_assert!(!self.processed[con]);
		let c = &self.fzn.constraints[con];

		let add_view = |me: &mut Self, name: S, view: Decision| {
			let e = me.map.insert(name, view);
			me.stats.extracted_views += 1;
			debug_assert!(e.is_none());
			me.processed[con] = true;
		};
		let arg_bool_view =
			|me: &mut Self, arg: &Argument<S>| -> Result<BoolDecision, FlatZincError> {
				if let Argument::Literal(Literal::Identifier(x)) = arg {
					if !me.map.contains_key(x) && defined_by.contains_key(x) {
						me.extract_view(defined_by, defined_by[x])?;
					}
				}
				me.arg_bool(arg)
			};
		let lit_int_view =
			|me: &mut Self, lit: &Literal<S>| -> Result<IntDecision, FlatZincError> {
				if let Literal::Identifier(x) = lit {
					if !me.map.contains_key(x) && defined_by.contains_key(x) {
						me.extract_view(defined_by, defined_by[x])?;
					}
				}
				me.lit_int(lit)
			};

		let l = c.defines.as_ref().unwrap();
		debug_assert!(!self.map.contains_key(l));
		match c.id.deref() {
			"bool2int" => {
				if let [b, Argument::Literal(Literal::Identifier(x))] = c.args.as_slice() {
					if x == l {
						let b = arg_bool_view(self, b)?;
						add_view(self, l.clone(), IntDecision::from(b).into());
					}
				}
			}
			"bool_not" => match c.args.as_slice() {
				[Argument::Literal(Literal::Identifier(x)), b]
				| [b, Argument::Literal(Literal::Identifier(x))]
					if x == l =>
				{
					let b = arg_bool_view(self, b)?;
					add_view(self, l.clone(), (!b).into());
				}
				_ => {}
			},
			"int_eq_reif" => match c.args.as_slice() {
				[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
				| [Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), x.eq(*i).into());
				}
				_ => {}
			},
			"int_le_reif" => match c.args.as_slice() {
				[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), x.geq(*i).into());
				}
				[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), x.leq(*i).into());
				}
				_ => {}
			},
			"int_ne_reif" => match c.args.as_slice() {
				[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
				| [Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), x.ne(*i).into());
				}
				_ => {}
			},
			"int_lin_eq"
				if c.args
					.get(1)
					.map(|v| self.arg_has_length(v, 2))
					.unwrap_or(false) =>
			'int_lin_eq: {
				let [coeff, vars, sum] = c.args.as_slice() else {
					break 'int_lin_eq;
				};
				let coeff = self.arg_array(coeff)?;
				let vars = self.arg_array(vars)?;
				let (c, (cy, vy)) = match vars.as_slice() {
					[Literal::Identifier(v), y] if v == l => {
						(self.par_int(&coeff[0])?, (self.par_int(&coeff[1])?, y))
					}
					[y, Literal::Identifier(v)] if v == l => {
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
				let view = if let Some(scale) = NonZeroIntVal::new(-cy / c) {
					let y = lit_int_view(self, vy)?;
					y * scale + offset
				} else {
					offset.into()
				};
				add_view(self, l.clone(), view.into());
			}
			_ => {}
		}
		Ok(())
	}

	/// Preprocess the [`FlatZinc`] instance to find variables that can be seen as
	/// views of other variables.
	pub(crate) fn extract_views(&mut self) -> Result<(), FlatZincError> {
		// Create a mapping from identifiers to the constraint that defines them
		let defined_by: HashMap<&S, usize> = self
			.fzn
			.constraints
			.iter()
			.enumerate()
			.filter_map(|(i, c)| c.defines.as_ref().map(|d| (d, i)))
			.collect();

		// Extract views for all constraints that define an identifier
		for (i, c) in self.fzn.constraints.iter().enumerate() {
			if let Some(ident) = &c.defines {
				if !self.map.contains_key(ident) {
					self.extract_view(&defined_by, i)?;
				}
			}
		}
		Ok(())
	}

	/// Finalize the builder and return the model
	pub(crate) fn finalize<MapTy: FromIterator<(S, Decision)>>(
		self,
	) -> (Model, MapTy, FlatZincStatistics) {
		(self.prb, self.map.into_iter().collect(), self.stats)
	}

	/// Extract a Boolean decision variable from the a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a Boolean decision variable.
	fn lit_bool(&mut self, lit: &Literal<S>) -> Result<BoolDecision, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => self.lookup_or_create_var(ident).map(|mv| match mv {
				Decision::Bool(bv) => Ok(bv),
				Decision::Int(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "bool",
					found: "int".to_owned(),
				}),
			})?,
			&Literal::Bool(v) => Ok(v.into()),
			_ => todo!(),
		}
	}

	/// Extract a integer decision variable from a [`Literal`] in a [`FlatZinc`]
	/// instance. A [`FlatZincError::InvalidArgumentType`] will be returned if the
	/// argument was not a integer decision variable.
	fn lit_int(&mut self, lit: &Literal<S>) -> Result<IntDecision, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => self.lookup_or_create_var(ident).map(|mv| match mv {
				Decision::Int(iv) => Ok(iv),
				Decision::Bool(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "int",
					found: "bool".to_owned(),
				}),
			})?,
			&Literal::Bool(v) => Ok((v as IntVal).into()),
			&Literal::Int(v) => Ok(v.into()),
			_ => todo!(),
		}
	}

	/// Find the decision variable, i.e. [`ModelView`], associated with the given
	/// identifier, or create a new one if it doesn't yet exist.
	fn lookup_or_create_var(&mut self, ident: &S) -> Result<Decision, FlatZincError> {
		match self.map.entry(ident.clone()) {
			Entry::Vacant(e) => {
				if let Some(var) = self.fzn.variables.get(ident) {
					Ok(e.insert(match var.ty {
						Type::Bool => Decision::Bool(self.prb.new_bool_var()),
						Type::Int => match &var.domain {
							Some(Domain::Int(r)) => {
								Decision::Int(self.prb.new_int_var(r.iter().collect()))
							}
							Some(_) => unreachable!(),
							None => todo!("Variables without a domain are not yet supported"),
						},
						_ => todo!("Variables of {:?} are not yet supported", var.ty),
					})
					.clone())
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			Entry::Occupied(e) => Ok(e.get().clone()),
		}
	}
	/// Create a new builder to create a model from a FlatZinc instance
	pub(crate) fn new(fzn: &'a FlatZinc<S>) -> Self {
		Self {
			fzn,
			map: HashMap::new(),
			prb: Model::default(),
			processed: vec![false; fzn.constraints.len()],
			stats: FlatZincStatistics::default(),
		}
	}

	/// Extract a Boolean parameter from the a [`Literal`] in a [`FlatZinc`]
	/// instance. A [`FlatZincError::InvalidArgumentType`] will be returned if the
	/// argument was not a Boolean parameter.
	fn par_bool(&self, lit: &Literal<S>) -> Result<bool, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => {
				if let Some(var) = self.fzn.variables.get(ident) {
					if var.ty == Type::Bool && var.value.is_some() {
						self.par_bool(var.value.as_ref().unwrap())
					} else {
						Err(FlatZincError::InvalidArgumentType {
							expected: "par bool",
							found: format!("{:?}", var.ty),
						})
					}
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			Literal::Bool(v) => Ok(*v),
			_ => todo!(),
		}
	}

	/// Extract a parameter integer value from the a [`Literal`] in a [`FlatZinc`]
	/// instance. A [`FlatZincError::InvalidArgumentType`] will be returned if the
	/// argument was not an integer parameter.
	fn par_int(&self, lit: &Literal<S>) -> Result<IntVal, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => {
				if let Some(var) = self.fzn.variables.get(ident) {
					if var.ty == Type::Int && var.value.is_some() {
						self.par_int(var.value.as_ref().unwrap())
					} else {
						Err(FlatZincError::InvalidArgumentType {
							expected: "par int",
							found: format!("{:?}", var.ty),
						})
					}
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			Literal::Bool(v) => Ok(if *v { 1 } else { 0 }),
			Literal::Int(v) => Ok(*v),
			_ => todo!(),
		}
	}

	/// Extract a parameter integer set value from the a [`Literal`] in a
	/// [`FlatZinc`] instance. A [`FlatZincError::InvalidArgumentType`] will be
	/// returned if the argument was not a parameter set.
	fn par_set(&self, lit: &Literal<S>) -> Result<IntSetVal, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => {
				if let Some(var) = self.fzn.variables.get(ident) {
					if var.ty == Type::IntSet && var.value.is_some() {
						self.par_set(var.value.as_ref().unwrap())
					} else {
						Err(FlatZincError::InvalidArgumentType {
							expected: "par set",
							found: format!("{:?}", var.ty),
						})
					}
				} else {
					Err(FlatZincError::UnknownIdentifier(ident.to_string()))
				}
			}
			Literal::IntSet(v) => Ok(v.iter().collect()),
			_ => todo!(),
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
			match c.id.deref() {
				"array_bool_and" => {
					if let [es, r] = c.args.as_slice() {
						let es = self.arg_array(es)?;
						let r = self.arg_bool(r)?;
						let es: Result<Vec<_>, _> = es
							.iter()
							.map(|l| self.lit_bool(l).map(Into::into))
							.collect();
						self.prb += Formula::Equiv(vec![r.into(), Formula::And(es?)]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_bool_and",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"array_bool_xor" => {
					if let [es] = c.args.as_slice() {
						let es = self.arg_array(es)?;
						let es: Vec<Formula<BoolDecision>> = es
							.iter()
							.map(|l| self.lit_bool(l).map(Into::into))
							.try_collect()?;
						self.prb += Formula::Xor(es);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_bool_xor",
							found: c.args.len(),
							expected: 1,
						});
					}
				}
				"array_bool_element" => {
					if let [idx, arr, val] = c.args.as_slice() {
						let arr: Vec<_> = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.par_bool(l))
							.try_collect()?;
						let idx = self.arg_int(idx)?;
						let val = self.arg_bool(val)?;

						self.prb += array_element(arr, idx - 1, val);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_bool_element",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"array_int_element" => {
					if let [idx, arr, val] = c.args.as_slice() {
						let arr: Vec<_> = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.par_int(l))
							.try_collect()?;
						let idx = self.arg_int(idx)?;
						let val = self.arg_int(val)?;
						self.prb += array_element(arr, idx - 1, val);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_int_element",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"array_var_bool_element" => {
					if let [idx, arr, val] = c.args.as_slice() {
						let arr = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.lit_bool(l))
							.try_collect()?;
						let idx = self.arg_int(idx)?;
						let val = self.arg_bool(val)?;

						self.prb += array_element(arr, idx - 1, val);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_var_bool_element",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"array_var_int_element" => {
					if let [idx, arr, val] = c.args.as_slice() {
						let arr: Vec<_> = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.lit_int(l))
							.try_collect()?;
						let idx = self.arg_int(idx)?;
						let val = self.arg_int(val)?;

						self.prb += array_element(arr, idx - 1, val);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_var_int_element",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"bool2int" => {
					if let [b, i] = c.args.as_slice() {
						let b = self.arg_bool(b)?;
						let i = self.arg_int(i)?;
						self.prb += (IntDecision::from(b) - i).eq(0);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool2int",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"bool_lin_eq" => {
					if let [coeffs, vars, sum] = c.args.as_slice() {
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

						let lin_exp: IntLinExpr = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| {
								NonZeroIntVal::new(c).map(|c| IntDecision::from(x) * c)
							})
							.chain(once(-sum))
							.sum();

						self.prb += lin_exp.eq(0);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_lin_eq",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"bool_clause" => {
					if let [pos, neg] = c.args.as_slice() {
						let pos = self.arg_array(pos)?;
						let neg = self.arg_array(neg)?;
						let mut lits = Vec::with_capacity(pos.len() + neg.len());
						for l in pos {
							let e = self.lit_bool(l)?;
							lits.push(e.into());
						}
						for l in neg {
							let e = self.lit_bool(l)?;
							lits.push((!e).into());
						}
						self.prb += Formula::Or(lits);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"bool_eq_reif" => {
					if let [a, b, r] = c.args.as_slice() {
						let a = self.arg_bool(a)?;
						let b = self.arg_bool(b)?;
						let r = self.arg_bool(r)?;
						self.prb += Formula::Equiv(vec![
							r.into(),
							Formula::Equiv(vec![a.into(), b.into()]),
						]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_eq_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"bool_not" => {
					if let [a, b] = c.args.as_slice() {
						let a = self.arg_bool(a)?;
						let b = self.arg_bool(b)?;
						self.prb += Formula::Equiv(vec![b.into(), (!a).into()]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_not",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"bool_xor" => {
					if (2..=3).contains(&c.args.len()) {
						let a = self.arg_bool(&c.args[0])?;
						let b = self.arg_bool(&c.args[1])?;
						let mut f = Formula::Xor(vec![a.into(), b.into()]);
						if c.args.len() == 3 {
							let r = self.arg_bool(&c.args[2])?;
							f = Formula::Equiv(vec![r.into(), f]);
						}
						self.prb += f;
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_xor",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"huub_all_different_int" => {
					if let [args] = c.args.as_slice() {
						let args = self.arg_array(args)?;
						let args: Result<Vec<_>, _> =
							args.iter().map(|l| self.lit_int(l)).collect();
						self.prb += all_different_int(args?);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_all_different",
							found: c.args.len(),
							expected: 1,
						});
					}
				}
				"huub_array_int_maximum" | "huub_array_int_minimum" => {
					let is_maximum = c.id.deref() == "huub_array_int_maximum";
					if let [m, args] = c.args.as_slice() {
						let args = self.arg_array(args)?;
						let args: Result<Vec<_>, _> =
							args.iter().map(|l| self.lit_int(l)).collect();
						let m = self.arg_int(m)?;
						if is_maximum {
							self.prb += array_maximum_int(args?, m);
						} else {
							self.prb += array_minimum_int(args?, m);
						}
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: if is_maximum {
								"huub_array_int_maximum"
							} else {
								"huub_array_int_minimum"
							},
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"huub_bool_clause_reif" => {
					if let [pos, neg, r] = c.args.as_slice() {
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
						self.prb += Formula::Equiv(vec![r.into(), Formula::Or(lits)]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"huub_disjunctive_strict" => {
					if let [starts, durations] = c.args.as_slice() {
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
						self.prb += disjunctive_strict(start_times, durations);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_disjunctive_strict",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"huub_regular" => {
					if let [x, q, s, d, q0, f] = c.args.as_slice() {
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
								found: format!("array of size {}, for {q} states and {s} input values", d.len())
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
						let f: HashSet<IntVal> = f.iter().flat_map(|r| r.into_iter()).collect();

						// Convert regular constraint in to table constraints and add them to the model
						let tables = self.convert_regular_to_tables(x, d, q0, f);
						for table in tables {
							self.prb += table;
						}
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_regular",
							found: c.args.len(),
							expected: 6,
						});
					}
				}
				"huub_table_int" => {
					if let [args, table] = c.args.as_slice() {
						let args = self.arg_array(args)?;
						let args: Vec<_> = args.iter().map(|l| self.lit_int(l)).try_collect()?;
						let table = self.arg_array(table)?;
						let table: Vec<_> = table.iter().map(|l| self.par_int(l)).try_collect()?;
						if args.is_empty() || (table.len() % args.len()) != 0 {
							return Err(FlatZincError::InvalidArgumentType {
								expected: "array of n integers, where n is divisible by the number of variables",
								found: format!("array of {} integers, to give values to {} variables", table.len(), args.len()),
							});
						}
						if table.is_empty() {
							return Err(ReformulationError::TrivialUnsatisfiable.into());
						}
						let table: Vec<Vec<_>> = table
							.into_iter()
							.chunks(args.len())
							.into_iter()
							.map(|c| c.collect())
							.collect();
						self.prb += table_int(args, table);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_table_int",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"int_abs" => {
					if let [origin, abs] = c.args.as_slice() {
						let origin = self.arg_int(origin)?;
						let abs = self.arg_int(abs)?;
						self.prb += abs_int(origin, abs);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_abs",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"int_div" => {
					if let [num, denom, res] = c.args.as_slice() {
						let num = self.arg_int(num)?;
						let denom = self.arg_int(denom)?;
						let res = self.arg_int(res)?;
						self.prb += div_int(num, denom, res);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_div",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_le" | "int_ne" => {
					if let [a, b] = c.args.as_slice() {
						let a = self.arg_int(a)?;
						let b = self.arg_int(b)?;
						let lin_exp = a - b;
						self.prb += match c.id.deref() {
							"int_le" => lin_exp.leq(0),
							"int_ne" => lin_exp.ne(0),
							_ => unreachable!(),
						};
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: match c.id.deref() {
								"int_le" => "int_le",
								"int_ne" => "int_ne",
								_ => unreachable!(),
							},
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"int_eq_imp" | "int_eq_reif" | "int_le_imp" | "int_le_reif" | "int_ne_imp"
				| "int_ne_reif" => {
					if let [a, b, r] = c.args.as_slice() {
						let a = self.arg_int(a)?;
						let b = self.arg_int(b)?;
						let r = self.arg_bool(r)?;

						let lin_exp = a - b;
						let lin = match c.id.deref() {
							"int_eq_imp" | "int_eq_reif" => lin_exp.eq(0),
							"int_le_imp" | "int_le_reif" => lin_exp.leq(0),
							"int_ne_imp" | "int_ne_reif" => lin_exp.ne(0),
							_ => unreachable!(),
						};
						self.prb += match c.id.deref() {
							"int_eq_imp" | "int_le_imp" | "int_ne_imp" => lin.implied_by(r),
							"int_eq_reif" | "int_le_reif" | "int_ne_reif" => lin.reified_by(r),
							_ => unreachable!(),
						};
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: match c.id.deref() {
								"int_eq_imp" => "int_eq_imp",
								"int_eq_reif" => "int_eq_reif",
								"int_le_imp" => "int_le_imp",
								"int_le_reif" => "int_le_reif",
								"int_ne_imp" => "int_ne_imp",
								"int_ne_reif" => "int_ne_reif",
								_ => unreachable!(),
							},
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_lin_eq" | "int_lin_le" | "int_lin_ne" => {
					if let [coeffs, vars, rhs] = c.args.as_slice() {
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
						let lin_exp: IntLinExpr = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.sum();

						self.prb += match c.id.deref() {
							"int_lin_eq" => lin_exp.eq(rhs),
							"int_lin_le" => lin_exp.leq(rhs),
							"int_lin_ne" => lin_exp.ne(rhs),
							_ => unreachable!(),
						};
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: match c.id.deref() {
								"int_lin_eq" => "int_lin_eq",
								"int_lin_le" => "int_lin_le",
								"int_lin_ne" => "int_lin_ne",
								_ => unreachable!(),
							},
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_lin_eq_imp" | "int_lin_eq_reif" | "int_lin_le_imp" | "int_lin_le_reif"
				| "int_lin_ne_imp" | "int_lin_ne_reif" => {
					if let [coeffs, vars, rhs, reified] = c.args.as_slice() {
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
						let lin_exp: IntLinExpr = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.sum();

						let lin = match c.id.deref() {
							"int_lin_eq_imp" | "int_lin_eq_reif" => lin_exp.eq(rhs),
							"int_lin_le_imp" | "int_lin_le_reif" => lin_exp.leq(rhs),
							"int_lin_ne_imp" | "int_lin_ne_reif" => lin_exp.ne(rhs),
							_ => unreachable!(),
						};
						self.prb += match c.id.deref() {
							"int_lin_eq_imp" | "int_lin_le_imp" | "int_lin_ne_imp" => {
								lin.implied_by(reified)
							}
							"int_lin_eq_reif" | "int_lin_le_reif" | "int_lin_ne_reif" => {
								lin.reified_by(reified)
							}
							_ => unreachable!(),
						};
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: match c.id.deref() {
								"int_lin_eq_imp" => "int_lin_eq_imp",
								"int_lin_eq_reif" => "int_lin_eq_reif",
								"int_lin_le_imp" => "int_lin_le_imp",
								"int_lin_le_reif" => "int_lin_le_reif",
								"int_lin_ne_imp" => "int_lin_ne_imp",
								"int_lin_ne_reif" => "int_lin_ne_reif",
								_ => unreachable!(),
							},
							found: c.args.len(),
							expected: 4,
						});
					}
				}
				"int_max" | "int_min" => {
					let is_maximum = c.id.deref() == "int_max";
					if let [a, b, m] = c.args.as_slice() {
						let a = self.arg_int(a)?;
						let b = self.arg_int(b)?;
						let m = self.arg_int(m)?;
						if is_maximum {
							self.prb += array_maximum_int(vec![a, b], m);
						} else {
							self.prb += array_minimum_int(vec![a, b], m);
						}
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: if is_maximum { "int_max" } else { "int_min" },
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"int_pow" => {
					if let [base, exponent, res] = c.args.as_slice() {
						let base = self.arg_int(base)?;
						let exponent = self.arg_int(exponent)?;
						let res = self.arg_int(res)?;
						self.prb += pow_int(base, exponent, res);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_pow",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_times" => {
					if let [x, y, z] = c.args.as_slice() {
						let a = self.arg_int(x)?;
						let b = self.arg_int(y)?;
						let m = self.arg_int(z)?;
						self.prb += times_int(a, b, m);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_times",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"set_in" => {
					if let [x, s] = c.args.as_slice() {
						let x = self.arg_int(x)?;
						let s = self.arg_par_set(s)?;

						self.prb.set_int_in_set(x, &s)?;
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "set_in",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"set_in_reif" => {
					if let [x, s, r] = c.args.as_slice() {
						let x = self.arg_int(x)?;
						let s = self.arg_par_set(s)?;
						let r = self.arg_bool(r)?;

						self.prb += int_in_set_reif(x, s, r);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "set_in_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				_ => return Err(FlatZincError::UnknownConstraint(c.id.to_string())),
			}
		}

		Ok(())
	}

	/// Unify variables in the [`Model`] that are know to be equivalent.
	///
	/// This can happen because of `bool_eq` and `int_eq` constraints in the
	/// [`FlatZinc`] instance.
	pub(crate) fn unify_variables(&mut self) -> Result<(), FlatZincError> {
		let mut unify_map = HashMap::<S, Rc<RefCell<Vec<Literal<S>>>>>::new();
		let unify_map_find = |map: &HashMap<S, Rc<RefCell<Vec<Literal<S>>>>>, a: &Literal<S>| {
			if let Literal::Identifier(x) = a {
				map.get(x).map(Rc::clone)
			} else {
				None
			}
		};

		let record_unify = |map: &mut HashMap<S, Rc<RefCell<Vec<Literal<S>>>>>, a, b| {
			let a_set = unify_map_find(map, a);
			let b_set = unify_map_find(map, b);
			match (a_set, b_set) {
				(Some(a_set), Some(b_set)) => {
					let mut members = (*a_set).borrow_mut();
					members.extend(b_set.take());
					for b in members.iter() {
						if let Literal::Identifier(b) = b {
							let _ = map.insert(b.clone(), Rc::clone(&a_set));
						}
					}
				}
				(Some(a_set), None) => {
					let mut members = (*a_set).borrow_mut();
					members.push(b.clone());
					if let Literal::Identifier(b) = b {
						let _ = map.insert(b.clone(), Rc::clone(&a_set));
					}
				}
				(None, Some(b_set)) => {
					let mut members = (*b_set).borrow_mut();
					members.push(a.clone());
					if let Literal::Identifier(a) = a {
						let _ = map.insert(a.clone(), Rc::clone(&b_set));
					}
				}
				(None, None) => {
					let n_set = Rc::new(RefCell::new(vec![a.clone(), b.clone()]));
					if let Literal::Identifier(a) = a {
						let _ = map.insert(a.clone(), Rc::clone(&n_set));
					}
					if let Literal::Identifier(b) = b {
						let _ = map.insert(b.clone(), n_set);
					}
				}
			};
		};

		for (i, c) in self.fzn.constraints.iter().enumerate() {
			if self.processed[i] {
				continue;
			}
			let mark_processed = |me: &mut Self| me.processed[i] = true;
			match c.id.deref() {
				"bool_eq" => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed(self);
					}
				}
				"int_eq" => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed(self);
					}
				}
				"array_bool_element" | "array_int_element" => {
					if let [idx, arr, Argument::Literal(b)] = c.args.as_slice() {
						let arr = self.arg_array(arr)?;
						let idx = self.arg_int(idx)?;
						// unify if the index is constant
						if let IntDecisionInner::Const(idx) = idx.0 {
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

		let mut resolved = HashSet::new();
		let keys = unify_map.keys().sorted();
		for k in keys {
			let li = unify_map[k].borrow();
			if resolved.contains(k) {
				continue;
			}
			let ty = &self.fzn.variables[k].ty;
			// Determine the domain of the list of literals
			let domain: Option<Literal<S>> = match ty {
				Type::Bool => {
					let mut domain = None;
					for lit in li.iter() {
						match lit {
							Literal::Bool(b) => {
								if domain == Some(!b) {
									return Err(ReformulationError::TrivialUnsatisfiable.into());
								} else {
									domain = Some(*b);
								}
							}
							Literal::Identifier(_) => {}
							_ => unreachable!(),
						};
					}
					domain.map(Literal::Bool)
				}
				Type::Int => {
					let mut domain = None::<IntSetVal>;
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
							Literal::Identifier(id) => {
								if let Some(Domain::Int(d)) = &self.fzn.variables[id].domain {
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
				}
				_ => unreachable!(),
			};
			// Find any view that is part of a unified group
			let var = li
				.iter()
				.find_map(|lit| -> Option<Decision> {
					if let Literal::Identifier(id) = lit {
						self.map.get(id).cloned()
					} else {
						None
					}
				})
				// Create a new variable if no view is found
				.unwrap_or_else(|| match domain {
					Some(Literal::Bool(b)) => BoolDecision::from(b).into(),
					Some(Literal::IntSet(dom)) => self.prb.new_int_var(dom).into(),
					Some(_) => unreachable!(),
					None => match ty {
						Type::Bool => self.prb.new_bool_var().into(),
						Type::Int => panic!("unbounded integer variables are not supported yet"),
						_ => unreachable!(),
					},
				});

			// Map (or equate) all names in the group to the new variable
			for lit in li.iter() {
				if let Literal::Identifier(id) = lit {
					match self.map.entry(id.clone()) {
						Entry::Vacant(e) => {
							let _ = e.insert(var.clone());
							self.stats.vars_unified += 1;
						}
						Entry::Occupied(e) => {
							if var != *e.get() {
								match ty {
									Type::Bool => {
										let (Decision::Bool(new), Decision::Bool(existing)) =
											(var.clone(), e.get().clone())
										else {
											unreachable!()
										};
										self.prb +=
											Formula::Equiv(vec![new.into(), existing.into()]);
									}
									Type::Int => {
										let (Decision::Int(new), Decision::Int(existing)) =
											(var.clone(), e.get().clone())
										else {
											unreachable!()
										};
										self.prb += (new - existing).eq(0);
									}
									_ => unreachable!(),
								}
							}
						}
					}
					let new = resolved.insert(id.clone());
					debug_assert!(new);
				}
			}
		}
		Ok(())
	}
}
