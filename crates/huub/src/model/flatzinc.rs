use std::{
	cell::RefCell,
	collections::{hash_map::Entry, HashMap, HashSet},
	fmt::{Debug, Display},
	hash::Hash,
	ops::Deref,
	rc::Rc,
};

use flatzinc_serde::{
	Annotation, AnnotationArgument, AnnotationCall, AnnotationLiteral, Argument, Domain, FlatZinc,
	Literal, Type,
};
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};
use rangelist::{IntervalIterator, RangeList};
use thiserror::Error;
use tracing::warn;

use crate::{
	model::{
		bool::BoolView,
		branching::{Branching, ValueSelection, VariableSelection},
		int::IntView,
		reformulate::ReformulationError,
		ModelView,
	},
	solver::SatSolver,
	BoolExpr, Constraint, InitConfig, IntSetVal, IntVal, Model, NonZeroIntVal, Solver, SolverView,
};

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
struct FznModelBuilder<'a, S: Eq + Hash + Ord> {
	/// The FlatZinc instance to build the model from
	fzn: &'a FlatZinc<S>,
	/// A mapping from FlatZinc identifiers to model views
	map: HashMap<S, ModelView>,
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
	/// Create a new builder to create a model from a FlatZinc instance
	fn new(fzn: &'a FlatZinc<S>) -> Self {
		Self {
			fzn,
			map: HashMap::new(),
			prb: Model::default(),
			processed: vec![false; fzn.constraints.len()],
			stats: FlatZincStatistics::default(),
		}
	}

	/// Add a view to the model and the mapping
	fn extract_views(&mut self) -> Result<(), FlatZincError> {
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

	fn extract_view(
		&mut self,
		defined_by: &HashMap<&S, usize>,
		con: usize,
	) -> Result<(), FlatZincError> {
		debug_assert!(!self.processed[con]);
		let c = &self.fzn.constraints[con];

		let add_view = |me: &mut Self, name: S, view: ModelView| {
			let e = me.map.insert(name, view);
			me.stats.extracted_views += 1;
			debug_assert!(e.is_none());
			me.processed[con] = true;
		};
		let arg_bool_view = |me: &mut Self, arg: &Argument<S>| -> Result<BoolView, FlatZincError> {
			if let Argument::Literal(Literal::Identifier(x)) = arg {
				if !me.map.contains_key(x) && defined_by.contains_key(x) {
					me.extract_view(defined_by, defined_by[x])?;
				}
			}
			me.arg_bool(arg)
		};
		let lit_int_view = |me: &mut Self, lit: &Literal<S>| -> Result<IntView, FlatZincError> {
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
						add_view(self, l.clone(), IntView::from(b).into());
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
					add_view(self, l.clone(), BoolView::IntEq(Box::new(x), *i).into());
				}
				_ => {}
			},
			"int_le_reif" => match c.args.as_slice() {
				[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(
						self,
						l.clone(),
						BoolView::IntGreaterEq(Box::new(x), *i).into(),
					);
				}
				[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), BoolView::IntLessEq(Box::new(x), *i).into());
				}
				_ => {}
			},
			"int_ne_reif" => match c.args.as_slice() {
				[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
				| [Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
					if r == l =>
				{
					let x = lit_int_view(self, x)?;
					add_view(self, l.clone(), BoolView::IntNotEq(Box::new(x), *i).into());
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
					IntView::Const(offset)
				};
				add_view(self, l.clone(), view.into());
			}
			_ => {}
		}
		Ok(())
	}

	/// Unify variables (e.g., from `bool_eq` and `int_eq` constraints)
	fn unify_variables(&mut self) -> Result<(), FlatZincError> {
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
						if let IntView::Const(idx) = idx {
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
		for (k, li) in unify_map.iter() {
			if resolved.contains(k) {
				continue;
			}
			let ty = &self.fzn.variables[k].ty;
			let li = li.borrow();
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
					let mut domain = None::<RangeList<IntVal>>;
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
				.find_map(|lit| -> Option<ModelView> {
					if let Literal::Identifier(id) = lit {
						self.map.get(id).cloned()
					} else {
						None
					}
				})
				// Create a new variable if no view is found
				.unwrap_or_else(|| match domain {
					Some(Literal::Bool(b)) => BoolView::Const(b).into(),
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
										let (ModelView::Bool(new), ModelView::Bool(existing)) =
											(var.clone(), e.get().clone())
										else {
											unreachable!()
										};
										self.prb +=
											BoolExpr::Equiv(vec![new.into(), existing.into()]);
									}
									Type::Int => {
										let (ModelView::Int(new), ModelView::Int(existing)) =
											(var.clone(), e.get().clone())
										else {
											unreachable!()
										};
										self.prb +=
											Constraint::IntLinEq(vec![new, existing * -1], 0);
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

	fn post_constraints(&mut self) -> Result<(), FlatZincError> {
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
						self.prb += BoolExpr::Equiv(vec![r.into(), BoolExpr::And(es?)]);
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
						let es: Result<Vec<BoolExpr>, _> = es
							.iter()
							.map(|l| self.lit_bool(l).map(Into::into))
							.collect();
						self.prb += BoolExpr::Xor(es?);
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

						// Convert array of boolean values to a set literals of the indices where
						// the value is true
						let mut ranges = Vec::new();
						let mut start = None;
						for (i, b) in arr.iter().enumerate() {
							match (b, start) {
								(true, None) => start = Some((i + 1) as IntVal),
								(false, Some(s)) => {
									ranges.push(s..=i as IntVal);
									start = None;
								}
								(false, None) | (true, Some(_)) => {}
							}
						}
						if let Some(s) = start {
							ranges.push(s..=arr.len() as IntVal);
						}
						assert_ne!(ranges.len(), 0, "unexpected empty range list");

						self.prb +=
							Constraint::SetInReif(idx, RangeList::from_iter(ranges), val.into());
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
						let arr: Result<Vec<_>, _> = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.par_int(l))
							.collect();
						let idx = self.arg_int(idx)?;
						let val = self.arg_int(val)?;
						self.prb += Constraint::ArrayIntElement(arr?, idx, val);
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
						let arr: Result<Vec<_>, FlatZincError> = self
							.arg_array(arr)?
							.iter()
							.map(|l| {
								let x: BoolView = self.lit_bool(l)?;
								Ok(x.into())
							})
							.collect();
						let idx = self.arg_int(idx)?;
						let val = self.arg_bool(val)?;

						self.prb += Constraint::ArrayVarBoolElement(arr?, idx, val.into());
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
						let arr: Result<Vec<_>, _> = self
							.arg_array(arr)?
							.iter()
							.map(|l| self.lit_int(l))
							.collect();
						let idx = self.arg_int(idx)?;
						let val = self.arg_int(val)?;
						self.prb += Constraint::ArrayVarIntElement(arr?, idx, val);
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
						self.prb += Constraint::IntLinEq(vec![b.into(), -i], 0);
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
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| {
								NonZeroIntVal::new(c).map(|c| IntView::from(x) * c)
							})
							.chain(Some(-sum))
							.collect();
						self.prb += Constraint::IntLinEq(vars, 0);
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
						self.prb += BoolExpr::Or(lits);
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
						self.prb += BoolExpr::Equiv(vec![
							r.into(),
							BoolExpr::Equiv(vec![a.into(), b.into()]),
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
						self.prb += BoolExpr::Equiv(vec![b.into(), (!a).into()]);
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
						let mut f = BoolExpr::Xor(vec![a.into(), b.into()]);
						if c.args.len() == 3 {
							let r = self.arg_bool(&c.args[2])?;
							f = BoolExpr::Equiv(vec![r.into(), f]);
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
						self.prb += Constraint::AllDifferentInt(args?);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_all_different",
							found: c.args.len(),
							expected: 1,
						});
					}
				}
				"huub_disjunctive_strict" => {
					if let [starts, durations] = c.args.as_slice() {
						let starts = self
							.arg_array(starts)?
							.iter()
							.map(|l| self.lit_int(l))
							.try_collect()?;
						let durations = self
							.arg_array(durations)?
							.iter()
							.map(|l| self.par_int(l))
							.try_collect()?;
						self.prb += Constraint::DisjunctiveStrict(starts, durations);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "huub_disjunctive_strict",
							found: c.args.len(),
							expected: 2,
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
							self.prb += Constraint::ArrayIntMaximum(args?, m);
						} else {
							self.prb += Constraint::ArrayIntMinimum(args?, m);
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
						self.prb += BoolExpr::Equiv(vec![r.into(), BoolExpr::Or(lits)]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_abs" => {
					if let [origin, abs] = c.args.as_slice() {
						let origin = self.arg_int(origin)?;
						let abs = self.arg_int(abs)?;
						self.prb += Constraint::IntAbs(origin, abs);
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
						self.prb += Constraint::IntDiv(num, denom, res);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_div",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_le" => {
					if let [a, b] = c.args.as_slice() {
						let a = self.arg_int(a)?;
						let b = self.arg_int(b)?;
						self.prb += Constraint::IntLinLessEq(vec![a, -b], 0);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_le",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"int_ne" => {
					if let [a, b] = c.args.as_slice() {
						let a = self.arg_int(a)?;
						let b = self.arg_int(b)?;
						self.prb += Constraint::IntLinNotEq(vec![a, -b], 0);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "int_ne",
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
						self.prb += match c.id.deref() {
							"int_eq_imp" => Constraint::IntLinEqImp,
							"int_eq_reif" => Constraint::IntLinEqReif,
							"int_le_imp" => Constraint::IntLinLessEqImp,
							"int_le_reif" => Constraint::IntLinLessEqReif,
							"int_ne_imp" => Constraint::IntLinNotEqImp,
							"int_ne_reif" => Constraint::IntLinNotEqReif,
							_ => unreachable!(),
						}(vec![a, -b], 0, r.into());
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
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.collect();

						self.prb += match c.id.deref() {
							"int_lin_eq" => Constraint::IntLinEq,
							"int_lin_le" => Constraint::IntLinLessEq,
							"int_lin_ne" => Constraint::IntLinNotEq,
							_ => unreachable!(),
						}(vars, rhs);
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
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.collect();
						self.prb += match c.id.deref() {
							"int_lin_eq_imp" => Constraint::IntLinEqImp,
							"int_lin_eq_reif" => Constraint::IntLinEqReif,
							"int_lin_le_imp" => Constraint::IntLinLessEqImp,
							"int_lin_le_reif" => Constraint::IntLinLessEqReif,
							"int_lin_ne_imp" => Constraint::IntLinNotEqImp,
							"int_lin_ne_reif" => Constraint::IntLinNotEqReif,
							_ => unreachable!(),
						}(vars, rhs, reified.into());
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
							self.prb += Constraint::ArrayIntMaximum(vec![a, b], m);
						} else {
							self.prb += Constraint::ArrayIntMinimum(vec![a, b], m);
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

						self.prb += Constraint::IntPow(base, exponent, res);
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
						self.prb += Constraint::IntTimes(a, b, m);
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

						self.prb
							.intersect_int_domain(&x, &s, self.prb.constraints.len())?;
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

						self.prb += Constraint::SetInReif(x, s, r.into());
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

			let n = self.prb.functional.len() - 1;
			self.prb.functional[n] = c.defines.is_some();
		}

		Ok(())
	}

	/// Create branchers according to the search annotations in the FlatZinc instance
	fn create_branchers(&mut self) -> Result<(), FlatZincError> {
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
	fn ensure_output(&mut self) -> Result<(), FlatZincError> {
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

	/// Finalize the builder and return the model
	fn finalize(self) -> (Model, HashMap<S, ModelView>, FlatZincStatistics) {
		(self.prb, self.map, self.stats)
	}

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

	// Get an array of variable literals from an annotation argument
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

	fn ann_to_branchings(
		&mut self,
		c: &'a AnnotationCall<S>,
	) -> Result<(Vec<BoolView>, Vec<Branching>), FlatZincError> {
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
							.map(|(var, val)| BoolView::IntEq(Box::new(var), val))
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

	fn lookup_or_create_var(&mut self, ident: &S) -> Result<ModelView, FlatZincError> {
		match self.map.entry(ident.clone()) {
			Entry::Vacant(e) => {
				if let Some(var) = self.fzn.variables.get(ident) {
					Ok(e.insert(match var.ty {
						Type::Bool => ModelView::Bool(self.prb.new_bool_var()),
						Type::Int => match &var.domain {
							Some(Domain::Int(r)) => {
								ModelView::Int(self.prb.new_int_var(r.iter().collect()))
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

	fn lit_bool(&mut self, lit: &Literal<S>) -> Result<BoolView, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => self.lookup_or_create_var(ident).map(|mv| match mv {
				ModelView::Bool(bv) => Ok(bv),
				ModelView::Int(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "bool",
					found: "int".to_owned(),
				}),
			})?,
			Literal::Bool(v) => Ok(BoolView::Const(*v)),
			_ => todo!(),
		}
	}

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

	fn arg_bool(&mut self, arg: &Argument<S>) -> Result<BoolView, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_bool(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "boolean literal",
				found: format!("{:?}", arg),
			}),
		}
	}

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

	fn lit_int(&mut self, lit: &Literal<S>) -> Result<IntView, FlatZincError> {
		match lit {
			Literal::Identifier(ident) => self.lookup_or_create_var(ident).map(|mv| match mv {
				ModelView::Int(iv) => Ok(iv),
				ModelView::Bool(_) => Err(FlatZincError::InvalidArgumentType {
					expected: "int",
					found: "bool".to_owned(),
				}),
			})?,
			Literal::Bool(v) => Ok(IntView::Const(if *v { 1 } else { 0 })),
			Literal::Int(v) => Ok(IntView::Const(*v)),
			_ => todo!(),
		}
	}

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

	fn arg_int(&mut self, arg: &Argument<S>) -> Result<IntView, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.lit_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "integer literal",
				found: format!("{:?}", arg),
			}),
		}
	}

	fn arg_par_int(&self, arg: &Argument<S>) -> Result<IntVal, FlatZincError> {
		match arg {
			Argument::Literal(l) => self.par_int(l),
			_ => Err(FlatZincError::InvalidArgumentType {
				expected: "par integer literal",
				found: format!("{:?}", arg),
			}),
		}
	}

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
}

impl Model {
	pub fn from_fzn<S>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, HashMap<S, ModelView>, FlatZincStatistics), FlatZincError>
	where
		S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
	{
		let mut builder = FznModelBuilder::new(fzn);
		builder.extract_views()?;
		builder.unify_variables()?;
		builder.post_constraints()?;
		builder.create_branchers()?;
		builder.ensure_output()?;

		Ok(builder.finalize())
	}
}

impl<Sol, Sat> Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol> + 'static,
{
	pub fn from_fzn<S>(
		fzn: &FlatZinc<S>,
		config: &InitConfig,
	) -> Result<(Self, HashMap<S, SolverView>, FlatZincStatistics), FlatZincError>
	where
		S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
	{
		let (mut prb, map, fzn_stats) = Model::from_fzn(fzn)?;
		let (mut slv, remap) = prb.to_solver(config)?;
		let map = map
			.into_iter()
			.map(|(k, v)| (k, remap.get(&mut slv, &v)))
			.collect();
		Ok((slv, map, fzn_stats))
	}
}

#[derive(Error, Debug)]
pub enum FlatZincError {
	#[error("{0:?} type variables are not supported by huub")]
	UnsupportedType(Type),
	#[error("constraint cannot be constructed using unknown identifier `{0}'")]
	UnknownConstraint(String),
	#[error("constraints with identifiers `{name}' must have {expected} arguments, found {found}")]
	InvalidNumArgs {
		name: &'static str,
		found: usize,
		expected: usize,
	},
	#[error("could not find identifier `{0}'")]
	UnknownIdentifier(String),
	#[error("argument found of type `{found}', expected `{expected}'")]
	InvalidArgumentType {
		expected: &'static str,
		found: String,
	},
	#[error("error reformulating generated model `{0}'")]
	ReformulationError(#[from] ReformulationError),
}
