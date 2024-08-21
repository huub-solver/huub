use std::{
	cell::RefCell,
	collections::{btree_map::Entry, BTreeMap},
	fmt::{Debug, Display},
	ops::Deref,
	rc::Rc,
};

use flatzinc_serde::{
	Annotation, AnnotationArgument, AnnotationCall, AnnotationLiteral, Argument, Domain, FlatZinc,
	Literal, Type, Variable,
};
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};
use rangelist::{IntervalIterator, RangeList};
use thiserror::Error;
use tracing::warn;

use super::{
	bool::BoolView,
	branching::{Branching, ValueSelection, VariableSelection},
};
use crate::{
	model::{int::IntView, reformulate::ReformulationError, ModelView},
	solver::SatSolver,
	BoolExpr, Constraint, InitConfig, IntSetVal, IntVal, Model, NonZeroIntVal, Solver, SolverView,
};
impl Model {
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug + Display>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, ModelView>), FlatZincError> {
		let mut map = BTreeMap::<S, ModelView>::new();
		let mut prb = Model::default();

		// Extract views from `defines_var` constraints
		let mut processed = vec![false; fzn.constraints.len()];
		for (i, c) in fzn.constraints.iter().enumerate() {
			let mut add_view = |map: &mut BTreeMap<_, _>, name: S, view: ModelView| {
				let e = map.insert(name, view);
				debug_assert!(e.is_none());
				processed[i] = true;
			};

			match (c.id.deref(), c.defines.as_ref()) {
				("bool2int", Some(l)) => {
					if let [b, Argument::Literal(Literal::Identifier(x))] = c.args.as_slice() {
						if x == l {
							let b = arg_bool(fzn, &mut prb, &mut map, b)?;
							add_view(&mut map, l.clone(), IntView::from(b).into());
						}
					}
				}
				("bool_not", Some(l)) => match c.args.as_slice() {
					[Argument::Literal(Literal::Identifier(x)), b]
					| [b, Argument::Literal(Literal::Identifier(x))]
						if x == l =>
					{
						let b = arg_bool(fzn, &mut prb, &mut map, b)?;
						add_view(&mut map, l.clone(), (!b).into());
					}
					_ => {}
				},
				("int_eq_reif", Some(l)) => match c.args.as_slice() {
					[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
					| [Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
						if r == l =>
					{
						let x = lit_int(fzn, &mut prb, &mut map, x)?;
						add_view(&mut map, l.clone(), BoolView::IntEq(Box::new(x), *i).into());
					}
					_ => {}
				},
				("int_le_reif", Some(l)) => match c.args.as_slice() {
					[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
						if r == l =>
					{
						let x = lit_int(fzn, &mut prb, &mut map, x)?;
						add_view(
							&mut map,
							l.clone(),
							BoolView::IntGreaterEq(Box::new(x), *i).into(),
						);
					}
					[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
						if r == l =>
					{
						let x = lit_int(fzn, &mut prb, &mut map, x)?;
						add_view(
							&mut map,
							l.clone(),
							BoolView::IntLessEq(Box::new(x), *i).into(),
						);
					}
					_ => {}
				},
				("int_ne_reif", Some(l)) => match c.args.as_slice() {
					[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
					| [Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
						if r == l =>
					{
						let x = lit_int(fzn, &mut prb, &mut map, x)?;
						add_view(
							&mut map,
							l.clone(),
							BoolView::IntNotEq(Box::new(x), *i).into(),
						);
					}
					_ => {}
				},
				("int_lin_eq", Some(l))
					if c.args
						.get(1)
						.map(|v| arg_has_length(fzn, v, 2))
						.unwrap_or(false) =>
				'int_lin_eq: {
					let [coeff, vars, sum] = c.args.as_slice() else {
						break 'int_lin_eq;
					};
					let coeff = arg_array(fzn, coeff)?;
					let vars = arg_array(fzn, vars)?;
					let (c, (cy, vy)) = match vars.as_slice() {
						[Literal::Identifier(v), y] if v == l => {
							(par_int(fzn, &coeff[0])?, (par_int(fzn, &coeff[1])?, y))
						}
						[y, Literal::Identifier(v)] if v == l => {
							(par_int(fzn, &coeff[1])?, (par_int(fzn, &coeff[0])?, y))
						}
						_ => break 'int_lin_eq,
					};
					let sum = arg_par_int(fzn, sum)?;
					// c * l + cy * y = sum === l = (sum - cy * y) / c
					if cy % c != 0 || sum % c != 0 {
						break 'int_lin_eq;
					}
					let offset = sum / c;
					let view = if let Some(scale) = NonZeroIntVal::new(-cy / c) {
						let y = lit_int(fzn, &mut prb, &mut map, vy)?;
						y * scale + offset
					} else {
						IntView::Const(offset)
					};
					add_view(&mut map, l.clone(), view.into());
				}
				_ => {}
			}
		}

		// Unify variables (e.g., from `bool_eq` and `int_eq` constraints)
		let mut unify_map = BTreeMap::<S, Rc<RefCell<Vec<Literal<S>>>>>::new();
		let unify_map_find = |map: &BTreeMap<S, Rc<RefCell<Vec<Literal<S>>>>>, a: &Literal<S>| {
			if let Literal::Identifier(x) = a {
				map.get(x).map(Rc::clone)
			} else {
				None
			}
		};
		let record_unify = |map: &mut BTreeMap<S, Rc<RefCell<Vec<Literal<S>>>>>, a, b| {
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
		for (i, c) in fzn.constraints.iter().enumerate() {
			let mut mark_processed = || processed[i] = true;
			match c.id.deref() {
				"bool_eq" => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed();
					}
				}
				"int_eq" => {
					if let [Argument::Literal(a), Argument::Literal(b)] = c.args.as_slice() {
						record_unify(&mut unify_map, a, b);
						mark_processed();
					}
				}
				"array_bool_element" | "array_int_element" => {
					if let [idx, arr, Argument::Literal(b)] = c.args.as_slice() {
						let arr = arg_array(fzn, arr)?;
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						// unify if the index is constant
						if let IntView::Const(idx) = idx {
							let a = &arr[(idx - 1) as usize];
							record_unify(&mut unify_map, a, b);
							mark_processed();
						}
						// unify if all values in arr are equal
						if !arr.is_empty() && arr.iter().all_equal() {
							record_unify(&mut unify_map, &arr[0], b);
							mark_processed();
						}
					}
				}
				_ => {}
			}
		}
		for (k, li) in unify_map {
			if map.contains_key(&k) {
				continue;
			}
			let ty = &fzn.variables[&k].ty;
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
								if let Some(Domain::Int(d)) = &fzn.variables[id].domain {
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
						map.get(id).cloned()
					} else {
						None
					}
				})
				// Create a new variable if no view is found
				.unwrap_or_else(|| match domain {
					Some(Literal::Bool(b)) => BoolView::Const(b).into(),
					Some(Literal::IntSet(dom)) => prb.new_int_var(dom).into(),
					Some(_) => unreachable!(),
					None => match ty {
						Type::Bool => prb.new_bool_var().into(),
						Type::Int => panic!("unbounded integer variables are not supported yet"),
						_ => unreachable!(),
					},
				});

			// Map (or equate) all names in the group to the new variable
			for lit in li.iter() {
				if let Literal::Identifier(id) = lit {
					match map.entry(id.clone()) {
						Entry::Vacant(e) => {
							let _ = e.insert(var.clone());
						}
						Entry::Occupied(e) => match ty {
							Type::Bool => {
								let (ModelView::Bool(new), ModelView::Bool(existing)) =
									(var.clone(), e.get().clone())
								else {
									unreachable!()
								};
								prb += BoolExpr::Equiv(vec![new.into(), existing.into()])
							}
							Type::Int => {
								let (ModelView::Int(new), ModelView::Int(existing)) =
									(var.clone(), e.get().clone())
								else {
									unreachable!()
								};
								prb += Constraint::IntLinEq(vec![new, existing * -1], 0)
							}
							_ => unreachable!(),
						},
					}
				}
			}
		}

		// Traditional relational constraints
		for (i, c) in fzn.constraints.iter().enumerate() {
			if processed[i] {
				continue;
			}
			match c.id.deref() {
				"array_bool_and" => {
					if let [es, r] = c.args.as_slice() {
						let es = arg_array(fzn, es)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						let es: Result<Vec<_>, _> = es
							.iter()
							.map(|l| lit_bool(fzn, &mut prb, &mut map, l).map(Into::into))
							.collect();
						prb += BoolExpr::Equiv(vec![r.into(), BoolExpr::And(es?)]);
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
						let es = arg_array(fzn, es)?;
						let es: Result<Vec<BoolExpr>, _> = es
							.iter()
							.map(|l| lit_bool(fzn, &mut prb, &mut map, l).map(Into::into))
							.collect();
						prb += BoolExpr::Xor(es?);
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
						let arr: Vec<_> = arg_array(fzn, arr)?
							.iter()
							.map(|l| par_bool(fzn, l))
							.try_collect()?;
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						let val = arg_bool(fzn, &mut prb, &mut map, val)?;

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

						prb += Constraint::SetInReif(idx, RangeList::from_iter(ranges), val.into());
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
						let arr: Result<Vec<_>, _> = arg_array(fzn, arr)?
							.iter()
							.map(|l| par_int(fzn, l))
							.collect();
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						let val = arg_int(fzn, &mut prb, &mut map, val)?;
						prb += Constraint::ArrayIntElement(arr?, idx, val);
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
						let arr: Result<Vec<_>, FlatZincError> = arg_array(fzn, arr)?
							.iter()
							.map(|l| {
								let x: BoolView = lit_bool(fzn, &mut prb, &mut map, l)?;
								Ok(x.into())
							})
							.collect();
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						let val = arg_bool(fzn, &mut prb, &mut map, val)?;

						prb += Constraint::ArrayVarBoolElement(arr?, idx, val.into());
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
						let arr: Result<Vec<_>, _> = arg_array(fzn, arr)?
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.collect();
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						let val = arg_int(fzn, &mut prb, &mut map, val)?;
						prb += Constraint::ArrayVarIntElement(arr?, idx, val);
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
						let b = arg_bool(fzn, &mut prb, &mut map, b)?;
						let i = arg_int(fzn, &mut prb, &mut map, i)?;
						prb += Constraint::IntLinEq(vec![b.into(), -i], 0);
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
						let coeffs: Vec<_> = arg_array(fzn, coeffs)?
							.iter()
							.map(|l| par_int(fzn, l))
							.try_collect()?;
						let vars: Vec<_> = arg_array(fzn, vars)?
							.iter()
							.map(|l| lit_bool(fzn, &mut prb, &mut map, l))
							.try_collect()?;
						let sum = arg_int(fzn, &mut prb, &mut map, sum)?;
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| {
								NonZeroIntVal::new(c).map(|c| IntView::from(x) * c)
							})
							.chain(Some(-sum))
							.collect();
						prb += Constraint::IntLinEq(vars, 0);
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
						let pos = arg_array(fzn, pos)?;
						let neg = arg_array(fzn, neg)?;
						let mut lits = Vec::with_capacity(pos.len() + neg.len());
						for l in pos {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push(e.into());
						}
						for l in neg {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push((!e).into())
						}
						prb += BoolExpr::Or(lits);
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
						let a = arg_bool(fzn, &mut prb, &mut map, a)?;
						let b = arg_bool(fzn, &mut prb, &mut map, b)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						prb += BoolExpr::Equiv(vec![
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
						let a = arg_bool(fzn, &mut prb, &mut map, a)?;
						let b = arg_bool(fzn, &mut prb, &mut map, b)?;
						prb += BoolExpr::Equiv(vec![b.into(), (!a).into()]);
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
						let a = arg_bool(fzn, &mut prb, &mut map, &c.args[0])?;
						let b = arg_bool(fzn, &mut prb, &mut map, &c.args[1])?;
						let mut f = BoolExpr::Xor(vec![a.into(), b.into()]);
						if c.args.len() == 3 {
							let r = arg_bool(fzn, &mut prb, &mut map, &c.args[2])?;
							f = BoolExpr::Equiv(vec![r.into(), f]);
						}
						prb += f;
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
						let args = arg_array(fzn, args)?;
						let args: Result<Vec<_>, _> = args
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.collect();
						prb += Constraint::AllDifferentInt(args?);
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
						let starts = arg_array(fzn, starts)?
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.try_collect()?;
						let durations = arg_array(fzn, durations)?
							.iter()
							.map(|l| par_int(fzn, l))
							.try_collect()?;
						prb += Constraint::Disjunctive(starts, durations);
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
						let args = arg_array(fzn, args)?;
						let args: Result<Vec<_>, _> = args
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.collect();
						let m = arg_int(fzn, &mut prb, &mut map, m)?;
						if is_maximum {
							prb += Constraint::ArrayIntMaximum(args?, m);
						} else {
							prb += Constraint::ArrayIntMinimum(args?, m);
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
						let pos = arg_array(fzn, pos)?;
						let neg = arg_array(fzn, neg)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						let mut lits = Vec::with_capacity(pos.len() + neg.len());
						for l in pos {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push(e.into());
						}
						for l in neg {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push((!e).into())
						}
						prb += BoolExpr::Equiv(vec![r.into(), BoolExpr::Or(lits)]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"int_le" => {
					if let [a, b] = c.args.as_slice() {
						let a = arg_int(fzn, &mut prb, &mut map, a)?;
						let b = arg_int(fzn, &mut prb, &mut map, b)?;
						prb += Constraint::IntLinLessEq(vec![a, -b], 0);
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
						let a = arg_int(fzn, &mut prb, &mut map, a)?;
						let b = arg_int(fzn, &mut prb, &mut map, b)?;
						prb += Constraint::IntLinNotEq(vec![a, -b], 0);
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
						let a = arg_int(fzn, &mut prb, &mut map, a)?;
						let b = arg_int(fzn, &mut prb, &mut map, b)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						prb += match c.id.deref() {
							"int_eq_imp" => Constraint::IntLinEqImp,
							"int_eq_reif" => Constraint::IntLinEqImp,
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
						let coeffs: Vec<_> = arg_array(fzn, coeffs)?
							.iter()
							.map(|l| par_int(fzn, l))
							.try_collect()?;
						let vars: Vec<_> = arg_array(fzn, vars)?
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.try_collect()?;
						let rhs = arg_par_int(fzn, rhs)?;
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.collect();

						prb += match c.id.deref() {
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
						let coeffs: Vec<_> = arg_array(fzn, coeffs)?
							.iter()
							.map(|l| par_int(fzn, l))
							.try_collect()?;
						let vars: Vec<_> = arg_array(fzn, vars)?
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.try_collect()?;
						let rhs = arg_par_int(fzn, rhs)?;
						let reified = arg_bool(fzn, &mut prb, &mut map, reified)?;
						let vars: Vec<IntView> = vars
							.into_iter()
							.zip(coeffs.into_iter())
							.filter_map(|(x, c)| NonZeroIntVal::new(c).map(|c| x * c))
							.collect();
						prb += match c.id.deref() {
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
						let a = arg_int(fzn, &mut prb, &mut map, a)?;
						let b = arg_int(fzn, &mut prb, &mut map, b)?;
						let m = arg_int(fzn, &mut prb, &mut map, m)?;
						if is_maximum {
							prb += Constraint::ArrayIntMaximum(vec![a, b], m);
						} else {
							prb += Constraint::ArrayIntMinimum(vec![a, b], m);
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
						let base = arg_int(fzn, &mut prb, &mut map, base)?;
						let exponent = arg_int(fzn, &mut prb, &mut map, exponent)?;
						let res = arg_int(fzn, &mut prb, &mut map, res)?;

						prb += Constraint::IntPow(base, exponent, res);
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
						let a = arg_int(fzn, &mut prb, &mut map, x)?;
						let b = arg_int(fzn, &mut prb, &mut map, y)?;
						let m = arg_int(fzn, &mut prb, &mut map, z)?;
						prb += Constraint::IntTimes(a, b, m);
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
						let x = arg_int(fzn, &mut prb, &mut map, x)?;
						let s = arg_par_set(fzn, s)?;

						prb.intersect_int_domain(&x, &s, prb.constraints.len())?;
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
						let x = arg_int(fzn, &mut prb, &mut map, x)?;
						let s = arg_par_set(fzn, s)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;

						prb += Constraint::SetInReif(x, s, r.into());
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

		// Extract search annotations
		for ann in fzn.solve.ann.iter() {
			match ann {
				Annotation::Call(c)
					if matches!(c.id.deref(), "bool_search" | "int_search" | "seq_search") =>
				{
					let branchings = ann_to_branchings(fzn, &mut prb, &mut map, c)?;
					for b in branchings {
						prb += b;
					}
				}
				_ => warn!("unsupported search annotation: {}", ann),
			}
		}

		// Ensure all variables in the output are in the model
		for ident in fzn.output.iter() {
			let mut ensure_exists = |ident: &S, var| {
				if !map.contains_key(ident) {
					let _ = map.insert(ident.clone(), new_var(&mut prb, var));
				}
			};
			if let Some(var) = fzn.variables.get(ident) {
				ensure_exists(ident, var);
			} else if let Some(arr) = fzn.arrays.get(ident) {
				for x in &arr.contents {
					if let Literal::Identifier(ident) = x {
						if let Some(var) = fzn.variables.get(ident) {
							ensure_exists(ident, var)
						} else {
							return Err(FlatZincError::UnknownIdentifier(ident.to_string()));
						}
					}
				}
			} else {
				return Err(FlatZincError::UnknownIdentifier(ident.to_string()));
			}
		}

		Ok((prb, map))
	}
}

impl<Sol, Sat> Solver<Sat>
where
	Sol: PropagatorAccess + SatValuation,
	Sat: SatSolver + SolverTrait<ValueFn = Sol>,
{
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug + Display>(
		fzn: &FlatZinc<S>,
		config: &InitConfig,
	) -> Result<(Self, BTreeMap<S, SolverView>), FlatZincError> {
		let (mut prb, map) = Model::from_fzn(fzn)?;
		let (mut slv, remap) = prb.to_solver(config)?;
		let map = map
			.into_iter()
			.map(|(k, v)| (k, remap.get(&mut slv, &v)))
			.collect();
		Ok((slv, map))
	}
}

fn arg_array<'a, S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &'a FlatZinc<S>,
	arg: &'a Argument<S>,
) -> Result<&'a Vec<Literal<S>>, FlatZincError> {
	match arg {
		Argument::Array(x) => Ok(x),
		Argument::Literal(Literal::Identifier(ident)) => {
			if let Some(arr) = fzn.arrays.get(ident) {
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

fn ann_to_branchings<'a, S: Ord + Deref<Target = str> + Clone + Debug + Display>(
	fzn: &'a FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, ModelView>,
	c: &'a AnnotationCall<S>,
) -> Result<Vec<Branching>, FlatZincError> {
	let mut branchings = Vec::new();
	match c.id.deref() {
		"bool_search" => {
			if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
				let vars = ann_arg_var_array(fzn, vars)?
					.iter()
					.map(|l| lit_bool(fzn, prb, map, l))
					.try_collect()?;
				let var_sel = ann_var_sel(var_sel)?;
				let val_sel = ann_val_sel(val_sel)?;

				branchings.push(Branching::Bool(vars, var_sel, val_sel));
			} else {
				return Err(FlatZincError::InvalidNumArgs {
					name: "bool_search",
					found: c.args.len(),
					expected: 4,
				});
			}
		}
		"int_search" => {
			if let [vars, var_sel, val_sel, _] = c.args.as_slice() {
				let vars = ann_arg_var_array(fzn, vars)?
					.iter()
					.map(|l| lit_int(fzn, prb, map, l))
					.try_collect()?;
				let var_sel = ann_var_sel(var_sel)?;
				let val_sel = ann_val_sel(val_sel)?;

				branchings.push(Branching::Int(vars, var_sel, val_sel));
			} else {
				return Err(FlatZincError::InvalidNumArgs {
					name: "int_search",
					found: c.args.len(),
					expected: 4,
				});
			}
		}
		"seq_search" => {
			if let [AnnotationArgument::Array(searches)] = c.args.as_slice() {
				searches.iter().for_each(|search| {
					if let AnnotationLiteral::Annotation(Annotation::Call(sub_call)) = search {
						let res = ann_to_branchings(fzn, prb, map, sub_call);
						if let Ok(mut bs) = res {
							branchings.append(&mut bs);
						}
					}
				})
			} else {
				return Err(FlatZincError::InvalidNumArgs {
					name: "seq_search",
					found: c.args.len(),
					expected: 1,
				});
			}
		}
		_ => warn!("unsupported search annotation: {}", c),
	}
	Ok(branchings)
}

// Get an array of variable literals from an annotation argument
fn ann_arg_var_array<'a, S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &'a FlatZinc<S>,
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
		AnnotationArgument::Literal(AnnotationLiteral::BaseLiteral(Literal::Identifier(ident))) => {
			if let Some(arr) = fzn.arrays.get(ident) {
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

fn arg_has_length<'a, S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &'a FlatZinc<S>,
	arg: &'a Argument<S>,
	len: usize,
) -> bool {
	match arg {
		Argument::Array(x) => x.len() == len,
		Argument::Literal(Literal::Identifier(ident)) => {
			if let Some(arr) = fzn.arrays.get(ident) {
				arr.contents.len() == len
			} else {
				false
			}
		}
		_ => false,
	}
}

fn new_var<S: Ord + Deref<Target = str> + Clone + Debug>(
	prb: &mut Model,
	var: &Variable<S>,
) -> ModelView {
	match var.ty {
		Type::Bool => ModelView::Bool(prb.new_bool_var()),
		Type::Int => match &var.domain {
			Some(Domain::Int(r)) => ModelView::Int(prb.new_int_var(r.iter().collect())),
			Some(_) => unreachable!(),
			None => todo!("Variables without a domain are not yet supported"),
		},
		_ => todo!("Variables of {:?} are not yet supported", var.ty),
	}
}

fn lit_bool<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, ModelView>,
	lit: &Literal<S>,
) -> Result<BoolView, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Bool {
					// TODO: Add boolean views of integers
					let ModelView::Bool(ret) = map
						.entry(ident.clone())
						.or_insert_with(|| new_var(prb, var))
					else {
						unreachable!()
					};
					Ok(ret.clone())
				} else {
					Err(FlatZincError::InvalidArgumentType {
						expected: "bool",
						found: format!("{:?}", var.ty),
					})
				}
			} else {
				Err(FlatZincError::UnknownIdentifier(ident.to_string()))
			}
		}
		Literal::Bool(v) => Ok(BoolView::Const(*v)),
		_ => todo!(),
	}
}

fn par_bool<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	lit: &Literal<S>,
) -> Result<bool, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Bool && var.value.is_some() {
					par_bool(fzn, var.value.as_ref().unwrap())
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

fn arg_bool<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, ModelView>,
	arg: &Argument<S>,
) -> Result<BoolView, FlatZincError> {
	match arg {
		Argument::Literal(l) => lit_bool(fzn, prb, map, l),
		_ => Err(FlatZincError::InvalidArgumentType {
			expected: "boolean literal",
			found: format!("{:?}", arg),
		}),
	}
}

fn ann_var_sel<S: Ord + Deref<Target = str> + Clone + Debug + Display>(
	arg: &AnnotationArgument<S>,
) -> Result<VariableSelection, FlatZincError> {
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

fn ann_val_sel<S: Ord + Deref<Target = str> + Clone + Debug + Display>(
	arg: &AnnotationArgument<S>,
) -> Result<ValueSelection, FlatZincError> {
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

fn lit_int<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, ModelView>,
	lit: &Literal<S>,
) -> Result<IntView, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Int {
					let ModelView::Int(ret) = map
						.entry(ident.clone())
						.or_insert_with(|| new_var(prb, var))
					else {
						unreachable!()
					};
					Ok(ret.clone())
				} else {
					Err(FlatZincError::InvalidArgumentType {
						expected: "int",
						found: format!("{:?}", var.ty),
					})
				}
			} else {
				Err(FlatZincError::UnknownIdentifier(ident.to_string()))
			}
		}
		Literal::Bool(v) => Ok(IntView::Const(if *v { 1 } else { 0 })),
		Literal::Int(v) => Ok(IntView::Const(*v)),
		_ => todo!(),
	}
}

fn par_int<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	lit: &Literal<S>,
) -> Result<IntVal, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Int && var.value.is_some() {
					par_int(fzn, var.value.as_ref().unwrap())
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

fn arg_int<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, ModelView>,
	arg: &Argument<S>,
) -> Result<IntView, FlatZincError> {
	match arg {
		Argument::Literal(l) => lit_int(fzn, prb, map, l),
		_ => Err(FlatZincError::InvalidArgumentType {
			expected: "integer literal",
			found: format!("{:?}", arg),
		}),
	}
}

fn arg_par_int<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	arg: &Argument<S>,
) -> Result<IntVal, FlatZincError> {
	match arg {
		Argument::Literal(l) => par_int(fzn, l),
		_ => Err(FlatZincError::InvalidArgumentType {
			expected: "par integer literal",
			found: format!("{:?}", arg),
		}),
	}
}

fn par_set<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	lit: &Literal<S>,
) -> Result<IntSetVal, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::IntSet && var.value.is_some() {
					par_set(fzn, var.value.as_ref().unwrap())
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

fn arg_par_set<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	arg: &Argument<S>,
) -> Result<IntSetVal, FlatZincError> {
	match arg {
		Argument::Literal(l) => par_set(fzn, l),
		_ => Err(FlatZincError::InvalidArgumentType {
			expected: "par set literal",
			found: format!("{:?}", arg),
		}),
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
