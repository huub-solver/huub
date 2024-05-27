use std::{collections::BTreeMap, fmt::Debug, ops::Deref};

use flatzinc_serde::{Argument, Domain, FlatZinc, Literal, Type, Variable};
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatorAccess, Solver as SolverTrait},
	Valuation as SatValuation,
};
use thiserror::Error;

use crate::{
	model::{
		bool::{BoolExpr, BoolView},
		int::IntView,
		reformulate::ReformulationError,
		ModelView,
	},
	solver::SatSolver,
	Constraint, IntVal, Model, NonZeroIntVal, Solver, SolverView,
};

impl Model {
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, ModelView>), FlatZincError> {
		let mut map = BTreeMap::<S, ModelView>::new();
		let mut prb = Model::default();

		// Extract views from `defines_var` constraints
		let processed = fzn
			.constraints
			.iter()
			.map(|c| {
				match (c.id.deref(), c.defines.as_ref()) {
					("bool2int", Some(l)) => {
						if let [b, Argument::Literal(Literal::Identifier(x))] = c.args.as_slice() {
							if x == l {
								let b = arg_bool(fzn, &mut prb, &mut map, b)?;
								let _ = map.insert(l.clone(), IntView::from(b).into());
								return Ok(true);
							}
						}
					}
					("bool_not", Some(l)) => match c.args.as_slice() {
						[Argument::Literal(Literal::Identifier(x)), b]
						| [b, Argument::Literal(Literal::Identifier(x))]
							if x == l =>
						{
							let b = arg_bool(fzn, &mut prb, &mut map, b)?;
							let _ = map.insert(l.clone(), (!b).into());
							return Ok(true);
						}
						_ => {}
					},
					("int_eq_reif", Some(l)) => match c.args.as_slice() {
						[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))] |
						[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
							if r == l =>
						{
							let x = lit_int(fzn, &mut prb, &mut map, x)?;
							let _ = map.insert(l.clone(), BoolView::IntEq(Box::new(x), *i).into());
							return Ok(true);
						}
						_ => {}
					},
					("int_le_reif", Some(l)) => match c.args.as_slice() {
						[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))]
							if r == l =>
						{
							let x = lit_int(fzn, &mut prb, &mut map, x)?;
							let _ = map.insert(l.clone(), BoolView::IntLessEq(Box::new(x), *i).into());
							return Ok(true);
						}
						[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
								if r == l =>
							{
								let x = lit_int(fzn, &mut prb, &mut map, x)?;
								let _ = map.insert(l.clone(), BoolView::IntGreater(Box::new(x), *i).into());
								return Ok(true);
							}
						_ => {}
					},
					("int_ne_reif", Some(l)) => match c.args.as_slice() {
						[Argument::Literal(Literal::Int(i)), Argument::Literal(x), Argument::Literal(Literal::Identifier(r))] |
						[Argument::Literal(x), Argument::Literal(Literal::Int(i)), Argument::Literal(Literal::Identifier(r))]
							if r == l =>
						{
							let x = lit_int(fzn, &mut prb, &mut map, x)?;
							let _ = map.insert(l.clone(), BoolView::IntNotEq(Box::new(x), *i).into());
							return Ok(true);
						}
						_ => {}
					},
					("int_lin_eq", Some(l))
						if c.args
							.get(1)
							.map(|v| arg_has_length(fzn, v, 2))
							.unwrap_or(false) =>
					{
						let [coeff, vars, sum] = c.args.as_slice() else {
							return Ok(false);
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
							_ => return Ok(false),
						};
						let sum = arg_par_int(fzn, sum)?;
						// c * l + cy * y = sum === l = (sum - cy * y) / c
						if cy % c != 0 || sum % c != 0 {
							return Ok(false);
						}
						let offset = sum / c;
						let view = if let Some(scale) = NonZeroIntVal::new(-cy / c) {
							let y = lit_int(fzn, &mut prb, &mut map, vy)?;
							y * scale + offset
						} else {
							IntView::Const(offset)
						};
						let _ = map.insert(l.clone(), view.into());
						return Ok(true);
					}
					_ => {}
				}
				Ok(false)
			})
			.collect::<Result<Vec<_>, FlatZincError>>()?;

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
				"array_int_element" => {
					if let [idx, arr, val] = c.args.as_slice() {
						let arr = arg_array(fzn, arr)?;
						let idx = arg_int(fzn, &mut prb, &mut map, idx)?;
						let val = arg_int(fzn, &mut prb, &mut map, val)?;
						let arr: Result<Vec<_>, _> = arr.iter().map(|l| par_int(fzn, l)).collect();
						// add clause (idx = i + 1) => (val = arr[i])
						(arr?).iter().enumerate().for_each(|(i, x)| {
							prb += BoolExpr::Implies(
								Box::new(BoolExpr::View(BoolView::IntEq(
									Box::new(idx.clone()),
									(i + 1) as i64,
								))),
								Box::new(BoolExpr::View(BoolView::IntEq(
									Box::new(val.clone()),
									*x,
								))),
							);
						});
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "array_int_element",
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
							"int_lin_eq_imp" => Constraint::IntLinLessEqImp,
							"int_lin_eq_reif" => Constraint::IntLinLessEqReif,
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
				_ => return Err(FlatZincError::UnknownConstraint(c.id.to_string())),
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
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, SolverView>), FlatZincError> {
		let (mut prb, map) = Model::from_fzn(fzn)?;
		let (slv, remap) = prb.to_solver()?;
		let map = map
			.into_iter()
			.map(|(k, v)| (k, remap.get(&slv, &v)))
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
			Some(Domain::Int(r)) => ModelView::Int(prb.new_int_var(r.clone())),
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
