use std::{collections::BTreeMap, fmt::Debug, ops::Deref};

use flatzinc_serde::{Argument, Domain, FlatZinc, Literal, Type, Variable};
use thiserror::Error;

use super::{
	bool::{BoolExpr, BoolView},
	int::IntView,
	reformulate::ReformulationError,
	ModelView,
};
use crate::{Constraint, IntVal, Model, Solver, SolverView};

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
					("bool_not", Some(l)) => {
						if let [a, b] = c.args.as_slice() {
							match (a, b) {
								(Argument::Literal(Literal::Identifier(x)), b)
								| (b, Argument::Literal(Literal::Identifier(x)))
									if x == l =>
								{
									let b = arg_bool(fzn, &mut prb, &mut map, b)?;
									let _ = map.insert(l.clone(), (!b).into());
									return Ok(true);
								}
								_ => {}
							}
						}
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
							expected: 2,
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
						prb += Constraint::AllDifferent(args?);
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
							prb += Constraint::Maximum(args?, m);
						} else {
							prb += Constraint::Minimum(args?, m);
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
				"int_lin_le" | "int_lin_eq" => {
					let is_eq = c.id.deref() == "int_lin_eq";
					if let [coeffs, vars, rhs] = c.args.as_slice() {
						let coeffs = arg_array(fzn, coeffs)?;
						let vars = arg_array(fzn, vars)?;
						let rhs = arg_par_int(fzn, rhs)?;
						let coeffs: Result<Vec<_>, _> =
							coeffs.iter().map(|l| par_int(fzn, l)).collect();
						let vars: Result<Vec<_>, _> = vars
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.collect();
						prb += if is_eq {
							Constraint::IntLinEq
						} else {
							Constraint::IntLinLessEq
						}(coeffs?, vars?, rhs);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: if is_eq { "int_lin_eq" } else { "int_linear_le" },
							found: c.args.len(),
							expected: 3,
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
							prb += Constraint::Maximum(vec![a, b], m);
						} else {
							prb += Constraint::Minimum(vec![a, b], m);
						}
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: if is_maximum { "int_max" } else { "int_min" },
							found: c.args.len(),
							expected: 2,
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

// TODO: Make generic on underlying solver
impl Solver {
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, SolverView>), FlatZincError> {
		let (mut prb, map) = Model::from_fzn(fzn)?;
		let (slv, remap) = prb.to_solver()?;
		let map = map.into_iter().map(|(k, v)| (k, remap.get(&v))).collect();
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
					Ok(*ret)
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
