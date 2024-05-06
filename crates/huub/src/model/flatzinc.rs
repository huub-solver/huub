use std::{collections::BTreeMap, fmt::Debug, ops::Deref};

use flatzinc_serde::{Argument, Domain, FlatZinc, Literal, Type, Variable};
use thiserror::Error;

use super::{bool::BoolExpr, reformulate::ReformulationError};
use crate::{
	model::{IntExpr, Variable as MVar},
	Constraint, Model, Solver, SolverView,
};

impl Model {
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, MVar>), FlatZincError> {
		let mut map = BTreeMap::<S, MVar>::new();
		let mut prb = Model::default();

		for c in fzn.constraints.iter() {
			match c.id.deref() {
				"array_bool_and" => {
					if let [es, r] = c.args.as_slice() {
						let es = arg_array(fzn, es)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						let es: Result<Vec<_>, _> = es
							.iter()
							.map(|l| lit_bool(fzn, &mut prb, &mut map, l))
							.collect();
						prb += BoolExpr::Equiv(vec![r, BoolExpr::And(es?)]);
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
						let es: Result<Vec<_>, _> = es
							.iter()
							.map(|l| lit_bool(fzn, &mut prb, &mut map, l))
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
							lits.push(e);
						}
						for l in neg {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push(!e)
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
				"bool_clause_reif" => {
					if let [pos, neg, r] = c.args.as_slice() {
						let pos = arg_array(fzn, pos)?;
						let neg = arg_array(fzn, neg)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						let mut lits = Vec::with_capacity(pos.len() + neg.len());
						for l in pos {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push(e);
						}
						for l in neg {
							let e = lit_bool(fzn, &mut prb, &mut map, l)?;
							lits.push(!e)
						}
						prb += BoolExpr::Equiv(vec![r, BoolExpr::Or(lits)]);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause_reif",
							found: c.args.len(),
							expected: 3,
						});
					}
				}
				"bool_eq_reif" => {
					if let [a, b, r] = c.args.as_slice() {
						let a = arg_bool(fzn, &mut prb, &mut map, a)?;
						let b = arg_bool(fzn, &mut prb, &mut map, b)?;
						let r = arg_bool(fzn, &mut prb, &mut map, r)?;
						prb += BoolExpr::Equiv(vec![r, BoolExpr::Equiv(vec![a, b])]);
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
						// TODO: This should not need two variables
						prb += BoolExpr::Equiv(vec![b, !a]);
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
						let mut f = BoolExpr::Xor(vec![a, b]);
						if c.args.len() == 3 {
							let r = arg_bool(fzn, &mut prb, &mut map, &c.args[2])?;
							f = BoolExpr::Equiv(vec![r, f]);
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
				"int_lin_le" | "int_lin_eq" => {
					let is_eq = c.id.deref() == "int_lin_eq";
					if let [coeffs, vars, rhs] = c.args.as_slice() {
						let coeffs = arg_array(fzn, coeffs)?;
						let vars = arg_array(fzn, vars)?;
						let Argument::Literal(Literal::Int(rhs)) = rhs else {
							return Err(FlatZincError::InvalidArgumentType {
								expected: "int",
								found: format!("{:?}", rhs),
							});
						};
						let coeffs: Result<Vec<_>, _> = coeffs
							.iter()
							.map(|l| match l {
								Literal::Int(v) => Ok(*v),
								_ => Err(FlatZincError::InvalidArgumentType {
									expected: "int",
									found: format!("{:?}", l),
								}),
							})
							.collect();
						let vars: Result<Vec<_>, _> = vars
							.iter()
							.map(|l| lit_int(fzn, &mut prb, &mut map, l))
							.collect();
						prb += if is_eq {
							Constraint::IntLinEq
						} else {
							Constraint::IntLinLessEq
						}(coeffs?, vars?, *rhs);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: if is_eq { "int_lin_eq" } else { "int_linear_le" },
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

// TODO: Make generic on underlying solver
impl Solver {
	pub fn from_fzn<S: Ord + Deref<Target = str> + Clone + Debug>(
		fzn: &FlatZinc<S>,
	) -> Result<(Self, BTreeMap<S, SolverView>), FlatZincError> {
		let (prb, map) = Model::from_fzn(fzn)?;
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
) -> MVar {
	match var.ty {
		Type::Bool => MVar::Bool(prb.new_bool_var()),
		Type::Int => match &var.domain {
			Some(Domain::Int(r)) => MVar::Int(prb.new_int_var(r.clone())),
			Some(_) => unreachable!(),
			None => todo!("Variables without a domain are not yet supported"),
		},
		_ => todo!("Variables of {:?} are not yet supported", var.ty),
	}
}

fn lit_bool<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, MVar>,
	lit: &Literal<S>,
) -> Result<BoolExpr, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Bool {
					// TODO: Add boolean views of integers
					let MVar::Bool(ret) = map
						.entry(ident.clone())
						.or_insert_with(|| new_var(prb, var))
					else {
						unreachable!()
					};
					Ok(BoolExpr::Lit((*ret).into()))
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
		Literal::Bool(v) => Ok(BoolExpr::Val(*v)),
		_ => todo!(),
	}
}

fn arg_bool<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, MVar>,
	arg: &Argument<S>,
) -> Result<BoolExpr, FlatZincError> {
	match arg {
		Argument::Literal(l) => lit_bool(fzn, prb, map, l),
		_ => Err(FlatZincError::InvalidArgumentType {
			expected: "bool",
			found: format!("{:?}", arg),
		}),
	}
}

fn lit_int<S: Ord + Deref<Target = str> + Clone + Debug>(
	fzn: &FlatZinc<S>,
	prb: &mut Model,
	map: &mut BTreeMap<S, MVar>,
	lit: &Literal<S>,
) -> Result<IntExpr, FlatZincError> {
	match lit {
		Literal::Identifier(ident) => {
			if let Some(var) = fzn.variables.get(ident) {
				if var.ty == Type::Int {
					let MVar::Int(ret) = map
						.entry(ident.clone())
						.or_insert_with(|| new_var(prb, var))
					else {
						unreachable!()
					};
					Ok(IntExpr::Var(*ret))
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
		Literal::Bool(v) => Ok(IntExpr::Val(if *v { 1 } else { 0 })),
		Literal::Int(v) => Ok(IntExpr::Val(*v)),
		_ => todo!(),
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
