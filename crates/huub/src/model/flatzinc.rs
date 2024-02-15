use std::collections::BTreeMap;

use flatzinc_serde::{Argument, Domain, FlatZinc, Literal, Type, Variable};
use thiserror::Error;

use crate::{
	model::{IntExpr, Variable as MVar},
	BoolExpr, Constraint, Model, SimplifiedVariable, Solver,
};

impl Model {
	pub fn from_fzn(fzn: &FlatZinc) -> Result<(Self, BTreeMap<String, MVar>), FlatZincError> {
		let mut map = BTreeMap::<String, MVar>::new();
		let mut prb = Model::default();

		for c in fzn.constraints.iter() {
			match c.id.as_str() {
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
							lits.push(match e {
								BoolExpr::Lit(l) => BoolExpr::Lit(!l),
								BoolExpr::Val(v) => BoolExpr::Val(!v),
								e => BoolExpr::Not(Box::new(e)),
							})
						}
						prb += Constraint::Clause(lits);
					} else {
						return Err(FlatZincError::InvalidNumArgs {
							name: "bool_clause",
							found: c.args.len(),
							expected: 2,
						});
					}
				}
				"huub_all_different_int" => {
					if let [args] = c.args.as_slice() {
						let args = arg_array(fzn, args)?;
						let args: Result<Vec<_>, _> = args
							.into_iter()
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
				_ => return Err(FlatZincError::UnknownConstraint(c.id.clone())),
			}
		}

		// Ensure all variables in the output are in the model
		for ident in fzn.output.iter() {
			let mut ensure_exists = |ident: &String, var| {
				if !map.contains_key(ident) {
					map.insert(ident.clone(), new_var(&mut prb, var));
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
							return Err(FlatZincError::UnknownIdentifier(ident.into()));
						}
					}
				}
			} else {
				return Err(FlatZincError::UnknownIdentifier(ident.into()));
			}
		}

		Ok((prb, map))
	}
}

// TODO: Make generic on underlying solver
impl Solver {
	pub fn from_fzn(
		fzn: &FlatZinc,
	) -> Result<(Self, BTreeMap<String, SimplifiedVariable>), FlatZincError> {
		let (prb, map) = Model::from_fzn(fzn)?;
		let (slv, remap) = prb.to_solver();
		let map = map.into_iter().map(|(k, v)| (k, remap.get(&v))).collect();
		Ok((slv, map))
	}
}

fn arg_array<'a>(fzn: &'a FlatZinc, arg: &'a Argument) -> Result<&'a Vec<Literal>, FlatZincError> {
	match arg {
		Argument::Array(x) => Ok(x),
		Argument::Literal(Literal::Identifier(ident)) => {
			if let Some(arr) = fzn.arrays.get(ident) {
				Ok(&arr.contents)
			} else {
				Err(FlatZincError::UnknownIdentifier(ident.clone()))
			}
		}
		Argument::Literal(x) => Err(FlatZincError::InvalidArgumentType {
			expected: "array",
			found: format!("{:?}", x),
		}),
	}
}

fn new_var(prb: &mut Model, var: &Variable) -> MVar {
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

fn lit_bool(
	fzn: &FlatZinc,
	prb: &mut Model,
	map: &mut BTreeMap<String, MVar>,
	lit: &Literal,
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
				Err(FlatZincError::UnknownIdentifier(ident.clone()))
			}
		}
		Literal::Bool(v) => Ok(BoolExpr::Val(*v)),
		_ => todo!(),
	}
}

fn lit_int(
	fzn: &FlatZinc,
	prb: &mut Model,
	map: &mut BTreeMap<String, MVar>,
	lit: &Literal,
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
				Err(FlatZincError::UnknownIdentifier(ident.clone()))
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
}
