use std::collections::BTreeMap;

use flatzinc_serde::{Argument, FlatZinc, Literal, Type, Variable};
use pindakaas::Cnf;
use thiserror::Error;

use crate::{
	solver::SatSolver, BoolExpr, Constraint, Model, SimplifiedVariable, Solver, Variable as MVar,
};

impl Model {
	pub fn from_fzn(fzn: &FlatZinc) -> Result<(Self, BTreeMap<String, MVar>), FlatZincError> {
		let mut map = BTreeMap::<String, MVar>::new();
		let mut prb = Model::default();

		let new_var = |prb: &mut Model, var: &Variable| match var.ty {
			Type::Bool => MVar::Bool(prb.new_bool_var()),
			Type::Int => todo!(),
			_ => unreachable!(),
		};
		let mut lit_bool = |prb: &mut Model, lit: &Literal| match lit {
			Literal::Identifier(ident) => {
				if let Some(var) = fzn.variables.get(ident) {
					if var.ty == Type::Bool {
						// TODO: Add boolean views of integers
						let MVar::Bool(ret) = map
							.entry(ident.clone())
							.or_insert_with(|| new_var(prb, var));
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
		};
		let _arg_bool = |prb, arg: &Argument| match arg {
			Argument::Literal(l) => lit_bool(prb, l),
			Argument::Array(_) => Err(FlatZincError::InvalidArgumentType {
				expected: "bool",
				found: "array".into(),
			}),
		};

		for c in fzn.constraints.iter() {
			match c.id.as_str() {
				"bool_clause" => {
					if let [pos, neg] = c.args.as_slice() {
						let pos = arg_array(fzn, pos)?;
						let neg = arg_array(fzn, neg)?;
						let mut lits = Vec::with_capacity(pos.len() + neg.len());
						for l in pos {
							let e = lit_bool(&mut prb, l)?;
							lits.push(e);
						}
						for l in neg {
							let e = lit_bool(&mut prb, l)?;
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

impl<S: SatSolver + From<Cnf>> Solver<S> {
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
