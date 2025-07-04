//! Module for the creation of a [`Model`] from a [`Xcsp3Instance`] instance.

use std::{
	collections::HashMap,
	fmt::{Debug, Display},
	hash::Hash,
	iter::once,
	ops::Deref,
};

use rangelist::RangeList;
use thiserror::Error;

use xcsp3_serde::{
	constraint::Constraint,
	error::UnrollError,
	expression::{BoolExp, Exp, IntExp},
	Instance as Xcsp3Instance, ObjType, Objective, SimpleRef,
};

use crate::{
	abs_int, actions::SimplificationActions, all_different_int, array_maximum_int,
	array_minimum_int, div_int, pow_int, reformulate::ReformulationError, solver::Goal, table_int,
	times_int, BoolDecision, BoolFormula, Decision, IntDecision, IntDecisionInner, IntLinExpr,
	IntVal, Model,
};

#[derive(Error, Debug)]
/// Errors that can occur when converting a [`Xcsp3Instance`] instance to a
/// [`Model`] or [`Solver`] object.
pub enum Xcsp3Error {
	#[error("identifier `{0}' is defined more than once")]
	/// XCSP3 instance used an identifier multiple times.
	DuplicateIdentifier(String),
	#[error("argument found of type `{found}', expected `{expected}'")]
	/// FlatZinc constraint or annotation used an argument of the wrong type.
	InvalidArgumentType {
		/// Expected type of the argument.
		expected: &'static str,
		/// Type of the argument found.
		found: String,
	},
	#[error("could not find identifier `{0}'")]
	/// XCSP3 instance used an identifier that was not defined.
	UnknownIdentifier(String),
	#[error("xcsp3 instance contains an unsupported constraint type `{0}'")]
	/// XCSP3 instance contained a constraint with an unsupported constraint
	UnsupportedConstraint(&'static str),
	#[error("xcsp3 instance contains an unsupported feature type `{0}'")]
	/// XCSP3 instance contained a constraint with an unsupported constraint
	UnsupportedFeature(&'static str),
	#[error("{0:?} type variables are not supported by huub")]
	/// XCSP3 instance contained a decision variable with an unsupported type.
	UnsupportedType(&'static str),
	#[error("an error occurred when unrolling instance constraints: {0}")]
	/// An error occurred when resolving the instance into a flat constraint list.
	UnrollError(#[from] UnrollError),
	#[error("error reformulating generated model `{0}'")]
	/// Error that occorred when converting a generated [`Model`] to a [`Solver`]
	/// object.
	ReformulationError(#[from] ReformulationError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// Statistical information about the extraction process that creates a
/// [`Model`] from a [`Xcsp3Instance`].
pub struct Xcsp3Statistics {
	/// Number of literal views extracted from the [`Xcsp3Instance`] specification
	extracted_views: u32,
	/// Number of variables removed by unification
	vars_unified: u32,
}

/// Builder for creating a [`Model`] from a [`Xcsp3Instance`].
pub(crate) struct Xcsp3ModelBuilder<'a, S: Eq + Hash + Ord> {
	/// The FlatZinc instance to build the model from
	instance: &'a Xcsp3Instance<S>,
	/// A mapping from identifiers and expressions to decisions
	expr_map: HashMap<Exp<SimpleRef<S>>, Decision>,
	/// A mapping from array identifiers to (flat) vector of decisions and the dimensions
	array_map: HashMap<S, (Vec<Decision>, Vec<usize>)>,
	/// The incumbent model
	prb: Model,
	/// Statistics about the extraction process
	stats: Xcsp3Statistics,
}

/// Function to initialize an uncomputed domain.
// TODO: This should be removed in the future.
fn full_domain() -> RangeList<IntVal> {
	// These bounds are not IntVal::MIN..=IntVal::MAX, because the cardinality of
	// individual ranges must be representable as IntVal in the `rangelist`
	// library.
	let r = IntVal::MAX >> 1;
	RangeList::from(-r..=r)
}

fn resolve_index(idxs: &[usize], dims: &[usize]) -> usize {
	debug_assert_eq!(idxs.len(), dims.len());
	let mut mult = 1;
	let mut idx = 0;
	for (i, size) in idxs.iter().zip(dims) {
		idx += mult * i;
		mult *= size;
	}
	idx
}

impl Xcsp3Statistics {
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

impl<'a, S> Xcsp3ModelBuilder<'a, S>
where
	S: Clone + Debug + Deref<Target = str> + Display + Eq + Hash + Ord,
{
	/// Create the decisions defined in the variable and array fields of the
	/// [`Xcsp3Instance`].
	pub(crate) fn create_decisions(&mut self) -> Result<(), Xcsp3Error> {
		let create_var = |prb: &mut Model, dom: RangeList<IntVal>| -> Decision {
			if dom == RangeList::from(0..=1) {
				prb.new_bool_var().into()
			} else {
				prb.new_int_var(dom).into()
			}
		};

		// Create all singleton variables
		for vardef in &self.instance.variables {
			let dom = vardef.domain.iter().collect();
			let var = create_var(&mut self.prb, dom);
			let prev = self
				.expr_map
				.insert(Exp::Var(SimpleRef::Ident(vardef.identifier.clone())), var);
			if prev.is_some() {
				return Err(Xcsp3Error::DuplicateIdentifier(
					vardef.identifier.to_string(),
				));
			}
		}

		// Create all arrays of variables
		for arr in &self.instance.arrays {
			let arr = arr.unroll()?;
			// Find the base domain of the variables (if no specific domains are
			// provided).
			let base = arr
				.domains
				.iter()
				.find_map(|(v, dom)| {
					if v.iter().any(|v| match v {
						SimpleRef::Ident(v) if &**v == "others" => todo!(),
						_ => false,
					}) {
						Some(dom.iter().collect())
					} else {
						None
					}
				})
				// Create fixed value if no domain is provided (undefined variable)
				.unwrap_or_else(|| RangeList::from(0..=0));

			// Determine number of elements and create positions
			let len: usize = arr.size.iter().product();
			let mut vars: Vec<Option<Decision>> = vec![None; len];

			// Initialize specialized domains for variables
			for (v, dom) in arr.domains.iter() {
				let dom = dom.iter().collect();
				for v in v {
					// TODO: Maybe throw an error if the identifier does not match
					match v {
						SimpleRef::ArrayAccess(_, idxs) => {
							let idx = resolve_index(idxs, &arr.size);
							if let Some(d) = &vars[idx] {
								// TODO: Duplicate domain definition, intersect domains or throw error?
								match d {
									Decision::Bool(_) => todo!(),
									&Decision::Int(iv) => self.prb.set_int_in_set(iv, &dom)?,
								}
							} else {
								vars[idx] = Some(create_var(&mut self.prb, dom.clone()));
							}
						}
						SimpleRef::Ident(_) => {}
					}
				}
			}

			// Initialize all other variables
			let vars = vars
				.into_iter()
				.map(|v| {
					if v.is_some() {
						v.unwrap()
					} else {
						create_var(&mut self.prb, base.clone())
					}
				})
				.collect();
			// Store variables and sizes to later resolve array accesses
			let prev = self
				.array_map
				.insert(arr.identifier.clone(), (vars, arr.size.clone()));
			if prev.is_some() {
				return Err(Xcsp3Error::DuplicateIdentifier(arr.identifier.to_string()));
			}
		}
		Ok(())
	}

	/// Create branchers according to the search annotations in the FlatZinc instance
	pub(crate) fn create_branchers(&mut self) -> Result<(), Xcsp3Error> {
		// let mut branchings = Vec::new();
		// let mut warm_start = Vec::new();
		// for ann in self.fzn.solve.ann.iter() {
		// 	match ann {
		// 		Annotation::Call(c) => {
		// 			let (w, b) = self.ann_to_branchings(c)?;
		// 			warm_start.extend(w);
		// 			branchings.extend(b);
		// 		}
		// 		_ => warn!("ignoring unsupported search annotation: {}", ann),
		// 	}
		// }
		// if !warm_start.is_empty() {
		// 	self.prb += Branching::WarmStart(warm_start);
		// }
		// for b in branchings {
		// 	self.prb += b;
		// }
		Ok(())
	}

	fn enforce_bool_exp(&mut self, exp: &BoolExp<SimpleRef<S>>) -> Result<(), Xcsp3Error> {
		match exp {
			BoolExp::Const(true) => Ok(()),
			BoolExp::Const(false) => Err(Xcsp3Error::ReformulationError(
				ReformulationError::TrivialUnsatisfiable,
			)),
			exp @ BoolExp::Var(_) => {
				let var = self.extract_bool(&exp)?;
				self.prb.set_bool(var)?;
				Ok(())
			}
			BoolExp::Not(exp) => {
				let var = self.extract_bool(&exp)?;
				self.prb.set_bool(var)?;
				Ok(())
			}
			BoolExp::And(sub) => {
				for exp in sub {
					self.enforce_bool_exp(exp)?;
				}
				Ok(())
			}
			BoolExp::Equiv(sub) | BoolExp::Or(sub) | BoolExp::Xor(sub) => {
				let sub = self
					.extract_bool_list(sub)?
					.into_iter()
					.map(BoolFormula::Atom)
					.collect();
				let f = match exp {
					BoolExp::Equiv(_) => BoolFormula::Equiv,
					BoolExp::Or(_) => BoolFormula::Or,
					BoolExp::Xor(_) => BoolFormula::Xor,
					_ => unreachable!(),
				};
				self.prb += f(sub);
				Ok(())
			}
			BoolExp::Implies(a, b) => {
				let a = self.extract_bool(&a)?;
				let b = self.extract_bool(&b)?;
				self.prb +=
					BoolFormula::Implies(BoolFormula::Atom(a).into(), BoolFormula::Atom(b).into());
				Ok(())
			}
			BoolExp::LessThan(a, b)
			| BoolExp::LessThanEq(a, b)
			| BoolExp::GreaterThan(a, b)
			| BoolExp::GreaterThanEq(a, b) => {
				let a = self.extract_int_lin(&a)?;
				let b = self.extract_int_lin(&b)?;
				let lin = a - b;

				match lin.terms.len() {
					// No remaining terms, check against constant 0
					0 => {
						match exp {
							BoolExp::LessThan(_, _) | BoolExp::GreaterThan(_, _) => {
								// 0 is not .lt(0) or .gt(0)
								return Err(ReformulationError::TrivialUnsatisfiable.into());
							}
							BoolExp::LessThanEq(_, _) | BoolExp::GreaterThanEq(_, _) => {}
							_ => unreachable!(),
						};
					}
					// One remaining term, change the domains allowed
					1 => {
						let var = lin.terms[0];
						match exp {
							BoolExp::LessThan(_, _) => self.prb.set_int_upper_bound(var, -1)?,
							BoolExp::LessThanEq(_, _) => self.prb.set_int_upper_bound(var, 0)?,
							BoolExp::GreaterThan(_, _) => self.prb.set_int_lower_bound(var, 1)?,
							BoolExp::GreaterThanEq(_, _) => self.prb.set_int_lower_bound(var, 0)?,
							_ => unreachable!(),
						};
					}
					// Multiple terms, create linear constraint
					_ => {
						let lin = match exp {
							BoolExp::LessThan(_, _) => lin.lt(0),
							BoolExp::LessThanEq(_, _) => lin.leq(0),
							BoolExp::GreaterThan(_, _) => lin.gt(0),
							BoolExp::GreaterThanEq(_, _) => lin.geq(0),
							_ => unreachable!(),
						};
						self.prb += lin;
					}
				}

				Ok(())
			}
			BoolExp::NotEqual(_, _) => todo!(),
			BoolExp::Equal(_) => todo!(),
			BoolExp::Member(_, _) => Err(Xcsp3Error::UnsupportedConstraint("member")),
			BoolExp::Disjoint(_, _) => Err(Xcsp3Error::UnsupportedConstraint("disjoint")),
			BoolExp::SubSet(_, _) => Err(Xcsp3Error::UnsupportedConstraint("subset")),
			BoolExp::SubSetEq(_, _) => Err(Xcsp3Error::UnsupportedConstraint("subset")),
			BoolExp::SuperSet(_, _) => Err(Xcsp3Error::UnsupportedConstraint("superset")),
			BoolExp::SuperSetEq(_, _) => Err(Xcsp3Error::UnsupportedConstraint("superset")),
			BoolExp::Convex(_) => Err(Xcsp3Error::UnsupportedConstraint("convex")),
		}
	}

	/// Extract one or more Boolean decision variables from a [`BoolExp`] in a
	/// [`Xcsp3Instance`]. A [`Xcsp3Error`] will be returned if the expression is
	/// invalid or unsupported.
	fn extract_bool(&mut self, exp: &BoolExp<SimpleRef<S>>) -> Result<BoolDecision, Xcsp3Error> {
		let map_to_bool = |v: Decision| match v {
			Decision::Bool(bv) => Ok(bv),
			Decision::Int(_) => Err(Xcsp3Error::InvalidArgumentType {
				expected: "bool",
				found: "int".into(),
			}),
		};
		let key = Exp::Bool(exp.clone().into());
		if let Some(var) = self.expr_map.get(&key) {
			return map_to_bool(var.clone());
		}
		debug_assert!(!self.expr_map.contains_key(&key));
		match exp {
			&BoolExp::Const(b) => Ok(b.into()),
			BoolExp::Var(var) => map_to_bool(self.extract_var(var)?),
			BoolExp::Not(sub) => {
				let sub = self.extract_bool(sub)?;
				Ok(!sub)
			}
			BoolExp::And(sub) | BoolExp::Equiv(sub) | BoolExp::Or(sub) | BoolExp::Xor(sub) => {
				// Recursively extract boolean variables from sub-expressions
				let sub = self.extract_bool_list(sub)?;
				// Create reification variable
				let ret = self.prb.new_bool_var();
				// Create relational constraint
				let f = match exp {
					BoolExp::And(_) => BoolFormula::And,
					BoolExp::Equiv(_) => BoolFormula::Equiv,
					BoolExp::Or(_) => BoolFormula::Or,
					BoolExp::Xor(_) => BoolFormula::Xor,
					_ => unreachable!(),
				};
				self.prb += BoolFormula::Equiv(vec![
					BoolFormula::Atom(ret),
					f(sub.into_iter().map(BoolFormula::Atom).collect()),
				]);
				// TODO: Normalize
				// Add result to CSE map
				let _ = self.expr_map.insert(key, ret.into());
				Ok(ret)
			}
			BoolExp::Implies(_, _) => todo!(),
			BoolExp::LessThan(_, _) => todo!(),
			BoolExp::LessThanEq(_, _) => todo!(),
			BoolExp::GreaterThan(_, _) => todo!(),
			BoolExp::GreaterThanEq(_, _) => todo!(),
			BoolExp::NotEqual(_, _) => todo!(),
			BoolExp::Equal(_) => todo!(),
			BoolExp::Member(_, _) => todo!(),
			BoolExp::Disjoint(_, _) => todo!(),
			BoolExp::SubSet(_, _) => todo!(),
			BoolExp::SubSetEq(_, _) => todo!(),
			BoolExp::SuperSet(_, _) => todo!(),
			BoolExp::SuperSetEq(_, _) => todo!(),
			BoolExp::Convex(_) => todo!(),
		}
	}

	/// Extract a list of integer decision variables from a list of [`IntExp`] in
	/// a [`Xcsp3Instance`]. A [`Xcsp3Error`] will be returned if the expression
	/// is invalid or unsupported.
	fn extract_bool_list(
		&mut self,
		exp: &[BoolExp<SimpleRef<S>>],
	) -> Result<Vec<BoolDecision>, Xcsp3Error> {
		exp.iter().map(|v| self.extract_bool(v)).collect()
	}

	pub(crate) fn extract_goal(&mut self) -> Result<Option<(Goal, IntDecision)>, Xcsp3Error> {
		if self.instance.objectives.is_empty() {
			return Ok(None);
		}
		if self.instance.objectives.objectives.len() > 1 {
			return Err(Xcsp3Error::UnsupportedFeature(
				"multi objective optimization",
			));
		}
		let (g, e) = match &self.instance.objectives.objectives[0] {
			Objective::Minimize(e) => (Goal::Minimize, e),
			Objective::Maximize(e) => (Goal::Maximize, e),
		};
		let e = e.unroll(self.instance)?;
		let list = if e.coeffs.is_empty() {
			e.list
		} else if e.list.len() == e.coeffs.len() {
			e.list
				.into_iter()
				.zip(e.coeffs)
				.map(|(v, c)| IntExp::Mul(vec![IntExp::Const(c), v]))
				.collect()
		} else {
			todo!()
		};
		let e = match e.ty {
			ObjType::Sum => IntExp::Add,
			ObjType::Minimum => IntExp::Min,
			ObjType::Maximum => IntExp::Max,
			ObjType::NValues => todo!(),
			ObjType::Lex => todo!(),
		}(list);
		self.extract_int(&e).map(|e| Some((g, e)))
	}

	/// Extract one or more integer decision variables from a [`IntExp`] in a
	/// [`Xcsp3Instance`]. A [`Xcsp3Error`] will be returned if the expression is
	/// invalid or unsupported.
	fn extract_int(&mut self, exp: &IntExp<SimpleRef<S>>) -> Result<IntDecision, Xcsp3Error> {
		let map_to_int = |v: Decision| match v {
			Decision::Bool(bv) => bv.into(),
			Decision::Int(iv) => iv,
		};
		let key = Exp::Int(exp.clone().into());
		if let Some(var) = self.expr_map.get(&key) {
			return Ok(map_to_int(var.clone()));
		}
		debug_assert!(!self.expr_map.contains_key(&key));
		match exp {
			&IntExp::Const(c) => Ok(IntDecision(IntDecisionInner::Const(c))),
			IntExp::Var(var) => Ok(map_to_int(self.extract_var(var)?)),
			IntExp::Neg(exp) => {
				let v = self.extract_int(exp)?;
				Ok(-v)
			}
			IntExp::Abs(sub) => {
				let sub = self.extract_int(sub)?;
				let r = self.prb.new_int_var(full_domain());
				self.prb += abs_int(sub, r);
				let _ = self.expr_map.insert(key, r.into());
				Ok(r)
			}
			exp @ IntExp::Add(_) => {
				let mut lin = self.extract_int_lin(exp)?;
				match lin.terms.len() {
					0 => Ok(0.into()),
					1 => Ok(lin.terms[0]),
					_ => {
						// Create returned decision variable
						let ret = self.prb.new_int_var(full_domain());
						lin -= ret;
						self.prb += lin.eq(0);
						// Store result in CSE map
						// TODO: normalize before storing in CSE map
						let _ = self.expr_map.insert(key, Decision::Int(ret));
						// Return the created decision variable
						Ok(ret)
					}
				}
			}
			IntExp::Sub(a, b) => self.extract_int(&IntExp::Add(vec![
				(**a).clone(),
				IntExp::Neg(b.clone()).into(),
			])),
			IntExp::Mul(sub) => {
				let rsub = self.extract_int_list(sub)?;
				let mut c = 1;
				let mut inc = None;
				for (i, &v) in rsub.iter().enumerate() {
					if let IntDecisionInner::Const(k) = v.0 {
						c *= k;
					} else if let Some(x) = inc {
						// Create a new decision variable for the (intermediate) product
						let r = self.prb.new_int_var(full_domain());
						// Post relational int_times constraint
						self.prb += times_int(v, x, r);
						// Store (intermediate) product in CSE map using original expression
						let _ = self.expr_map.insert(
							Exp::Int(IntExp::Mul(sub[0..=i].iter().cloned().collect()).into()),
							Decision::Int(r),
						);
						inc = Some(r);
					} else {
						inc = Some(v);
					}
				}

				Ok(match inc {
					Some(v) => v * c,
					None => c.into(),
				})
			}
			IntExp::Div(a, b) | IntExp::Pow(a, b) => {
				// Extract different variables
				let a = self.extract_int(a)?;
				let b = self.extract_int(b)?;
				// Create returned decision variable
				let r = self.prb.new_int_var(full_domain());
				match exp {
					IntExp::Div(_, _) => self.prb += div_int(a, b, r),
					IntExp::Pow(_, _) => self.prb += pow_int(a, b, r),
					_ => unreachable!(),
				}
				// Store result in CSE map
				let _ = self.expr_map.insert(key, r.into());
				Ok(r)
			}
			IntExp::Max(sub) | IntExp::Min(sub) => {
				// Extract list of subexpressions
				let vars: Vec<_> = self.extract_int_list(sub)?;
				// Create returned decision variable
				let ret = self.prb.new_int_var(full_domain());
				// Post relational constraint
				match exp {
					IntExp::Add(_) => {
						let lin: IntLinExpr = vars.iter().copied().chain(once(ret)).sum();
						self.prb += lin.eq(0);
					}
					IntExp::Max(_) => self.prb += array_maximum_int(vars, ret),
					IntExp::Min(_) => self.prb += array_minimum_int(vars, ret),
					_ => unreachable!(),
				}
				// Store result in CSE map
				// TODO: normalize before storing in CSE map
				let _ = self.expr_map.insert(key, ret.into());
				// Return the created decision variable
				Ok(ret)
			}
			IntExp::Dist(a, b) => {
				// TODO: normalize
				self.extract_int(&IntExp::Abs(IntExp::Sub(a.clone(), b.clone()).into()))
			}
			IntExp::Bool(bv) => {
				let bv = self.extract_bool(bv)?;
				Ok(bv.into())
			}
			IntExp::Mod(_, _) => todo!(),
			IntExp::Sqr(_) => todo!(),
			IntExp::If(_, _, _) => todo!(),
			IntExp::Card(_) => todo!(),
		}
	}

	fn extract_int_lin(&mut self, exp: &IntExp<SimpleRef<S>>) -> Result<IntLinExpr, Xcsp3Error> {
		match exp {
			IntExp::Add(sub) => {
				let mut lin = IntLinExpr { terms: Vec::new() };
				for term in sub {
					lin += self.extract_int_lin(term)?
				}
				Ok(lin)
			}
			IntExp::Sub(a, b) => Ok(self.extract_int_lin(a)? - self.extract_int_lin(b)?),
			IntExp::Neg(a) => Ok(-self.extract_int_lin(a)?),
			IntExp::Mul(sub) => {
				let mut x = None;
				let mut mult = 1;
				for term in sub {
					match term {
						IntExp::Const(c) => mult *= c,
						v if x == None => {
							x = Some(self.extract_int_lin(v)?);
						}
						_ => return self.extract_int(exp).map(|e| IntLinExpr { terms: vec![e] }),
					}
				}
				match x {
					Some(lin) => Ok(lin * mult),
					None => Ok(IntLinExpr {
						terms: vec![mult.into()],
					}),
				}
			}
			exp => self.extract_int(exp).map(|e| IntLinExpr { terms: vec![e] }),
		}
	}

	/// Extract a list of integer decision variables from a list of [`IntExp`] in
	/// a [`Xcsp3Instance`]. A [`Xcsp3Error`] will be returned if the expression
	/// is invalid or unsupported.
	fn extract_int_list(
		&mut self,
		exp: &[IntExp<SimpleRef<S>>],
	) -> Result<Vec<IntDecision>, Xcsp3Error> {
		exp.iter().map(|v| self.extract_int(v)).collect()
	}

	fn extract_var(&mut self, var: &SimpleRef<S>) -> Result<Decision, Xcsp3Error> {
		match var {
			SimpleRef::Ident(x) => {
				if let Some(vars) = self.expr_map.get(&Exp::Var(SimpleRef::Ident(x.clone()))) {
					Ok(vars.clone())
				} else {
					Err(Xcsp3Error::UnknownIdentifier(x.to_string()))
				}
			}
			SimpleRef::ArrayAccess(ident, idxs) => {
				if let Some((vars, dims)) = self.array_map.get(&ident) {
					let idx = resolve_index(idxs, dims);
					Ok(vars[idx].clone())
				} else {
					Err(Xcsp3Error::UnknownIdentifier(ident.to_string()))
				}
			}
		}
	}

	/// Finalize the builder and return the model
	pub(crate) fn finalize<MapTy: FromIterator<(S, Vec<Decision>)>>(
		self,
	) -> (Model, MapTy, Xcsp3Statistics) {
		(
			self.prb,
			self.expr_map
				.into_iter()
				.filter_map(|(k, v)| {
					if let Exp::Var(SimpleRef::Ident(ident)) = k {
						Some((ident, vec![v]))
					} else {
						None
					}
				})
				.chain(
					self.array_map
						.into_iter()
						.map(|(ident, (vars, _))| (ident, vars)),
				)
				.collect(),
			self.stats,
		)
	}

	/// Create a new builder to create a model from a FlatZinc instance
	pub(crate) fn new(fzn: &'a Xcsp3Instance<S>) -> Self {
		Self {
			instance: fzn,
			expr_map: HashMap::new(),
			array_map: HashMap::new(),
			prb: Model::default(),
			stats: Xcsp3Statistics::default(),
		}
	}

	/// Process the [`FlatZinc::constraints`] field and add [`Constraint`] items
	/// to the [`Model`] to enforce the constraints.
	pub(crate) fn post_constraints(&mut self) -> Result<(), Xcsp3Error> {
		// Traditional relational constraints
		let constraints = self.instance.unroll_constraints()?;
		for c in constraints {
			match c {
				Constraint::AllDifferent(con) => {
					if con.except.len() != 0 {
						return Err(Xcsp3Error::UnsupportedConstraint("all_different_except"));
					}
					let vars = self.extract_int_list(&con.list)?;
					self.prb += all_different_int(vars);
				}
				Constraint::AllEqual(con) => {
					if con.except.len() == 0 {
						return Err(Xcsp3Error::UnsupportedConstraint("all_equal_except"));
					}
					let vars = self.extract_int_list(&con.list)?;
					if let Some(&var) = vars.get(0) {
						for &v in vars.iter().skip(1) {
							self.prb.unify_int(var, v)?;
						}
					}
				}
				Constraint::BinPacking(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("bin_packing"))
				}
				Constraint::Cardinality(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("cardinality"))
				}
				Constraint::Channel(_) => return Err(Xcsp3Error::UnsupportedConstraint("channel")),
				Constraint::Circuit(_) => return Err(Xcsp3Error::UnsupportedConstraint("circuit")),
				Constraint::Count(_) => return Err(Xcsp3Error::UnsupportedConstraint("count")),
				Constraint::Cumulative(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("cumulative"))
				}
				Constraint::Element(_) => return Err(Xcsp3Error::UnsupportedConstraint("element")),
				Constraint::Extension(con) => {
					let vars = self.extract_int_list(&con.list)?;
					if con.conflicts.len() > 0 {
						for tup in con.conflicts.iter() {
							if tup.len() != vars.len() {
								return Err(Xcsp3Error::InvalidArgumentType {
									expected: "extension value tuple",
									found: "value tuple of the wrong length".to_string(),
								});
							}
							self.prb += BoolFormula::Or(
								vars.iter()
									.zip(tup.iter())
									.map(|(var, &val)| BoolFormula::Atom(var.ne(val)))
									.collect(),
							);
						}
					}
					if con.supports.len() > 0 {
						for tup in con.supports.iter() {
							if tup.len() != vars.len() {
								return Err(Xcsp3Error::InvalidArgumentType {
									expected: "extension value tuple",
									found: "value tuple of the wrong length".to_string(),
								});
							}
						}
						self.prb += table_int(vars, con.supports.clone());
					}
				}
				Constraint::Instantiation(con) => {
					let vars: Vec<_> = con
						.list
						.iter()
						.map(|v| self.extract_int(&IntExp::Var(v.clone())))
						.collect::<Result<Vec<_>, _>>()?;
					for (&var, &val) in vars.iter().zip(con.values.iter()) {
						self.prb.set_int_val(var, val)?;
					}
				}
				Constraint::Intension(con) => self.enforce_bool_exp(&con.function)?,
				Constraint::Knapsack(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("knapsack"))
				}
				Constraint::Maximum(_) => return Err(Xcsp3Error::UnsupportedConstraint("maximum")),
				Constraint::Mdd(_) => return Err(Xcsp3Error::UnsupportedConstraint("mdd")),
				Constraint::Minimum(_) => return Err(Xcsp3Error::UnsupportedConstraint("minimum")),
				Constraint::NValues(_) => return Err(Xcsp3Error::UnsupportedConstraint("nvalues")),
				Constraint::NoOverlap(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("no_overlap"))
				}
				Constraint::Ordered(_) => return Err(Xcsp3Error::UnsupportedConstraint("ordered")),
				Constraint::Precedence(_) => {
					return Err(Xcsp3Error::UnsupportedConstraint("precedence"))
				}
				Constraint::Regular(_) => return Err(Xcsp3Error::UnsupportedConstraint("regular")),
				Constraint::Sum(_) => return Err(Xcsp3Error::UnsupportedConstraint("sum")),
			}
		}

		Ok(())
	}
}
