//! The `.fzt` model language: the representation of constraints and terms,
//! and the writing of the decisions of a [`Model`] as terms.

use std::{
	borrow::Cow,
	error::Error,
	fmt::{self, Display, Write},
	num::NonZero,
};

use crate::{
	IntSet, IntVal,
	model::{
		Decision, Model, View,
		decision::integer::Domain,
		preprocess::state::PreprocessTrace,
		view::{boolean::BoolView, integer::IntView},
	},
	views::LinearBoolView,
};

/// The domain that a FlatZinc variable is declared with.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclaredDomain {
	/// A Boolean variable.
	Bool,
	/// An integer variable with the given domain, or without a domain.
	Int(Option<IntSet>),
}

/// An argument of a constraint in the `.fzt` model language.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum FztArg {
	/// An array of arguments.
	Array(Vec<FztArg>),
	/// A Boolean constant.
	Bool(bool),
	/// An integer constant.
	///
	/// The value is wide enough to hold the accumulated right-hand side of a
	/// linear constraint that may overflow a 64-bit integer.
	Int(i128),
	/// A constant set of integers.
	Set(IntSet),
	/// A term over the decisions of the model, as created by a
	/// [`FztContext`].
	Term(FztTerm),
}

/// A constraint in the `.fzt` model language: a predicate applied to a list of
/// arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FztConstraint {
	/// The predicate of the constraint.
	pub(super) name: Cow<'static, str>,
	/// The arguments of the predicate.
	pub(super) args: Vec<FztArg>,
}

/// Context used by
/// [`Constraint::to_fzt`](crate::constraints::Constraint::to_fzt) to write the
/// decisions that a constraint refers to as `.fzt` terms.
///
/// Views are written as terms over the decisions that are still part of the
/// model, following the aliases created by unification. Unlike the resolution
/// used during simplification, this never evaluates a view against the current
/// domains: the checker performs the same substitutions, but does not know the
/// domain-dependent shortcuts that Huub takes.
#[derive(Clone, Copy, Debug)]
pub struct FztContext<'a> {
	/// The model whose decisions are written.
	model: &'a Model,
}

/// Error that occurs when the preprocessing trace cannot be produced.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum FztError {
	/// A constraint of the model cannot be written in the `.fzt` model
	/// language.
	UnsupportedConstraint {
		/// The name of the type of the constraint.
		constraint: &'static str,
	},
	/// The objective of the instance is not a decision variable.
	UnsupportedObjective,
	/// A constraint was changed without it ever having been logged.
	UnloggedConstraint,
}

/// A term over the decisions of the model in the `.fzt` model language.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FztTerm(pub(super) String);

/// Write `c*atom + a`, omitting a unit coefficient unless `explicit`.
pub(super) fn affine(scale: IntVal, atom: &str, offset: IntVal, explicit: bool) -> String {
	let mut s = match scale {
		1 if !explicit => atom.to_owned(),
		-1 if !explicit => format!("-{atom}"),
		_ => format!("{scale}*{atom}"),
	};
	match offset.cmp(&0) {
		std::cmp::Ordering::Greater => write!(s, " + {offset}").unwrap(),
		std::cmp::Ordering::Less => write!(s, " - {}", -(offset as i128)).unwrap(),
		std::cmp::Ordering::Equal => {}
	}
	s
}

/// Write the declared domain of a FlatZinc variable in the `.fzt` model
/// language.
pub(super) fn fzt_declared(domain: &DeclaredDomain) -> String {
	match domain {
		DeclaredDomain::Bool => "bool".to_owned(),
		DeclaredDomain::Int(Some(d)) => fzt_domain(d),
		DeclaredDomain::Int(None) => "int".to_owned(),
	}
}

/// Write a domain in the `.fzt` model language.
pub(crate) fn fzt_domain(domain: &IntSet) -> String {
	let ranges: Vec<_> = domain.iter().map(|r| (*r.start(), *r.end())).collect();
	match ranges.as_slice() {
		[] => "{}".to_owned(),
		[(a, b)] if a == b => format!("{{{a}}}"),
		[(a, b)] => format!("{a}..{b}"),
		_ => {
			let parts: Vec<_> = ranges
				.iter()
				.map(|(a, b)| {
					if a == b {
						a.to_string()
					} else {
						format!("{a}..{b}")
					}
				})
				.collect();
			format!("{{{}}}", parts.join(", "))
		}
	}
}

impl Display for FztArg {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			FztArg::Array(v) => {
				f.write_str("[")?;
				for (i, a) in v.iter().enumerate() {
					if i > 0 {
						f.write_str(", ")?;
					}
					Display::fmt(a, f)?;
				}
				f.write_str("]")
			}
			FztArg::Bool(b) => write!(f, "{b}"),
			FztArg::Int(i) => write!(f, "{i}"),
			FztArg::Set(s) => f.write_str(&fzt_domain(s)),
			FztArg::Term(t) => f.write_str(&t.0),
		}
	}
}

impl From<IntVal> for FztArg {
	fn from(value: IntVal) -> Self {
		FztArg::Int(value.into())
	}
}

impl From<Vec<FztArg>> for FztArg {
	fn from(value: Vec<FztArg>) -> Self {
		FztArg::Array(value)
	}
}

impl FztConstraint {
	/// The predicate of the constraint.
	pub fn name(&self) -> &str {
		&self.name
	}

	/// Create a constraint that applies the predicate `name` to `args`.
	pub fn new(name: impl Into<Cow<'static, str>>, args: Vec<FztArg>) -> Self {
		Self {
			name: name.into(),
			args,
		}
	}
}

impl Display for FztConstraint {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}(", self.name)?;
		for (i, a) in self.args.iter().enumerate() {
			if i > 0 {
				f.write_str(", ")?;
			}
			Display::fmt(a, f)?;
		}
		f.write_str(")")
	}
}

impl<'a> FztContext<'a> {
	/// Write a Boolean view as an argument.
	pub fn bool(&self, view: impl Into<View<bool>>) -> FztArg {
		let view = view.into();
		match self.resolve_bool(view).0 {
			BoolView::Const(b) => FztArg::Bool(b),
			_ => FztArg::Term(FztTerm(self.bool_term(view))),
		}
	}

	/// The name of a (non-negated) Boolean decision.
	pub(super) fn bool_name(&self, var: Decision<bool>) -> Cow<'a, str> {
		let idx = var.idx();
		match self.trace().bool_names.get(idx) {
			Some(Some(name)) => Cow::Borrowed(name.as_str()),
			_ => Cow::Owned(format!("huub__b{idx}")),
		}
	}

	/// Write a Boolean view as a term, e.g. `b`, `!b`, or `[x >= 3]`.
	pub(crate) fn bool_term(&self, view: View<bool>) -> String {
		match self.resolve_bool(view).0 {
			BoolView::Const(b) => b.to_string(),
			BoolView::Decision(l) => {
				let name = self.bool_name(l.var());
				if l.is_negated() {
					format!("!{name}")
				} else {
					name.into_owned()
				}
			}
			BoolView::IntEq(x, k) => format!("[{} == {k}]", self.int_name(x)),
			BoolView::IntNotEq(x, k) => format!("[{} != {k}]", self.int_name(x)),
			BoolView::IntGreaterEq(x, k) => format!("[{} >= {k}]", self.int_name(x)),
			BoolView::IntLess(x, k) => match k.checked_sub(1) {
				Some(k) => format!("[{} <= {k}]", self.int_name(x)),
				None => "false".to_owned(),
			},
		}
	}

	/// Write a list of Boolean views as an array argument.
	pub fn bools<V: Into<View<bool>>>(&self, views: impl IntoIterator<Item = V>) -> FztArg {
		FztArg::Array(views.into_iter().map(|v| self.bool(v)).collect())
	}

	/// Write a propositional formula over Boolean views in the encoding of the
	/// `huub_formula` predicate.
	///
	/// The formula is written as an integer array `ops`, in which each node
	/// occupies consecutive positions, and an array `atoms` of Boolean terms.
	/// The root of the formula is at position 1, and a node is one of:
	///
	/// - `[0, i]`: the `i`-th element of `atoms`,
	/// - `[1, c]`: the negation of the node at position `c`,
	/// - `[2, n, c1, …, cn]`: the conjunction of the nodes at the positions
	///   `c1, …, cn`,
	/// - `[3, n, c1, …, cn]`: their disjunction,
	/// - `[4, n, c1, …, cn]`: whether an odd number of them hold,
	/// - `[5, n, c1, …, cn]`: whether they are all equal,
	/// - `[6, a, b]`: the implication from node `a` to node `b`,
	/// - `[7, c, t, e]`: if node `c` holds then node `t`, else node `e`.
	pub(crate) fn formula_encoding(
		&self,
		formula: &pindakaas::propositional_logic::Formula<View<bool>>,
	) -> (FztArg, FztArg) {
		use pindakaas::propositional_logic::Formula;

		/// Append the node for `f` to `ops`, returning its (1-based) position.
		fn encode(
			ctx: &FztContext<'_>,
			f: &Formula<View<bool>>,
			ops: &mut Vec<IntVal>,
			atoms: &mut Vec<FztArg>,
		) -> IntVal {
			let pos = ops.len() as IntVal + 1;
			let nary = |code: IntVal,
			            fs: &[Formula<View<bool>>],
			            ops: &mut Vec<IntVal>,
			            atoms: &mut Vec<FztArg>| {
				let start = ops.len();
				ops.push(code);
				ops.push(fs.len() as IntVal);
				ops.extend(std::iter::repeat_n(0, fs.len()));
				for (i, f) in fs.iter().enumerate() {
					let child = encode(ctx, f, ops, atoms);
					ops[start + 2 + i] = child;
				}
			};
			match f {
				Formula::Atom(a) => {
					atoms.push(ctx.bool(*a));
					ops.extend([0, atoms.len() as IntVal]);
				}
				Formula::Not(g) => {
					let start = ops.len();
					ops.extend([1, 0]);
					let child = encode(ctx, g, ops, atoms);
					ops[start + 1] = child;
				}
				Formula::And(fs) => nary(2, fs, ops, atoms),
				Formula::Or(fs) => nary(3, fs, ops, atoms),
				Formula::Xor(fs) => nary(4, fs, ops, atoms),
				Formula::Equiv(fs) => nary(5, fs, ops, atoms),
				Formula::Implies(a, b) => {
					let start = ops.len();
					ops.extend([6, 0, 0]);
					let a = encode(ctx, a, ops, atoms);
					ops[start + 1] = a;
					let b = encode(ctx, b, ops, atoms);
					ops[start + 2] = b;
				}
				Formula::IfThenElse { cond, then, els } => {
					let start = ops.len();
					ops.extend([7, 0, 0, 0]);
					let c = encode(ctx, cond, ops, atoms);
					ops[start + 1] = c;
					let t = encode(ctx, then, ops, atoms);
					ops[start + 2] = t;
					let e = encode(ctx, els, ops, atoms);
					ops[start + 3] = e;
				}
			}
			pos
		}

		let mut ops = Vec::new();
		let mut atoms = Vec::new();
		let _ = encode(self, formula, &mut ops, &mut atoms);
		(
			FztArg::Array(ops.into_iter().map(FztArg::from).collect()),
			FztArg::Array(atoms),
		)
	}

	/// Write an integer view as an argument.
	pub fn int(&self, view: impl Into<View<IntVal>>) -> FztArg {
		let view = self.resolve_int(view.into());
		match view.0 {
			IntView::Const(c) => c.into(),
			_ => FztArg::Term(FztTerm(self.int_term(view))),
		}
	}

	/// The name of an integer decision.
	pub(super) fn int_name(&self, var: Decision<IntVal>) -> Cow<'a, str> {
		let idx = var.idx();
		match self.trace().int_names.get(idx) {
			Some(Some(name)) => Cow::Borrowed(name.as_str()),
			_ => Cow::Owned(format!("huub__i{idx}")),
		}
	}

	/// Write an integer view as a term, e.g. `5`, `x`, `2*x - 1`, or `3*b +
	/// 1`.
	pub(crate) fn int_term(&self, view: View<IntVal>) -> String {
		match self.resolve_int(view).0 {
			IntView::Const(c) => c.to_string(),
			IntView::Linear(lin) => {
				affine(lin.scale.get(), &self.int_name(lin.var), lin.offset, false)
			}
			IntView::Bool(lin) => {
				affine(lin.scale.get(), &self.bool_term(lin.var), lin.offset, true)
			}
		}
	}

	/// Write a list of integer views as an array argument.
	pub fn ints<V: Into<View<IntVal>>>(&self, views: impl IntoIterator<Item = V>) -> FztArg {
		FztArg::Array(views.into_iter().map(|v| self.int(v)).collect())
	}

	/// Write the linear expression `terms` compared to `rhs` as the
	/// coefficients, the variables, and the right-hand side of an `int_lin_*`
	/// constraint, folding the offsets of the terms into the right-hand side.
	pub(crate) fn linear(
		&self,
		terms: impl IntoIterator<Item = View<IntVal>>,
		rhs: i128,
	) -> (FztArg, FztArg, FztArg) {
		let mut rhs = rhs;
		let mut coeffs = Vec::new();
		let mut vars = Vec::new();
		for t in terms {
			match self.resolve_int(t).0 {
				IntView::Const(c) => rhs -= i128::from(c),
				IntView::Linear(lin) => {
					coeffs.push(lin.scale.get().into());
					vars.push(FztArg::Term(FztTerm(self.int_name(lin.var).into_owned())));
					rhs -= i128::from(lin.offset);
				}
				IntView::Bool(lin) => {
					coeffs.push(lin.scale.get().into());
					vars.push(FztArg::Term(FztTerm(affine(
						1,
						&self.bool_term(lin.var),
						0,
						true,
					))));
					rhs -= i128::from(lin.offset);
				}
			}
		}
		(FztArg::Array(coeffs), FztArg::Array(vars), FztArg::Int(rhs))
	}

	/// Write the name of a variable, which has no decision of its own, as an
	/// argument.
	pub(crate) fn name(&self, name: &str) -> FztArg {
		FztArg::Term(FztTerm(name.to_owned()))
	}

	/// Create a context to write the decisions of `model`.
	pub(crate) fn new(model: &'a Model) -> Self {
		debug_assert!(model.trace.recording().is_some());
		Self { model }
	}

	/// Follow the aliases of a Boolean view to a view over decisions that are
	/// still part of the model.
	///
	/// A literal view over an integer decision is rewritten through the
	/// alias of the integer decision, e.g. `[x >= 3]` becomes `[y >= 1]` when
	/// `x` has been unified with `2*y + 1`.
	pub(crate) fn resolve_bool(&self, view: View<bool>) -> View<bool> {
		let mut result = view;
		loop {
			let next = match result.0 {
				BoolView::Decision(lit) => match self.model.bool_vars[lit.idx()].alias {
					Some(alias) if lit.is_negated() => !alias,
					Some(alias) => alias,
					None => return result,
				},
				BoolView::Const(_) => return result,
				BoolView::IntEq(x, k) => self.resolve_int(x.into()).eq(k),
				BoolView::IntNotEq(x, k) => self.resolve_int(x.into()).ne(k),
				BoolView::IntGreaterEq(x, k) => self.resolve_int(x.into()).geq(k),
				BoolView::IntLess(x, k) => self.resolve_int(x.into()).lt(k),
			};
			if next == result {
				return result;
			}
			result = next;
		}
	}

	/// Follow the aliases of an integer view to a view over decisions that are
	/// still part of the model.
	pub(crate) fn resolve_int(&self, view: View<IntVal>) -> View<IntVal> {
		let mut view = view;
		let mut scale: IntVal = 1;
		let mut offset: IntVal = 0;
		loop {
			match view.0 {
				IntView::Const(c) => return (c * scale + offset).into(),
				IntView::Linear(lin) => match self.model.int_vars[lin.var.idx()].domain {
					Domain::Domain(_) => {
						return View(IntView::Linear(lin * NonZero::new(scale).unwrap() + offset));
					}
					Domain::Alias(alias) => {
						view = alias;
						offset += scale * lin.offset;
						scale *= lin.scale.get();
					}
				},
				IntView::Bool(lin) => {
					let var = self.resolve_bool(lin.var);
					if let BoolView::Const(b) = var.0 {
						return (lin.transform_val(b as IntVal) * scale + offset).into();
					}
					let lin = LinearBoolView::new(lin.scale, lin.offset, var);
					return View(IntView::Bool(lin * NonZero::new(scale).unwrap() + offset));
				}
			}
		}
	}

	/// Write a constant set of integers as an argument.
	pub fn set(&self, set: &IntSet) -> FztArg {
		FztArg::Set(set.clone())
	}

	/// The recording state of the model.
	pub(super) fn trace(&self) -> &'a PreprocessTrace {
		self.model.trace.recording().unwrap()
	}
}

impl Display for FztError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			FztError::UnsupportedConstraint { constraint } => write!(
				f,
				"the constraint `{constraint}` cannot be written to the preprocessing trace"
			),
			FztError::UnsupportedObjective => write!(
				f,
				"the objective must be a decision variable to write the preprocessing trace"
			),
			FztError::UnloggedConstraint => write!(
				f,
				"a constraint was changed before it was written to the preprocessing trace"
			),
		}
	}
}

impl Error for FztError {}
