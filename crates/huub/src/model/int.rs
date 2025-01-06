//! Representation and manipulation of integer decision variable in [`Model`].

use std::ops::{Add, Mul, Neg, Sub};

use index_vec::define_index_type;
use pindakaas::solver::propagation::PropagatingSolver;

use crate::{
	helpers::linear_transform::LinearTransform,
	model::{bool::BoolView, reformulate::VariableMap},
	solver::{engine::Engine, view},
	IntLinExpr, IntSetVal, IntVal, LitMeaning, NonZeroIntVal, Solver,
};

define_index_type! {
	/// Reference type for integer decision variables in a [`Model`].
	pub struct IntVar = u32;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Defintition of an integer decision variable in a [`Model`].
pub(crate) struct IntVarDef {
	/// The set of possible values that the variable can take.
	pub(crate) domain: IntSetVal,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A reference to an integer value or its transformation in a [`Model`].
pub enum IntExpr {
	/// Direct reference to an integer variable.
	Var(IntVar),
	/// Constant integer value.
	Const(i64),
	/// Linear transformation of an integer variable.
	Linear(LinearTransform, IntVar),
	/// Linear transformation of a Boolean variable.
	Bool(LinearTransform, BoolView),
}

impl IntVarDef {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSetVal) -> Self {
		Self {
			domain: dom,
			constraints: Vec::new(),
		}
	}
}

impl IntExpr {
	/// Get the [`view::IntView`] to which the expression will be mapped.
	pub(crate) fn as_solver_arg<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
	) -> view::IntView {
		map.get_int(slv, *self)
	}

	/// Get a Boolean view that represent whether the integer view is equal to the
	/// given value.
	pub fn eq(&self, v: IntVal) -> BoolView {
		match self {
			&Self::Var(x) => BoolView::IntEq(x, v),
			&Self::Const(c) => BoolView::Const(c == v),
			&Self::Linear(t, x) => match t.rev_transform_lit(LitMeaning::Eq(v)) {
				Ok(LitMeaning::Eq(val)) => BoolView::IntEq(x, val),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(!b);
					BoolView::Const(false)
				}
				_ => unreachable!(),
			},
			&Self::Bool(t, x) => match t.rev_transform_lit(LitMeaning::Eq(v)) {
				Ok(LitMeaning::Eq(1))  => x,
				Ok(LitMeaning::Eq(0))  => !x,
				Ok(LitMeaning::Eq(_)) /* if val != 0 */ => BoolView::Const(false),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is greater than
	/// the given value.
	pub fn gt(&self, v: IntVal) -> BoolView {
		self.geq(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is greater than
	/// or equal to the given value.
	pub fn geq(&self, v: IntVal) -> BoolView {
		match self {
			&Self::Var(x) => BoolView::IntGreaterEq(x, v),
			&Self::Const(c) => BoolView::Const(c >= v),
			&Self::Linear(t, x) => match t.rev_transform_lit(LitMeaning::GreaterEq(v)) {
				Ok(LitMeaning::GreaterEq(val)) => BoolView::IntGreaterEq(x, val),
				Ok(LitMeaning::Less(val)) => BoolView::IntLess(x, val),
				_ => unreachable!(),
			},
			&Self::Bool(t, x) => match t.rev_transform_lit(LitMeaning::GreaterEq(v)) {
				Ok(LitMeaning::GreaterEq(1)) => x,
				Ok(LitMeaning::GreaterEq(val)) if val > 1 => BoolView::Const(true),
				Ok(LitMeaning::GreaterEq(_)) /* if val <= 0 */ => BoolView::Const(false),
				Ok(LitMeaning::Less(1)) => !x,
				Ok(LitMeaning::Less(val)) if val > 1 => BoolView::Const(false),
				Ok(LitMeaning::Less(_)) /* if val <= 0 */ => BoolView::Const(true),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is less than
	/// the given value.
	pub fn lt(&self, v: IntVal) -> BoolView {
		match self {
			&Self::Var(x) => BoolView::IntLess(x, v),
			&Self::Const(c) => BoolView::Const(c <= v),
			&Self::Linear(t, x) => match t.rev_transform_lit(LitMeaning::Less(v)) {
				Ok(LitMeaning::GreaterEq(val)) => BoolView::IntGreaterEq(x, val),
				Ok(LitMeaning::Less(val)) => BoolView::IntLess(x, val),
				_ => unreachable!(),
			},
			&Self::Bool(t, x) => match t.rev_transform_lit(LitMeaning::Less(v)) {
				Ok(LitMeaning::GreaterEq(1)) => x,
				Ok(LitMeaning::GreaterEq(val)) if val > 1 => BoolView::Const(false),
				Ok(LitMeaning::GreaterEq(_)) /* if val <= 0 */ => BoolView::Const(true),
				Ok(LitMeaning::Less(1)) => !x,
				Ok(LitMeaning::Less(val)) if val > 1 => BoolView::Const(true),
				Ok(LitMeaning::Less(_)) /* if val <= 0 */ => BoolView::Const(false),
				_ => unreachable!(),
			},
		}
	}

	/// Get a Boolean view that represent whether the integer view is less than or
	/// equal to the given value.
	pub fn leq(&self, v: IntVal) -> BoolView {
		self.lt(v + 1)
	}

	/// Get a Boolean view that represent whether the integer view is not equal to
	/// the given value.
	pub fn ne(&self, v: IntVal) -> BoolView {
		match self {
			&Self::Var(x) => BoolView::IntNotEq(x, v),
			&Self::Const(c) => BoolView::Const(c != v),
			&Self::Linear(t, x) => match t.rev_transform_lit(LitMeaning::NotEq(v)) {
				Ok(LitMeaning::NotEq(val)) => BoolView::IntNotEq(x, val),
				Err(b) => {
					// After the transformation, the value `v` does not remain an integer.
					debug_assert!(b);
					BoolView::Const(true)
				}
				_ => unreachable!(),
			},
			&Self::Bool(t, x) => match t.rev_transform_lit(LitMeaning::NotEq(v)) {
				Ok(LitMeaning::NotEq(1))  => !x,
				Ok(LitMeaning::NotEq(0))  => x,
				Ok(LitMeaning::NotEq(_)) /* if val != 0 */ => BoolView::Const(true),
				_ => unreachable!(),
			},
		}
	}
}

impl Add<IntExpr> for IntExpr {
	type Output = IntLinExpr;

	fn add(self, rhs: IntExpr) -> Self::Output {
		IntLinExpr {
			terms: vec![self, rhs],
		}
	}
}

impl Add<IntVal> for IntExpr {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			return self;
		}
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::offset(rhs), x),
			Self::Const(v) => Self::Const(v + rhs),
			Self::Linear(t, x) => {
				let t = t + rhs;
				if t.is_identity() {
					Self::Var(x)
				} else {
					Self::Linear(t, x)
				}
			}
			Self::Bool(t, x) => Self::Bool(t + rhs, x),
		}
	}
}

impl From<BoolView> for IntExpr {
	fn from(value: BoolView) -> Self {
		match value {
			BoolView::Const(b) => Self::Const(b as IntVal),
			x => Self::Bool(LinearTransform::offset(0), x),
		}
	}
}

impl From<IntVar> for IntExpr {
	fn from(value: IntVar) -> Self {
		Self::Var(value)
	}
}

impl Mul<IntVal> for IntExpr {
	type Output = Self;

	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			Self::Const(0)
		} else {
			self.mul(NonZeroIntVal::new(rhs).unwrap())
		}
	}
}

impl Mul<NonZeroIntVal> for IntExpr {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::scaled(rhs), x),
			Self::Const(v) => Self::Const(v * rhs.get()),
			Self::Linear(t, x) => Self::Linear(t * rhs, x),
			Self::Bool(t, x) => Self::Bool(t * rhs, x),
		}
	}
}

impl Neg for IntExpr {
	type Output = Self;

	fn neg(self) -> Self::Output {
		match self {
			Self::Var(x) => {
				Self::Linear(LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()), x)
			}
			Self::Const(v) => Self::Const(-v),
			Self::Linear(t, x) => Self::Linear(-t, x),
			Self::Bool(t, x) => Self::Bool(-t, x),
		}
	}
}

impl Sub<IntExpr> for IntExpr {
	type Output = IntLinExpr;

	fn sub(self, rhs: IntExpr) -> Self::Output {
		self + -rhs
	}
}

impl Sub<IntVal> for IntExpr {
	type Output = Self;

	fn sub(self, rhs: IntVal) -> Self::Output {
		self + -rhs
	}
}
