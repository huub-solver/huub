//! Definitions of solutions that are found by [`Solver`] and (helper) methods
//! to extract values from them.

use std::fmt::{self, Debug, Display, Formatter};

use pindakaas::Valuation as RawValuation;

use crate::{
	IntVal,
	actions::IntInspectionActions,
	solver::{
		Decision, View,
		engine::State,
		view::{boolean::BoolView, integer::IntView},
	},
};

/// A general representation for any default view in the solver.
///
/// This representation is used only when list with different types of decision
/// variable views have to be created. In general users should prefer using
/// [`View`] instead.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AnyView {
	/// A Boolean type value.
	Bool(View<bool>),
	/// An integer type value.
	Int(View<IntVal>),
}

/// Reference to a solution state of the [`Solver`](crate::solver::Solver).
///
/// Solution allows the user to query the values that decision variable have
/// been assigned in the solution.
#[derive(Clone, Copy)]
pub struct Solution<'a> {
	/// SAT valuation used to retrieve Boolean assignments.
	pub(crate) sat: &'a dyn RawValuation,
	/// Solver state used to resolve integer values and views.
	pub(crate) state: &'a State,
}

/// Trait for extracting a solution value from a [`Solution`] for a given
/// decision variable view.
pub trait Valuation {
	/// The type of value associated with this view in a solution.
	type Val;

	/// Return the value for this view in the given solution.
	fn val(&self, sol: Solution<'_>) -> Self::Val;
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[expect(
	variant_size_differences,
	reason = "`Int` cannot be as small as `Bool`"
)]
/// The general representation for any solution value in the solver.
pub enum Value {
	/// A Boolean value.
	Bool(bool),
	/// An integer value.
	Int(IntVal),
}

impl From<IntVal> for AnyView {
	fn from(value: IntVal) -> Self {
		AnyView::Int(View::from(value))
	}
}

impl From<View<IntVal>> for AnyView {
	fn from(value: View<IntVal>) -> Self {
		AnyView::Int(value)
	}
}

impl From<View<bool>> for AnyView {
	fn from(value: View<bool>) -> Self {
		AnyView::Bool(value)
	}
}

impl Valuation for AnyView {
	type Val = Value;

	/// Return the value of this view in the given solution.
	fn val(&self, sol: Solution<'_>) -> Value {
		match self {
			AnyView::Bool(view) => Value::Bool(view.val(sol)),
			AnyView::Int(view) => Value::Int(Valuation::val(view, sol)),
		}
	}
}

impl Valuation for Decision<IntVal> {
	type Val = IntVal;

	fn val(&self, sol: Solution<'_>) -> IntVal {
		debug_assert_eq!(
			IntInspectionActions::min(self, sol.state),
			IntInspectionActions::max(self, sol.state)
		);
		IntInspectionActions::min(self, sol.state)
	}
}

impl Valuation for Decision<bool> {
	type Val = bool;

	fn val(&self, sol: Solution<'_>) -> bool {
		sol.sat.value(self.0)
	}
}

impl Debug for Solution<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let sat_str: *const dyn RawValuation = self.sat;
		f.debug_struct("Solution")
			.field("sat", &(sat_str as *const std::ffi::c_void))
			.field("state", &self.state)
			.finish()
	}
}

impl Display for Value {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match self {
			Value::Bool(b) => write!(f, "{}", b),
			Value::Int(i) => write!(f, "{}", i),
		}
	}
}

impl From<IntVal> for Value {
	fn from(value: IntVal) -> Self {
		Value::Int(value)
	}
}

impl From<bool> for Value {
	fn from(value: bool) -> Self {
		Value::Bool(value)
	}
}

impl Valuation for View<IntVal> {
	type Val = IntVal;

	fn val(&self, sol: Solution<'_>) -> IntVal {
		match self.0 {
			IntView::Const(c) => c,
			IntView::Linear(v) => Valuation::val(&v, sol),
			IntView::Bool(v) => Valuation::val(&v, sol),
		}
	}
}

impl Valuation for View<bool> {
	type Val = bool;

	fn val(&self, sol: Solution<'_>) -> bool {
		match self.0 {
			BoolView::Lit(decision) => decision.val(sol),
			BoolView::Const(b) => b,
		}
	}
}
