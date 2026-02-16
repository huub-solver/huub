//! Definitions of solutions that are found by [`Solver`] and (helper) methods
//! to extract values from them.

use std::fmt::{self, Debug, Display, Formatter};

use pindakaas::Valuation;

use crate::{
	IntVal,
	actions::IntInspectionActions,
	solver::{
		Decision, View,
		engine::State,
		view::{boolean::BoolView, integer::IntView},
	},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A general representation for any default view in the solver.
///
/// This representation is used only when list with different types of decision
/// variable views have to be created. In general users should prefer using
/// [`View`] instead.
pub enum AnyView {
	/// A Boolean type value.
	Bool(View<bool>),
	/// An integer type value.
	Int(View<IntVal>),
}

/// Trait for extracting a Boolean value from a solution.
pub trait BoolValuation {
	/// Return the Boolean value for this view in the given solution.
	fn val(&self, sol: Solution<'_>) -> bool;
}

/// Trait for extracting an integer value from a solution.
pub trait IntValuation {
	/// Return the integer value for this view in the given solution.
	fn val(&self, sol: Solution<'_>) -> IntVal;
}

#[derive(Clone, Copy)]
/// Reference to a solution state of the [`Solver`](crate::solver::Solver).
///
/// Solution allows the user to query the values that decision variable have
/// been assigned in the solution.
pub struct Solution<'a> {
	/// SAT valuation used to retrieve Boolean assignments.
	pub(crate) sat: &'a dyn Valuation,
	/// Solver state used to resolve integer values and views.
	pub(crate) state: &'a State,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(
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

impl AnyView {
	/// Return the value of this view in the given solution.
	pub fn val(&self, sol: Solution<'_>) -> Value {
		match self {
			AnyView::Bool(view) => Value::Bool(BoolValuation::val(view, sol)),
			AnyView::Int(view) => Value::Int(IntValuation::val(view, sol)),
		}
	}
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

impl BoolValuation for Decision<bool> {
	fn val(&self, sol: Solution<'_>) -> bool {
		sol.sat.value(self.0)
	}
}

impl IntValuation for Decision<IntVal> {
	fn val(&self, sol: Solution<'_>) -> IntVal {
		debug_assert_eq!(
			IntInspectionActions::min(self, sol.state),
			IntInspectionActions::max(self, sol.state)
		);
		IntInspectionActions::min(self, sol.state)
	}
}

impl Debug for Solution<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let sat_str: *const dyn Valuation = self.sat;
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

impl BoolValuation for View<bool> {
	fn val(&self, sol: Solution<'_>) -> bool {
		match self.0 {
			BoolView::Lit(decision) => BoolValuation::val(&decision, sol),
			BoolView::Const(b) => b,
		}
	}
}

impl IntValuation for View<IntVal> {
	fn val(&self, sol: Solution<'_>) -> IntVal {
		match self.0 {
			IntView::Const(c) => c,
			IntView::Linear(v) => IntValuation::val(&v, sol),
			IntView::Bool(v) => IntValuation::val(&v, sol),
		}
	}
}
