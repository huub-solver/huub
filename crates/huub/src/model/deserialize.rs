//! Model (and solver) construction from external formats.

#[cfg(feature = "flatzinc")]
pub mod flatzinc;

use pindakaas::solver::propagation::ExternalPropagation;

use crate::{
	IntVal,
	lower::LoweringMap,
	model::View,
	solver::{
		Solver,
		branchers::{
			BoolBrancher, IntBrancher, ValueSelection, VariableSelection, WarmStartBrancher,
		},
	},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Reference to a decision in a [`Model`](crate::model::Model).
pub enum AnyView {
	/// Reference to a Boolean decision.
	Bool(View<bool>),
	/// Reference to an integer decision.
	Int(View<IntVal>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Specification of a search strategy that can lowered into
/// [`Brancher`](crate::solver::branchers::Brancher) implementations added to a
/// [`Solver`] instance.
///
/// Note that a [`Branching`] might be ignored (or used as only a suggestion) in
/// [`Solver`] depending on the configuration.
pub enum Branching {
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// Boolean decision variable, and then set its value by using the
	/// [`ValueSelection`].
	Bool(Vec<View<bool>>, VariableSelection, ValueSelection),
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// integer decision variable, and then limit the domain of the variable by
	/// using the [`ValueSelection`].
	Int(Vec<View<IntVal>>, VariableSelection, ValueSelection),
	/// Search by sequentially applying the given branching strategies.
	Seq(Vec<Branching>),
	/// Search by enforcing the given Boolean expressions, but abandon the
	/// search when finding a conflict.
	WarmStart(Vec<View<bool>>),
}

impl From<View<IntVal>> for AnyView {
	fn from(value: View<IntVal>) -> Self {
		Self::Int(value)
	}
}

impl From<View<bool>> for AnyView {
	fn from(value: View<bool>) -> Self {
		Self::Bool(value)
	}
}

impl Branching {
	/// Add a [`Brancher`](crate::solver::branchers::Brancher) implementation to
	/// the solver that matches the branching strategy of the [`Branching`].
	pub fn to_solver<Sat: ExternalPropagation>(&self, slv: &mut Solver<Sat>, map: &LoweringMap) {
		match self {
			Branching::Bool(vars, var_sel, val_sel) => {
				let vars = vars.iter().map(|v| map.get(slv, *v)).collect();
				BoolBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Int(v, var_sel, val_sel) => {
				let vars: Vec<_> = v.iter().map(|v| map.get(slv, *v)).collect();
				IntBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Seq(branchings) => {
				for b in branchings {
					b.to_solver(slv, map);
				}
			}
			Branching::WarmStart(exprs) => {
				let decisions = exprs.iter().map(|v| map.get(slv, *v)).collect();
				WarmStartBrancher::new_in(slv, decisions);
			}
		}
	}
}
