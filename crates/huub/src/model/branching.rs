//! Definitions of branching strategies that can be included in a [`Model`].

use pindakaas::solver::propagation::PropagatingSolver;

use crate::{
	branchers::{BoolBrancher, IntBrancher, WarmStartBrancher},
	model::{bool::BoolView, int::IntExpr, reformulate::VariableMap},
	solver::engine::Engine,
	Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Strategy for making a search decision in a [`Model`].
pub enum Branching {
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// Boolean decision variable, and then set its value by using the
	/// [`ValueSelection`].
	Bool(Vec<BoolView>, VariableSelection, ValueSelection),
	/// Make a search decision by using the [`VariableSelection`] to select a
	/// integer decision variable, and then limit the domain of the variable by
	/// using the [`ValueSelection`].
	Int(Vec<IntExpr>, VariableSelection, ValueSelection),
	/// Search by sequentially applying the given branching strategies.
	Seq(Vec<Branching>),
	/// Search by enforcing the given Boolean expressions, but abandon the search
	/// when finding a conflict.
	WarmStart(Vec<BoolView>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Strategy for limiting the domain of a selected decision variable as part of
/// a search decision.
pub enum ValueSelection {
	/// Set the decision variable to its current lower bound value.
	IndomainMax,
	/// Set the decision variable to its current upper bound value.
	IndomainMin,
	/// Exclude the current upper bound value from the domain of the decision
	/// variable.
	OutdomainMax,
	/// Exclude the current lower bound value from the domain of the decision
	/// variable.
	OutdomainMin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Strategy of selecting the next decision variable from a list to make a
/// search decision.
pub enum VariableSelection {
	/// Select the unfixed decision variable with the largest remaining domain
	/// size, using the order of the variables in case of a tie.
	AntiFirstFail,
	/// Select the unfixed decision variable with the smallest remaining domain
	/// size, using the order of the variables in case of a tie.
	FirstFail,
	/// Select the first unfixed decision variable in the list.
	InputOrder,
	/// Select the unfixed decision variable with the largest upper bound, using
	/// the order of the variables in case of a tie.
	Largest,
	/// Select the unfixed decision variable with the smallest lower bound, using
	/// the order of the variables in case of a tie.
	Smallest,
}

impl Branching {
	/// Add a [`Brancher`] implementation to the solver that matches the branching
	/// strategy of the [`Branching`].
	pub(crate) fn to_solver<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
	) {
		match self {
			Branching::Bool(vars, var_sel, val_sel) => {
				let vars = vars.iter().map(|v| map.get_bool(slv, *v)).collect();
				BoolBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Int(v, var_sel, val_sel) => {
				let vars: Vec<_> = v.iter().map(|v| v.as_solver_arg(slv, map)).collect();
				IntBrancher::new_in(slv, vars, *var_sel, *val_sel);
			}
			Branching::Seq(branchings) => {
				for b in branchings {
					b.to_solver(slv, map);
				}
			}
			Branching::WarmStart(exprs) => {
				let decisions = exprs.iter().map(|v| map.get_bool(slv, *v)).collect();
				WarmStartBrancher::new_in(slv, decisions);
			}
		}
	}
}
