//! Module containing methods for making search decisions in the solver.

use std::fmt::Debug;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{BrancherInitActions, DecisionActions},
	solver::{
		solving_context::SolvingContext, trail::TrailedInt, BoolView, BoolViewInner, IntLitMeaning,
		IntView, IntViewInner, View,
	},
	ValueSelection, VariableSelection,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// General brancher for Boolean variables that makes search decision by
/// following a given [`VariableSelection`] and [`ValueSelection`] strategy.
pub struct BoolBrancher {
	/// Boolean variables to be branched on.
	vars: Vec<RawLit>,
	/// [`VariableSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: VariableSelection,
	/// [`ValueSelection`] strategy used to select the way in which to branch on
	/// the selected decision variable.
	val_sel: ValueSelection,
	/// The start of the unfixed variables in `vars`.
	next: TrailedInt,
}

/// Type alias to represent [`Brancher`] contained in a [`Box`], that is used by
/// [`Engine`].
pub(crate) type BoxedBrancher = Box<dyn for<'a> Brancher<SolvingContext<'a>>>;

/// A trait for making search decisions in the solver
pub trait Brancher<D: DecisionActions>: DynBrancherClone + Debug {
	/// Make a next search decision using the given decision actions.
	fn decide(&mut self, actions: &mut D) -> Decision;
}

/// An search decision made by a [`Brancher`].
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Decision {
	/// Make the decision to branch on the given literal.
	Select(RawLit),
	/// The brancher has exhausted all possible decisions, but can be backtracked
	/// to a previous state.
	Exhausted,
	/// The brancher has exhausted all possible decisions and cannot be
	/// backtracked to a previous state.
	Consumed,
}

/// A trait to allow the cloning of boxed branchers.
///
/// This trait allows us to implement [`Clone`] for [`BoxedBrancher`].
pub trait DynBrancherClone {
	/// Clone the object and store it as a boxed trait object.
	fn clone_dyn_brancher(&self) -> BoxedBrancher;
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// General brancher for integer variables that makes search decision by
/// following a given [`VariableSelection`] and [`ValueSelection`] strategy.
pub struct IntBrancher {
	/// Integer variables to be branched on.
	vars: Vec<IntView>,
	/// [`VariableSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: VariableSelection,
	/// [`ValueSelection`] strategy used to select the way in which to branch on
	/// the selected decision variable.
	val_sel: ValueSelection,
	/// The start of the unfixed variables in `vars`.
	next: TrailedInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// A brancher that enforces Boolean conditions that is abandoned when a
/// conflict is encountered. These branchers are generally used to warm start,
/// i.e. quickly reach, a (partial) known or expected solution.
pub struct WarmStartBrancher {
	/// Boolean conditions to be tried.
	decisions: Vec<RawLit>,
	/// Number of conflicts at the time of posting the brancher.
	conflicts: u64,
}

impl<B: for<'a> Brancher<SolvingContext<'a>> + Clone + 'static> DynBrancherClone for B {
	fn clone_dyn_brancher(&self) -> BoxedBrancher {
		Box::new(self.clone())
	}
}

impl BoolBrancher {
	/// Create a new [`BoolBrancher`] brancher and add to the end of the branching
	/// queue in the solver.
	pub fn new_in(
		solver: &mut impl BrancherInitActions,
		vars: Vec<BoolView>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) {
		let vars: Vec<_> = vars
			.into_iter()
			.filter_map(|b| match b.0 {
				BoolViewInner::Lit(l) => {
					solver.ensure_decidable(View::Bool(b));
					Some(l)
				}
				BoolViewInner::Const(_) => None,
			})
			.collect();

		let next = solver.new_trailed_int(0);
		solver.push_brancher(Box::new(BoolBrancher {
			vars,
			var_sel,
			val_sel,
			next,
		}));
	}
}

impl<D: DecisionActions> Brancher<D> for BoolBrancher {
	fn decide(&mut self, actions: &mut D) -> Decision {
		let begin = actions.get_trailed_int(self.next) as usize;

		// return if all variables have been assigned
		if begin == self.vars.len() {
			return Decision::Exhausted;
		}

		// Variable selection currently can just select first unfixed in the array
		debug_assert!(matches!(
			self.var_sel,
			VariableSelection::InputOrder
				| VariableSelection::Smallest
				| VariableSelection::Largest
				| VariableSelection::FirstFail
				| VariableSelection::AntiFirstFail
		));

		let mut loc = None;
		for (i, &var) in self.vars.iter().enumerate().skip(begin) {
			if actions
				.get_bool_val(BoolView(BoolViewInner::Lit(var)))
				.is_none()
			{
				loc = Some(i);
				break;
			}
		}
		let var = if let Some(i) = loc {
			// Update position for next iteration
			let _ = actions.set_trailed_int(self.next, (i + 1) as i64);
			self.vars[i]
		} else {
			// Return if everything has already been assigned
			let _ = actions.set_trailed_int(self.next, self.vars.len() as i64);
			return Decision::Exhausted;
		};

		// select the next value to branch on based on the value selection strategy
		Decision::Select(match self.val_sel {
			ValueSelection::IndomainMin | ValueSelection::OutdomainMax => !var,
			ValueSelection::IndomainMax | ValueSelection::OutdomainMin => var,
		})
	}
}

impl Clone for BoxedBrancher {
	fn clone(&self) -> BoxedBrancher {
		self.clone_dyn_brancher()
	}
}

impl IntBrancher {
	/// Create a new [`IntBrancher`] brancher and add to the end of the branching
	/// queue in the solver.
	pub fn new_in(
		solver: &mut impl BrancherInitActions,
		vars: Vec<IntView>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) {
		let vars: Vec<_> = vars
			.into_iter()
			.filter(|i| !matches!(i.0, IntViewInner::Const(_)))
			.collect();

		for &v in &vars {
			solver.ensure_decidable(v.into());
		}

		let next = solver.new_trailed_int(0);
		solver.push_brancher(Box::new(IntBrancher {
			vars,
			var_sel,
			val_sel,
			next,
		}));
	}
}

impl<D: DecisionActions> Brancher<D> for IntBrancher {
	fn decide(&mut self, actions: &mut D) -> Decision {
		let begin = actions.get_trailed_int(self.next) as usize;

		// return if all variables have been assigned
		if begin == self.vars.len() {
			return Decision::Exhausted;
		}

		let score = |var| match self.var_sel {
			VariableSelection::AntiFirstFail | VariableSelection::FirstFail => {
				let (lb, ub) = actions.get_int_bounds(var);
				ub - lb
			}
			VariableSelection::InputOrder => 0,
			VariableSelection::Largest => actions.get_int_upper_bound(var),
			VariableSelection::Smallest => actions.get_int_lower_bound(var),
		};

		let is_better = |incumbent_score, new_score| match self.var_sel {
			VariableSelection::AntiFirstFail | VariableSelection::Largest => {
				incumbent_score < new_score
			}
			VariableSelection::FirstFail | VariableSelection::Smallest => {
				incumbent_score > new_score
			}
			VariableSelection::InputOrder => unreachable!(),
		};

		let mut first_unfixed = begin;
		let mut selection = None;
		for i in begin..self.vars.len() {
			if actions.get_int_lower_bound(self.vars[i])
				== actions.get_int_upper_bound(self.vars[i])
			{
				// move the unfixed variable to the front
				let unfixed_var = self.vars[first_unfixed];
				let fixed_var = self.vars[i];
				self.vars[first_unfixed] = fixed_var;
				self.vars[i] = unfixed_var;
				first_unfixed += 1;
			} else if let Some((_, sel_score)) = selection {
				let new_score = score(self.vars[i]);
				if is_better(sel_score, new_score) {
					selection = Some((self.vars[i], new_score));
				}
			} else {
				selection = Some((self.vars[i], score(self.vars[i])));
				if self.var_sel == VariableSelection::InputOrder {
					break;
				}
			}
		}
		// update the next variable to the index of the first unfixed variable
		let _ = actions.set_trailed_int(self.next, first_unfixed as i64);

		// return if all variables have been assigned
		let Some((next_var, _)) = selection else {
			return Decision::Exhausted;
		};
		// select the next value to branch on based on the value selection strategy
		let view = match self.val_sel {
			ValueSelection::IndomainMin => actions.get_int_lit(
				next_var,
				IntLitMeaning::Less(actions.get_int_lower_bound(next_var) + 1),
			),
			ValueSelection::IndomainMax => actions.get_int_lit(
				next_var,
				IntLitMeaning::GreaterEq(actions.get_int_upper_bound(next_var)),
			),
			ValueSelection::OutdomainMin => actions.get_int_lit(
				next_var,
				IntLitMeaning::GreaterEq(actions.get_int_lower_bound(next_var) + 1),
			),
			ValueSelection::OutdomainMax => actions.get_int_lit(
				next_var,
				IntLitMeaning::Less(actions.get_int_upper_bound(next_var)),
			),
		};

		match view.0 {
			BoolViewInner::Lit(lit) => Decision::Select(lit),
			_ => unreachable!(),
		}
	}
}

impl WarmStartBrancher {
	/// Create a new [`BoolBrancher`] brancher and add to the end of the branching
	/// queue in the solver.
	pub fn new_in(solver: &mut impl BrancherInitActions, decisions: Vec<BoolView>) {
		// Filter out the decisions that are already satisfied or are known to cause
		// a conflict
		let mut filtered_decision = Vec::new();
		for d in decisions {
			match d.0 {
				BoolViewInner::Lit(l) => {
					solver.ensure_decidable(View::Bool(d));
					filtered_decision.push(l);
				}
				// Warm starts decision conflict here, we don't have to add this or any
				// other decisions to the brancher
				BoolViewInner::Const(false) => break,
				// Warm starts decision is already satisfied, we don't have to add this
				BoolViewInner::Const(true) => {}
			}
		}

		if !filtered_decision.is_empty() {
			filtered_decision.reverse();
			solver.push_brancher(Box::new(WarmStartBrancher {
				decisions: filtered_decision,
				conflicts: solver.get_num_conflicts(),
			}));
		}
	}
}

impl<D: DecisionActions> Brancher<D> for WarmStartBrancher {
	fn decide(&mut self, actions: &mut D) -> Decision {
		if actions.get_num_conflicts() > self.conflicts {
			return Decision::Consumed;
		}
		while let Some(lit) = self.decisions.pop() {
			match actions.get_bool_val(BoolView(BoolViewInner::Lit(lit))) {
				Some(true) => {}
				Some(false) => return Decision::Consumed,
				None => return Decision::Select(lit),
			}
		}
		Decision::Consumed
	}
}
