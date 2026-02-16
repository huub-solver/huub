//! Module containing methods for making search decisions in the solver.

use std::fmt::Debug;

use dyn_clone::DynClone;

use crate::{
	IntVal,
	actions::{
		BoolInspectionActions, BrancherInitActions, DecisionActions, IntDecisionActions,
		IntInspectionActions, ReasoningContext, Trailed,
	},
	solver::{
		Decision, IntLitMeaning,
		solving_context::SolvingContext,
		view::{View, boolean::BoolView, integer::IntView},
	},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// General brancher for Boolean variables that makes search decision by
/// following a given [`VariableSelection`] and [`ValueSelection`] strategy.
pub struct BoolBrancher {
	/// Boolean variables to be branched on.
	vars: Vec<Decision<bool>>,
	/// [`VariableSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: VariableSelection,
	/// [`ValueSelection`] strategy used to select the way in which to branch on
	/// the selected decision variable.
	val_sel: ValueSelection,
	/// The start of the unfixed variables in `vars`.
	next: Trailed<usize>,
}

/// Type alias to represent [`Brancher`] contained in a [`Box`], that is used by
/// [`Engine`].
pub(crate) type BoxedBrancher = Box<dyn for<'a> Brancher<SolvingContext<'a>>>;

/// A trait for making search decisions in the solver
pub trait Brancher<D: DecisionActions>: Debug + DynClone {
	/// Make a next search decision using the given decision actions.
	fn decide(&mut self, actions: &mut D) -> Directive;
}

/// An search decision made by a [`Brancher`].
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Directive {
	/// Make the decision to branch on the given literal.
	Select(View<bool>),
	/// The brancher has exhausted all possible decisions, but can be
	/// backtracked to a previous state.
	Exhausted,
	/// The brancher has exhausted all possible decisions and cannot be
	/// backtracked to a previous state.
	Consumed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// General brancher for integer variables that makes search decision by
/// following a given [`VariableSelection`] and [`ValueSelection`] strategy.
pub struct IntBrancher {
	/// Integer variables to be branched on.
	vars: Vec<View<IntVal>>,
	/// [`VariableSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: VariableSelection,
	/// [`ValueSelection`] strategy used to select the way in which to branch on
	/// the selected decision variable.
	val_sel: ValueSelection,
	/// The start of the unfixed variables in `vars`.
	next: Trailed<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Strategy for limiting the domain of a selected decision variable for a
/// [`BoolBrancher`] or [`IntBrancher`] .
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
/// Strategy of selecting the next decision variable for a [`BoolBrancher`] or
/// [`IntBrancher`] .
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
	/// Select the unfixed decision variable with the smallest lower bound,
	/// using the order of the variables in case of a tie.
	Smallest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// A brancher that enforces Boolean conditions that is abandoned when a
/// conflict is encountered. These branchers are generally used to warm start,
/// i.e. quickly reach, a (partial) known or expected solution.
pub struct WarmStartBrancher {
	/// Boolean conditions to be tried.
	decisions: Vec<Decision<bool>>,
	/// Number of conflicts at the time of posting the brancher.
	conflicts: u64,
}

impl BoolBrancher {
	/// Create a new [`BoolBrancher`] brancher and add to the end of the
	/// branching queue in the solver.
	pub fn new_in(
		solver: &mut impl BrancherInitActions,
		vars: Vec<View<bool>>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) {
		let vars: Vec<_> = vars
			.into_iter()
			.filter_map(|b| match b.0 {
				BoolView::Lit(l) => {
					solver.ensure_decidable::<bool>(b);
					Some(l)
				}
				BoolView::Const(_) => None,
			})
			.collect();

		let next = solver.new_trailed(0);
		solver.push_brancher(Box::new(BoolBrancher {
			vars,
			var_sel,
			val_sel,
			next,
		}));
	}
}

impl<E> Brancher<E> for BoolBrancher
where
	E: DecisionActions,
	Decision<bool>: BoolInspectionActions<E>,
{
	fn decide(&mut self, ctx: &mut E) -> Directive {
		let begin = ctx.trailed(self.next);

		// return if all variables have been assigned
		if begin == self.vars.len() {
			return Directive::Exhausted;
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
			if var.val(ctx).is_none() {
				loc = Some(i);
				break;
			}
		}
		let var = if let Some(first_unfixed) = loc {
			// Update position for next iteration
			ctx.set_trailed(self.next, first_unfixed);
			self.vars[first_unfixed]
		} else {
			// Return that everything has already been assigned
			return Directive::Exhausted;
		};

		// select the next value to branch on based on the value selection strategy
		Directive::Select(
			match self.val_sel {
				ValueSelection::IndomainMin | ValueSelection::OutdomainMax => !var,
				ValueSelection::IndomainMax | ValueSelection::OutdomainMin => var,
			}
			.into(),
		)
	}
}

impl Clone for BoxedBrancher {
	fn clone(&self) -> BoxedBrancher {
		dyn_clone::clone_box(&**self)
	}
}

impl IntBrancher {
	/// Create a new [`IntBrancher`] brancher and add to the end of the
	/// branching queue in the solver.
	pub fn new_in(
		solver: &mut impl BrancherInitActions,
		vars: Vec<View<IntVal>>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) {
		let vars: Vec<_> = vars
			.into_iter()
			.filter(|i| !matches!(i.0, IntView::Const(_)))
			.collect();

		for &v in &vars {
			solver.ensure_decidable(v);
		}

		let next = solver.new_trailed(0);
		solver.push_brancher(Box::new(IntBrancher {
			vars,
			var_sel,
			val_sel,
			next,
		}));
	}
}

impl<D> Brancher<D> for IntBrancher
where
	D: DecisionActions + ReasoningContext<Atom = View<bool>>,
	View<IntVal>: IntDecisionActions<D>,
{
	fn decide(&mut self, actions: &mut D) -> Directive {
		let begin = actions.trailed(self.next);

		// return if all variables have been assigned
		if begin == self.vars.len() {
			return Directive::Exhausted;
		}

		let score = |var: View<IntVal>| match self.var_sel {
			VariableSelection::AntiFirstFail | VariableSelection::FirstFail => {
				let (lb, ub) = var.bounds(actions);
				ub - lb
			}
			VariableSelection::InputOrder => 0,
			VariableSelection::Largest => var.max(actions),
			VariableSelection::Smallest => var.min(actions),
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
			if self.vars[i].min(actions) == self.vars[i].max(actions) {
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

		// return if all variables have been assigned
		let Some((next_var, _)) = selection else {
			return Directive::Exhausted;
		};

		// update the next variable to the index of the first unfixed variable
		actions.set_trailed(self.next, first_unfixed);

		// select the next value to branch on based on the value selection strategy
		let view = next_var.lit(
			actions,
			match self.val_sel {
				ValueSelection::IndomainMin => IntLitMeaning::Less(next_var.min(actions) + 1),
				ValueSelection::IndomainMax => IntLitMeaning::GreaterEq(next_var.max(actions)),
				ValueSelection::OutdomainMin => IntLitMeaning::GreaterEq(next_var.min(actions) + 1),
				ValueSelection::OutdomainMax => IntLitMeaning::Less(next_var.max(actions)),
			},
		);
		Directive::Select(view)
	}
}

impl WarmStartBrancher {
	/// Create a new [`BoolBrancher`] brancher and add to the end of the
	/// branching queue in the solver.
	pub fn new_in(solver: &mut impl BrancherInitActions, decisions: Vec<View<bool>>) {
		// Filter out the decisions that are already satisfied or are known to cause
		// a conflict
		let mut filtered_decision = Vec::new();
		for d in decisions {
			match d.0 {
				BoolView::Lit(l) => {
					solver.ensure_decidable::<bool>(d);
					filtered_decision.push(l);
				}
				// Warm starts decision conflict here, we don't have to add this or any
				// other decisions to the brancher
				BoolView::Const(false) => break,
				// Warm starts decision is already satisfied, we don't have to add this
				BoolView::Const(true) => {}
			}
		}

		if !filtered_decision.is_empty() {
			filtered_decision.reverse();
			solver.push_brancher(Box::new(WarmStartBrancher {
				decisions: filtered_decision,
				conflicts: solver.num_conflicts(),
			}));
		}
	}
}

impl<Context> Brancher<Context> for WarmStartBrancher
where
	Context: DecisionActions,
	Decision<bool>: BoolInspectionActions<Context>,
{
	fn decide(&mut self, ctx: &mut Context) -> Directive {
		if ctx.num_conflicts() > self.conflicts {
			return Directive::Consumed;
		}
		while let Some(lit) = self.decisions.pop() {
			match lit.val(ctx) {
				Some(true) => {}
				Some(false) => return Directive::Consumed,
				None => return Directive::Select(lit.into()),
			}
		}
		Directive::Consumed
	}
}
