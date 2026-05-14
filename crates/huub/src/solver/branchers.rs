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

/// General brancher for Boolean decision variables that makes search decisions
/// by following a given [`DecisionSelection`] and [`DomainSelection`] strategy.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BoolBrancher {
	/// Boolean decision variables to be branched on.
	vars: Vec<Decision<bool>>,
	/// [`DecisionSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: DecisionSelection,
	/// [`DomainSelection`] strategy used to select the way in which to branch
	/// on the selected decision variable.
	val_sel: DomainSelection,
	/// The start of the unfixed variables in `vars`.
	next: Trailed<usize>,
}

/// Type alias to represent [`Brancher`] contained in a [`Box`], that is used by
/// [`Engine`].
pub(crate) type BoxedBrancher = Box<dyn for<'a> Brancher<SolvingContext<'a>>>;

/// A trait for making search decisions in the solver.
pub trait Brancher<D: DecisionActions>: Debug + DynClone {
	/// Make a next search decision using the given decision actions.
	fn decide(&mut self, actions: &mut D) -> Directive;
}

/// A search decision made by a [`Brancher`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

/// General brancher for integer variables that makes search decisions by
/// following a given [`DecisionSelection`] and [`DomainSelection`] strategy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntBrancher {
	/// Integer variables to be branched on.
	vars: Vec<View<IntVal>>,
	/// [`DecisionSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: DecisionSelection,
	/// [`DomainSelection`] strategy used to select the way in which to branch
	/// on the selected decision variable.
	val_sel: DomainSelection,
	/// The start of the unfixed variables in `vars`.
	next: Trailed<usize>,
}

/// Strategy for limiting the domain of a selected decision variable for a
/// [`BoolBrancher`] or [`IntBrancher`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum DomainSelection {
	/// Set the decision variable to its current maximum value.
	IndomainMax,
	/// Set the decision variable to its current minimum value.
	IndomainMin,
	/// Exclude the current upper bound value from the domain of the decision
	/// variable.
	OutdomainMax,
	/// Exclude the current lower bound value from the domain of the decision
	/// variable.
	OutdomainMin,
}

/// Strategy of selecting the next decision variable for a [`BoolBrancher`] or
/// [`IntBrancher`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum DecisionSelection {
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

/// A brancher that enforces Boolean conditions and is abandoned when a
/// conflict is encountered. These branchers are generally used to warm start,
/// i.e. quickly reach, a (partial) known or expected solution.
#[derive(Clone, Debug, Eq, PartialEq)]
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
		var_sel: DecisionSelection,
		val_sel: DomainSelection,
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

		// Return if all variables have been assigned.
		if begin == self.vars.len() {
			return Directive::Exhausted;
		}

		// Boolean variable selection currently selects the first unfixed variable.
		debug_assert!(matches!(
			self.var_sel,
			DecisionSelection::InputOrder
				| DecisionSelection::Smallest
				| DecisionSelection::Largest
				| DecisionSelection::FirstFail
				| DecisionSelection::AntiFirstFail
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
				DomainSelection::IndomainMin | DomainSelection::OutdomainMax => !var,
				DomainSelection::IndomainMax | DomainSelection::OutdomainMin => var,
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
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{
	/// # 		Solver, Status, Valuation,
	/// # 		branchers::{IntBrancher, DomainSelection, DecisionSelection},
	/// # 	},
	/// # };
	/// # let mut model = Model::default();
	/// # let x = model.new_int_decision(1..=3);
	/// # let y = model.new_int_decision(1..=3);
	/// # model.linear(x + y).eq(4).post();
	/// # let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// # let x = map.get(&mut solver, x);
	/// # let y = map.get(&mut solver, y);
	/// IntBrancher::new_in(
	/// 	&mut solver,
	/// 	vec![x, y],
	/// 	DecisionSelection::FirstFail,
	/// 	DomainSelection::IndomainMin,
	/// );
	///
	/// # let status = solver
	/// # 	.solve()
	/// # 	.on_solution(|solution| {
	/// # 		assert_eq!(x.val(solution) + y.val(solution), 4);
	/// # 	})
	/// # 	.satisfy();
	/// # assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn new_in(
		solver: &mut impl BrancherInitActions,
		vars: Vec<View<IntVal>>,
		var_sel: DecisionSelection,
		val_sel: DomainSelection,
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
			DecisionSelection::AntiFirstFail | DecisionSelection::FirstFail => {
				let (lb, ub) = var.bounds(actions);
				ub - lb
			}
			DecisionSelection::InputOrder => 0,
			DecisionSelection::Largest => var.max(actions),
			DecisionSelection::Smallest => var.min(actions),
		};

		let is_better = |incumbent_score, new_score| match self.var_sel {
			DecisionSelection::AntiFirstFail | DecisionSelection::Largest => {
				incumbent_score < new_score
			}
			DecisionSelection::FirstFail | DecisionSelection::Smallest => {
				incumbent_score > new_score
			}
			DecisionSelection::InputOrder => unreachable!(),
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
				if self.var_sel == DecisionSelection::InputOrder {
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
				DomainSelection::IndomainMin => IntLitMeaning::Less(next_var.min(actions) + 1),
				DomainSelection::IndomainMax => IntLitMeaning::GreaterEq(next_var.max(actions)),
				DomainSelection::OutdomainMin => {
					IntLitMeaning::GreaterEq(next_var.min(actions) + 1)
				}
				DomainSelection::OutdomainMax => IntLitMeaning::Less(next_var.max(actions)),
			},
		);
		Directive::Select(view)
	}
}

impl WarmStartBrancher {
	/// Create a new [`WarmStartBrancher`] brancher and add to the end of the
	/// branching queue in the solver.
	///
	/// A warm start is a preference, not a constraint. If the suggested
	/// decisions cause a conflict, the brancher is consumed and regular search
	/// continues.
	///
	/// ```
	/// # use huub::{
	/// # 	actions::IntDecisionActions,
	/// # 	model::Model,
	/// # 	solver::{IntLitMeaning, Solver, Status, Valuation, branchers::WarmStartBrancher},
	/// # };
	/// # let mut model = Model::default();
	/// # let x = model.new_int_decision(1..=3);
	/// # let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// # let x = map.get(&mut solver, x);
	/// let prefer_two = x.lit(&mut solver, IntLitMeaning::Eq(2));
	/// WarmStartBrancher::new_in(&mut solver, vec![prefer_two]);
	///
	/// # let mut value = None;
	/// # let status = solver
	/// # 	.solve()
	/// # 	.on_solution(|solution| {
	/// # 		value = Some(x.val(solution));
	/// # 	})
	/// # 	.satisfy();
	/// # assert_eq!(status, Status::Satisfied);
	/// # assert_eq!(value, Some(2));
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
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
