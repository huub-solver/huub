use std::fmt::Debug;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{decision::DecisionActions, initialization::InitializationActions},
	model::branching::{ValueSelection, VariableSelection},
	propagator::int_event::IntEvent,
	solver::{
		engine::{solving_context::SolvingContext, trail::TrailedInt},
		poster::{BoxedBrancher, BrancherPoster},
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, LitMeaning,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoolBrancherPoster {
	vars: Vec<BoolView>,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
}

pub(crate) trait Brancher<D: DecisionActions>: DynBranchClone + Debug {
	fn decide(&mut self, actions: &mut D) -> Decision;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoolBrancher {
	vars: Vec<RawLit>,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
	next: TrailedInt,
}

pub(crate) enum Decision {
	/// Make the decision to branch on the given literal
	Select(RawLit),
	/// The brancher has exhausted all possible decisions, but can be backtracked to a previous state
	Exhausted,
	/// The brancher has exhausted all possible decisions and cannot be backtracked to a previous state
	Consumed,
}

pub(crate) trait DynBranchClone {
	fn clone_dyn_branch(&self) -> BoxedBrancher;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntBrancher {
	vars: Vec<IntView>,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
	next: TrailedInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct IntBrancherPoster {
	vars: Vec<IntView>,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
}

impl<B: for<'a> Brancher<SolvingContext<'a>> + Clone + 'static> DynBranchClone for B {
	fn clone_dyn_branch(&self) -> BoxedBrancher {
		Box::new(self.clone())
	}
}

impl BoolBrancher {
	pub(crate) fn prepare(
		vars: Vec<BoolView>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) -> impl BrancherPoster {
		BoolBrancherPoster {
			vars,
			var_sel,
			val_sel,
		}
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

impl BrancherPoster for BoolBrancherPoster {
	fn post<I: InitializationActions>(self, actions: &mut I) -> BoxedBrancher {
		let vars: Vec<_> = self
			.vars
			.into_iter()
			.filter_map(|b| match b.0 {
				BoolViewInner::Lit(l) => {
					actions.subscribe_bool(BoolView(BoolViewInner::Lit(l)), 0);
					Some(l)
				}
				BoolViewInner::Const(_) => None,
			})
			.collect();
		Box::new(BoolBrancher {
			vars,
			var_sel: self.var_sel,
			val_sel: self.val_sel,
			next: actions.new_trailed_int(0),
		})
	}
}

impl Clone for BoxedBrancher {
	fn clone(&self) -> BoxedBrancher {
		self.clone_dyn_branch()
	}
}

impl IntBrancher {
	pub(crate) fn prepare(
		vars: Vec<IntView>,
		var_sel: VariableSelection,
		val_sel: ValueSelection,
	) -> impl BrancherPoster {
		IntBrancherPoster {
			vars,
			var_sel,
			val_sel,
		}
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
				LitMeaning::Less(actions.get_int_lower_bound(next_var) + 1),
			),
			ValueSelection::IndomainMax => actions.get_int_lit(
				next_var,
				LitMeaning::GreaterEq(actions.get_int_upper_bound(next_var)),
			),
			ValueSelection::OutdomainMin => actions.get_int_lit(
				next_var,
				LitMeaning::GreaterEq(actions.get_int_lower_bound(next_var) + 1),
			),
			ValueSelection::OutdomainMax => actions.get_int_lit(
				next_var,
				LitMeaning::Less(actions.get_int_upper_bound(next_var)),
			),
		};

		match view.0 {
			BoolViewInner::Lit(lit) => Decision::Select(lit),
			_ => unreachable!(),
		}
	}
}

impl BrancherPoster for IntBrancherPoster {
	fn post<I: InitializationActions>(self, actions: &mut I) -> BoxedBrancher {
		let vars: Vec<_> = self
			.vars
			.into_iter()
			.filter(|i| !matches!(i.0, IntViewInner::Const(_)))
			.collect();

		for v in &vars {
			actions.subscribe_int(*v, IntEvent::Domain, 0);
		}

		Box::new(IntBrancher {
			vars,
			var_sel: self.var_sel,
			val_sel: self.val_sel,
			next: actions.new_trailed_int(0),
		})
	}
}
