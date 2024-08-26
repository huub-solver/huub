use std::fmt::Debug;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{explanation::ExplanationActions, initialization::InitializationActions},
	model::branching::{ValueSelection, VariableSelection},
	solver::{
		engine::trail::TrailedInt,
		poster::BrancherPoster,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Brancher {
	vars: BrancherVars,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
	next: TrailedInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BrancherVars {
	Bool(Vec<RawLit>),
	Int(Vec<IntView>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct IntBrancherPoster {
	vars: Vec<IntView>,
	var_sel: VariableSelection,
	val_sel: ValueSelection,
}

fn decide_bool<E: ExplanationActions>(
	actions: &mut E,
	vars: &[RawLit],
	var_sel: VariableSelection,
	val_sel: ValueSelection,
	next: TrailedInt,
) -> Option<RawLit> {
	let begin = actions.get_trailed_int(next) as usize;

	// return if all variables have been assigned
	if begin == vars.len() {
		return None;
	}

	// Variable selection currently can just select first unfixed in the array
	debug_assert!(matches!(
		var_sel,
		VariableSelection::InputOrder
			| VariableSelection::Smallest
			| VariableSelection::Largest
			| VariableSelection::FirstFail
			| VariableSelection::AntiFirstFail
	));

	let mut loc = None;
	for (i, &var) in vars.iter().enumerate().skip(begin) {
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
		let _ = actions.set_trailed_int(next, (i + 1) as i64);
		vars[i]
	} else {
		// Return if everything has already been assigned
		let _ = actions.set_trailed_int(next, vars.len() as i64);
		return None;
	};

	// select the next value to branch on based on the value selection strategy
	Some(match val_sel {
		ValueSelection::IndomainMin | ValueSelection::OutdomainMax => !var,
		ValueSelection::IndomainMax | ValueSelection::OutdomainMin => var,
	})
}

fn decide_int<E: ExplanationActions>(
	actions: &mut E,
	vars: &mut [IntView],
	var_sel: VariableSelection,
	val_sel: ValueSelection,
	next: TrailedInt,
) -> Option<RawLit> {
	let begin = actions.get_trailed_int(next) as usize;

	// return if all variables have been assigned
	if begin == vars.len() {
		return None;
	}

	let score = |var| match var_sel {
		VariableSelection::AntiFirstFail | VariableSelection::FirstFail => {
			let (lb, ub) = actions.get_int_bounds(var);
			ub - lb
		}
		VariableSelection::InputOrder => 0,
		VariableSelection::Largest => actions.get_int_upper_bound(var),
		VariableSelection::Smallest => actions.get_int_lower_bound(var),
	};

	let is_better = |incumbent_score, new_score| match var_sel {
		VariableSelection::AntiFirstFail | VariableSelection::Largest => {
			incumbent_score < new_score
		}
		VariableSelection::FirstFail | VariableSelection::Smallest => incumbent_score > new_score,
		VariableSelection::InputOrder => unreachable!(),
	};

	let mut first_unfixed = begin;
	let mut selection = None;
	for i in begin..vars.len() {
		if actions.get_int_lower_bound(vars[i]) == actions.get_int_upper_bound(vars[i]) {
			// move the unfixed variable to the front
			let unfixed_var = vars[first_unfixed];
			let fixed_var = vars[i];
			vars[first_unfixed] = fixed_var;
			vars[i] = unfixed_var;
			first_unfixed += 1;
		} else if let Some((_, sel_score)) = selection {
			let new_score = score(vars[i]);
			if is_better(sel_score, new_score) {
				selection = Some((vars[i], new_score));
			}
		} else {
			selection = Some((vars[i], score(vars[i])));
			if var_sel == VariableSelection::InputOrder {
				break;
			}
		}
	}
	// update the next variable to the index of the first unfixed variable
	let _ = actions.set_trailed_int(next, first_unfixed as i64);

	// return if all variables have been assigned
	let (next_var, _) = selection?;
	// select the next value to branch on based on the value selection strategy
	let view = match val_sel {
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
		BoolViewInner::Lit(lit) => Some(lit),
		_ => unreachable!(),
	}
}

impl Brancher {
	pub(crate) fn decide<E: ExplanationActions>(&mut self, actions: &mut E) -> Option<RawLit> {
		match &mut self.vars {
			BrancherVars::Bool(vars) => {
				decide_bool(actions, vars, self.var_sel, self.val_sel, self.next)
			}
			BrancherVars::Int(vars) => {
				decide_int(actions, vars, self.var_sel, self.val_sel, self.next)
			}
		}
	}

	pub(crate) fn prepare_bool(
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

	pub(crate) fn prepare_int(
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

impl BrancherPoster for BoolBrancherPoster {
	fn post<I: InitializationActions>(self, actions: &mut I) -> Brancher {
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
		Brancher {
			vars: BrancherVars::Bool(vars),
			var_sel: self.var_sel,
			val_sel: self.val_sel,
			next: actions.new_trailed_int(0),
		}
	}
}

impl BrancherPoster for IntBrancherPoster {
	fn post<I: InitializationActions>(self, actions: &mut I) -> Brancher {
		let vars: Vec<_> = self
			.vars
			.into_iter()
			.filter(|i| match i.0 {
				IntViewInner::Const(_) => false,
				IntViewInner::Bool { lit, .. } => {
					actions.subscribe_bool(BoolView(BoolViewInner::Lit(lit)), 0);
					true
				}
				_ => true,
			})
			.collect();
		Brancher {
			vars: BrancherVars::Int(vars),
			var_sel: self.var_sel,
			val_sel: self.val_sel,
			next: actions.new_trailed_int(0),
		}
	}
}
