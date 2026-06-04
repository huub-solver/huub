//! Module containing methods for making search decisions in the solver.

use std::{cmp, fmt::Debug};

use dyn_clone::DynClone;
use itertools::Itertools;
use rangelist::IntervalIterator;

use crate::{
	IntSet, IntVal,
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
	/// The Boolean value assigned to the selected decision variable first.
	///
	/// The [`DomainSelection`] strategy is reduced to this polarity when the
	/// brancher is installed (see [`BoolBrancher::new_in`]).
	value: bool,
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

/// Strategy of selecting the next decision variable for a [`BoolBrancher`] or
/// [`IntBrancher`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum DecisionSelection {
	/// Select the unfixed decision variable with the largest remaining domain
	/// size, using the order of the decisions in case of a tie.
	AntiFirstFail,
	/// Select the unfixed decision variable with the smallest remaining domain
	/// size divided by the number of subscribed propagators (its degree), using
	/// the order of the decisions in case of a tie. Decision variables without
	/// any attached propagators are selected last.
	DomWDeg,
	/// Select the unfixed decision variable with the smallest remaining domain
	/// size, using the order of the decisions in case of a tie.
	FirstFail,
	/// Select the first unfixed decision variable in the list.
	InputOrder,
	/// Select the unfixed decision variable with the largest upper bound, using
	/// the order of the decisions in case of a tie.
	Largest,
	/// Select the unfixed decision variable with the largest difference between
	/// the two smallest values in its domain, using the order of the decisions
	/// in case of a tie.
	MaxRegret,
	/// Select the unfixed decision variable with the smallest remaining domain
	/// size, breaking ties by the largest number of subscribed propagators and
	/// then by the order of the decisions.
	MostConstrained,
	/// Select the unfixed decision variable with the largest number of
	/// subscribed propagators, using the order of the decisions in case of a
	/// tie.
	Occurrence,
	/// Select the unfixed decision variable with the smallest lower bound,
	/// using the order of the decisions in case of a tie.
	Smallest,
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

/// Strategy for limiting the domain of a selected decision variable for a
/// [`BoolBrancher`] or [`IntBrancher`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum DomainSelection {
	/// If the domain consists of several contiguous intervals, reduce the
	/// domain to the first interval. Otherwise, bisect the domain (as
	/// [`Self::IndomainSplit`]).
	IndomainInterval,
	/// Set the decision variable to its current maximum value.
	IndomainMax,
	/// Set the decision variable to the median value in its domain, picking the
	/// smaller value when the domain has an even number of values.
	IndomainMedian,
	/// Set the decision variable to the value in its domain closest to the mean
	/// of its current bounds, preferring the smaller value when two are equally
	/// close.
	IndomainMiddle,
	/// Set the decision variable to its current minimum value.
	IndomainMin,
	/// Bisect the domain of the decision variable, exploring the half holding
	/// the larger values first.
	IndomainReverseSplit,
	/// Bisect the domain of the decision variable, exploring the half holding
	/// the smaller values first.
	IndomainSplit,
	/// Exclude the current upper bound value from the domain of the decision
	/// variable.
	OutdomainMax,
	/// Exclude the median value (as [`Self::IndomainMedian`]) from the domain
	/// of the decision variable.
	OutdomainMedian,
	/// Exclude the current lower bound value from the domain of the decision
	/// variable.
	OutdomainMin,
}

/// General brancher for integer decision variables that makes search decisions
/// by following a given [`DecisionSelection`] and [`DomainSelection`] strategy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntBrancher {
	/// Integer decision variables to be branched on.
	vars: Vec<View<IntVal>>,
	/// Number of propagator subscriptions for each decision variable in `vars`,
	/// captured when the brancher is installed and kept aligned with `vars`
	/// (including when it is reordered).
	///
	/// This is empty unless `var_sel` is one of the occurrence-based strategies
	/// ([`DecisionSelection::Occurrence`],
	/// [`DecisionSelection::MostConstrained`], or
	/// [`DecisionSelection::DomWDeg`]).
	degree: Vec<u32>,
	/// [`DecisionSelection`] strategy used to select the next decision variable
	/// to branch on.
	var_sel: DecisionSelection,
	/// [`DomainSelection`] strategy used to select the way in which to branch
	/// on the selected decision variable.
	val_sel: DomainSelection,
	/// The start of the unfixed decision variables in `vars`.
	next: Trailed<usize>,
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

/// Return the median value of the given (non-empty) domain: its middle value,
/// or the smaller of the two middle values when the domain holds an even number
/// of values.
fn domain_median(dom: &IntSet) -> IntVal {
	if let Some(card) = dom.card() {
		// The lower median is the value at this (zero-based) index in the domain.
		let mut index = (card - 1) / 2;
		for interval in dom.iter() {
			let len = (*interval.end() - *interval.start() + 1) as usize;
			if index < len {
				return *interval.start() + index as IntVal;
			}
			index -= len;
		}
	}
	let min = dom.min().unwrap();
	let max = dom.max().unwrap();
	min + (max - min) / 2
}

/// Return the value of the given (non-empty) domain closest to the mean,
/// preferring the smaller value when two are equally close.
fn domain_middle(dom: &IntSet) -> IntVal {
	// The largest domain value at or below the mean, and the smallest one above
	// it. As the decision variable is unfixed, `mid < max`, so the latter always
	// exists.
	let min = *dom.min().unwrap();
	let max = *dom.max().unwrap();
	let mid = min + (max - min) / 2;
	let mut below = min;
	let mut above = max;
	for interval in dom.iter() {
		let (start, end) = (*interval.start(), *interval.end());
		if start <= mid {
			below = cmp::min(end, mid);
		}
		if end > mid {
			above = cmp::max(start, mid + 1);
			break;
		}
	}
	// Compare doubled distances to the mean to stay in integer arithmetic.
	if (2 * below - (min + max)).abs() <= (2 * above - (min + max)).abs() {
		below
	} else {
		above
	}
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

		// A Boolean domain `{false, true}` has `false` as its lower value, median,
		// and middle, and forms a single interval, so every strategy that prefers
		// the smaller value branches on `false` first, and those that prefer the
		// larger value or exclude the median branch on `true` first.
		let value = match val_sel {
			DomainSelection::IndomainMax
			| DomainSelection::OutdomainMin
			| DomainSelection::IndomainReverseSplit
			| DomainSelection::OutdomainMedian => true,
			DomainSelection::IndomainMin
			| DomainSelection::OutdomainMax
			| DomainSelection::IndomainSplit
			| DomainSelection::IndomainInterval
			| DomainSelection::IndomainMedian
			| DomainSelection::IndomainMiddle => false,
		};

		let next = solver.new_trailed(0);
		solver.push_brancher(Box::new(BoolBrancher {
			vars,
			var_sel,
			value,
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

		// Return if all decisions have been assigned.
		if begin == self.vars.len() {
			return Directive::Exhausted;
		}

		// Boolean decision selection currently selects the first unfixed decision
		// variable, regardless of the configured decision selection strategy.
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

		// Branch on the selected decision variable using the precomputed polarity.
		Directive::Select(if self.value { var } else { !var }.into())
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

		// Only the occurrence-based strategies use the degree of a decision
		// variable. The degree is captured here, when the brancher is installed,
		// at which point all constraints (and therefore all propagators) have
		// been posted.
		let degree = matches!(
			var_sel,
			DecisionSelection::Occurrence
				| DecisionSelection::MostConstrained
				| DecisionSelection::DomWDeg
		)
		.then(|| vars.iter().map(|&v| solver.num_subscribers(v)).collect())
		.unwrap_or_default();

		let next = solver.new_trailed(0);
		solver.push_brancher(Box::new(IntBrancher {
			vars,
			degree,
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

		// return if all decisions have been assigned
		if begin == self.vars.len() {
			return Directive::Exhausted;
		}

		// Score a decision variable for the current strategy as a
		// `(primary, secondary)` pair; the secondary component is only used by
		// `MostConstrained` and `DomWDeg`, which require the decision variable's
		// `degree` (its number of attached propagators).
		let score = |var: View<IntVal>, degree: u32| -> (IntVal, IntVal) {
			match self.var_sel {
				DecisionSelection::AntiFirstFail | DecisionSelection::FirstFail => {
					let (lb, ub) = var.bounds(actions);
					(ub - lb, 0)
				}
				DecisionSelection::InputOrder => (0, 0),
				DecisionSelection::Largest => (var.max(actions), 0),
				DecisionSelection::Smallest => (var.min(actions), 0),
				DecisionSelection::Occurrence => (IntVal::from(degree), 0),
				DecisionSelection::MaxRegret => {
					// The difference between the two smallest values in the domain.
					let Some((first, second)) =
						var.domain(actions).iter().flatten().take(2).collect_tuple()
					else {
						unreachable!();
					};
					(second - first, 0)
				}
				DecisionSelection::MostConstrained | DecisionSelection::DomWDeg => {
					let (lb, ub) = var.bounds(actions);
					(ub - lb, IntVal::from(degree))
				}
			}
		};

		let is_better = |incumbent: (IntVal, IntVal), candidate: (IntVal, IntVal)| match self
			.var_sel
		{
			DecisionSelection::AntiFirstFail
			| DecisionSelection::Largest
			| DecisionSelection::Occurrence
			| DecisionSelection::MaxRegret => incumbent.0 < candidate.0,
			DecisionSelection::FirstFail | DecisionSelection::Smallest => incumbent.0 > candidate.0,
			DecisionSelection::MostConstrained => {
				// Smallest domain first, breaking ties by the largest degree.
				candidate.0 < incumbent.0
					|| (candidate.0 == incumbent.0 && candidate.1 > incumbent.1)
			}
			DecisionSelection::DomWDeg => {
				// Smallest domain size divided by degree, treating a degree of
				// zero as an infinite ratio so such decision variables are selected
				// last.
				// The ratios are compared by cross-multiplication, widened to
				// `i128` to avoid overflow.
				match (incumbent.1, candidate.1) {
					(0, 0) => false,
					(0, _) => true,
					(_, 0) => false,
					(incumbent_deg, candidate_deg) => {
						i128::from(candidate.0) * i128::from(incumbent_deg)
							< i128::from(incumbent.0) * i128::from(candidate_deg)
					}
				}
			}
			DecisionSelection::InputOrder => unreachable!(),
		};

		let mut first_unfixed = begin;
		let mut selection = None;
		for i in begin..self.vars.len() {
			if self.vars[i].min(actions) == self.vars[i].max(actions) {
				// Move the fixed decision variable to the front, keeping `degree`
				// aligned with `vars` when it is populated.
				self.vars.swap(first_unfixed, i);
				if !self.degree.is_empty() {
					self.degree.swap(first_unfixed, i);
				}
				first_unfixed += 1;
			} else {
				let var = self.vars[i];
				// `degree` is empty (and thus the degree zero) for the strategies
				// that do not use it.
				let new_score = score(var, self.degree.get(i).copied().unwrap_or(0));
				if let Some((_, sel_score)) = selection {
					if is_better(sel_score, new_score) {
						selection = Some((var, new_score));
					}
				} else {
					selection = Some((var, new_score));
					if self.var_sel == DecisionSelection::InputOrder {
						break;
					}
				}
			}
		}

		// return if all decisions have been assigned
		let Some((next_var, _)) = selection else {
			return Directive::Exhausted;
		};

		// update the next decision to the index of the first unfixed decision
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
				// The selected decision variable is unfixed, so `min < max` and the bisection
				// point `min + (max - min) / 2` lies in `min..max`, leaving both
				// halves non-empty and guaranteeing the search makes progress.
				DomainSelection::IndomainSplit => {
					let (min, max) = next_var.bounds(actions);
					IntLitMeaning::Less(min + (max - min) / 2 + 1)
				}
				DomainSelection::IndomainReverseSplit => {
					let (min, max) = next_var.bounds(actions);
					IntLitMeaning::GreaterEq(min + (max - min) / 2 + 1)
				}
				DomainSelection::IndomainMedian => {
					IntLitMeaning::Eq(domain_median(&next_var.domain(actions)))
				}
				DomainSelection::OutdomainMedian => {
					IntLitMeaning::NotEq(domain_median(&next_var.domain(actions)))
				}
				DomainSelection::IndomainMiddle => {
					IntLitMeaning::Eq(domain_middle(&next_var.domain(actions)))
				}
				DomainSelection::IndomainInterval => {
					let dom = next_var.domain(actions);
					let mut intervals = dom.iter();
					let first = intervals
						.next()
						.expect("the domain of an unfixed decision variable is non-empty");
					if intervals.next().is_some() {
						// Several contiguous intervals: reduce to the first interval.
						IntLitMeaning::Less(*first.end() + 1)
					} else {
						// A single interval: bisect as `indomain_split`.
						let (min, max) = next_var.bounds(actions);
						IntLitMeaning::Less(min + (max - min) / 2 + 1)
					}
				}
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

#[cfg(test)]
mod tests {
	use crate::{
		IntSet,
		solver::branchers::{domain_median, domain_middle},
	};

	#[test]
	fn test_domain_median() {
		// Odd number of values: the single middle value.
		assert_eq!(domain_median(&IntSet::from_iter([1..=5])), 3);
		// Even number of values: the smaller of the two middle values.
		assert_eq!(domain_median(&IntSet::from_iter([1..=4])), 2);
		// Holes are skipped: the median is the middle element, not the bound
		// midpoint (which would be `4` and `3` respectively here).
		assert_eq!(domain_median(&IntSet::from_iter([1..=3, 7..=8])), 3);
		assert_eq!(domain_median(&IntSet::from_iter([1..=2, 10..=12])), 10);
		assert_eq!(domain_median(&IntSet::from_iter([1..=2, 5..=6])), 2);
	}

	#[test]
	fn test_domain_middle() {
		// Mean of the bounds is in the domain.
		assert_eq!(domain_middle(&IntSet::from_iter([0..=10])), 5);
		// Mean falls between two values: the smaller is preferred.
		assert_eq!(domain_middle(&IntSet::from_iter([0..=9])), 4);
		// The value closest to the mean of the bounds, regardless of element
		// counts: the mean `4.5` is nearest to `3` (not the median `7`).
		assert_eq!(domain_middle(&IntSet::from_iter([0..=3, 7..=9])), 3);
		// Equally close below and above the mean: the smaller is preferred.
		assert_eq!(domain_middle(&IntSet::from_iter([0..=1, 8..=9])), 1);
		// The closest value lies above the mean.
		assert_eq!(domain_middle(&IntSet::from_iter([0..=0, 8..=10])), 8);
	}
}
