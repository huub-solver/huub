//! Structures and algorithms for the integer in set constraint, which
//! constraints that an integer decision variable is assigned to a member of a
//! given set if-and-only-if a given Boolean decision variable is assigned to
//! `true`.

use itertools::Itertools;
use pindakaas::propositional_logic::Formula;
use rangelist::IntervalIterator;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInitActions, BoolInspectionActions, BoolPropagationActions, BoolSimplificationActions,
		IntInitActions, IntInspectionActions, IntPropCond, IntSimplificationActions,
		ReasoningEngine, SimplificationActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, IntModelActions, IntSolverActions,
		Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::{expressions::BoolFormula, view::View},
};

/// Representation of the integer `contains` constraint within a model.
///
/// This constraint enforces that the given Boolean variable takes the value
/// `true` if-and-only-if an integer variable is in a given set.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntSetContainsReif {
	/// The integer decision variable monitored.
	pub(crate) var: View<IntVal>,
	/// The set of considered values for the integer decision variable.
	pub(crate) set: IntSet,
	/// The Boolean variable that indicates if the integer decision variable is
	/// in the set.
	pub(crate) reif: View<bool>,
}

impl<E> Constraint<E> for IntSetContainsReif
where
	E: ReasoningEngine,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	View<IntVal>: IntModelActions<E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// Check whether `reif` is set, then just enforce the domain.
		match self.reif.val(ctx) {
			Some(true) => {
				self.var
					.restrict_domain(ctx, &self.set, [self.reif.into()])?;
				return Ok(SimplificationStatus::Subsumed);
			}
			Some(false) => {
				self.var.exclude(ctx, &self.set, [(!self.reif).into()])?;
				return Ok(SimplificationStatus::Subsumed);
			}
			None => {}
		}
		// Compute the overlap between the set and the domain of `var`.
		let domain = self.var.domain(ctx);
		self.set = self.set.intersect(&domain);
		// If the intersection is empty, then `reif` must be false.
		if self.set.is_empty() {
			self.reif
				.fix(ctx, false, |_: &mut E::PropagationContext<'_>| {
					self.set
						.iter()
						.flatten()
						.map(|v| self.var.ne(v).into())
						.collect_vec()
				})?;
			return Ok(SimplificationStatus::Subsumed);
		}
		// If `set` is a superset of domain, then it is known that `reif` is true.
		// (After intersection, we can just check equality)
		if domain == self.set {
			self.reif.require(ctx, [])?;
			return Ok(SimplificationStatus::Subsumed);
		}
		// Otherwise, we check whether we can rewrite the constraint into a simpler
		// form.
		if self.set.intervals().len() == 1 {
			let lb = self.set.lower_bound().unwrap();
			let ub = self.set.upper_bound().unwrap();
			if lb == ub {
				self.reif.unify(ctx, self.var.eq(*lb))?;
				return Ok(SimplificationStatus::Subsumed);
			}
			if lb == domain.lower_bound().unwrap() {
				self.reif.unify(ctx, self.var.leq(*ub))?;
				return Ok(SimplificationStatus::Subsumed);
			}
			if ub == domain.upper_bound().unwrap() {
				self.reif.unify(ctx, self.var.geq(*lb))?;
				return Ok(SimplificationStatus::Subsumed);
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		if self.set.iter().len() == 1 {
			let lb = *self.set.lower_bound().unwrap();
			let ub = *self.set.upper_bound().unwrap();
			<BoolFormula as Constraint<E>>::to_solver(
				&Formula::Equiv(vec![
					Formula::And(vec![self.var.geq(lb).into(), self.var.leq(ub).into()]),
					self.reif.into(),
				]),
				slv,
			)
		} else {
			let eq_lits = self
				.set
				.iter()
				.flatten()
				.map(|v| self.var.eq(v).into())
				.collect();
			<BoolFormula as Constraint<E>>::to_solver(
				&Formula::Equiv(vec![self.reif.into(), Formula::Or(eq_lits)]),
				slv,
			)
		}
	}
}

impl<E> Propagator<E> for IntSetContainsReif
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
	View<bool>: BoolSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		self.var.enqueue_when(ctx, IntPropCond::Domain);
		self.reif.enqueue_when_fixed(ctx);
	}

	fn propagate(&mut self, _: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		unreachable!()
	}
}
