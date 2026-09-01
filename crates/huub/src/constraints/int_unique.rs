//! Structure and algorithms for the integer unique constraint, which
//! enforces that a list of integer variables each take a different value.
//!
//! This module exposes the [`IntUnique`] model constraint together with the
//! three propagator strengths it can be lowered to: [`IntUniqueValue`] (value
//! consistency), [`IntUniqueBounds`] (bounds consistency), and
//! [`IntUniqueDomain`] (domain consistency). Each propagator lives in a
//! private submodule with its dedicated helpers; the propagator types
//! themselves are re-exported here.

mod bounds;
mod domain;
mod value;

use itertools::{Either, Itertools};
use rangelist::IntervalIterator;
use tracing::warn;

pub use crate::constraints::int_unique::{
	bounds::IntUniqueBounds, domain::IntUniqueDomain, value::IntUniqueValue,
};
use crate::{
	DeepClone, IntSet, IntVal,
	actions::{IntAnalyzeActions, IntEvent, IntInspectionActions, ReasoningEngine},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
};

/// Representation of the integer `unique` constraint within a model.
///
/// This constraint enforces that all the given integer decisions take different
/// values.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub struct IntUnique {
	/// Instance of the [`IntUniqueBounds`] propagator.
	pub(crate) bounds_prop: IntUniqueBounds<View<IntVal>>,
	/// Instance of the [`IntUniqueValue`] propagator.
	pub(crate) value_prop: IntUniqueValue<View<IntVal>>,
	/// Whether to enable the bounds consistent propagator.
	///
	/// Defaults to `true`.
	pub(crate) bounds_propagation: Option<bool>,
	/// Whether to enable the value consistent propagator.
	///
	/// Defaults to `false`.
	pub(crate) value_propagation: Option<bool>,
	/// Whether to enable the domain consistent propagator.
	///
	/// Defaults to `false`.
	pub(crate) domain_propagation: Option<bool>,
}

impl IntUnique {
	/// Returns whether a bounds consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn bounds_propagation(&self) -> bool {
		self.bounds_propagation.unwrap_or(true)
	}

	/// Returns whether a domain consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn domain_propagation(&self) -> bool {
		self.domain_propagation.unwrap_or(false)
	}

	/// Returns whether a value consistent propagator will be posted when
	/// creating a [`Solver`](crate::solver::Solver) object.
	pub fn value_propagation(&self) -> bool {
		self.value_propagation.unwrap_or(false)
	}
}

impl<E> Constraint<E> for IntUnique
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		// The direct encoding is only used by the value- and domain-consistency
		// propagators.
		if !(self.value_propagation() || self.domain_propagation()) {
			return;
		}

		// The eager value encoding pays off when the decisions jointly range
		// over few values relative to their number. Use the cardinality of
		// the union of all the decision variable domains.
		let dcns = &self.bounds_prop.vars;
		let mut union: Option<IntSet> = None;
		for d in dcns {
			let dom = d.domain(ctx);
			union = Some(match union {
				None => dom,
				Some(u) => u.union(&dom),
			});
		}
		let tight = union
			.and_then(|u| u.card())
			.is_some_and(|card| card <= dcns.len() * 100 / 80);
		if tight {
			for d in dcns {
				d.request_direct_eager(ctx);
			}
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let (_vals, vars): (Vec<_>, Vec<_>) = self.bounds_prop.vars.iter().partition_map(|&var| {
			let var = slv.solver_view(var);
			if let Some(val) = var.val(slv) {
				Either::Left(val)
			} else {
				Either::Right(var)
			}
		});
		// Propagation should have detected any duplicate fixed values and
		// removed them from the domains of other decision variables.
		debug_assert!(_vals.iter().unique().collect_vec().len() == _vals.len());
		debug_assert!(
			_vals
				.iter()
				.all(|&val| vars.iter().all(|var| !var.in_domain(slv, val)))
		);

		// If the number of non-fixed decision variables is less than or equal
		// to 1, there is no need to post any propagators.
		if vars.len() <= 1 {
			return Ok(());
		}

		let value_propagation = self.value_propagation();
		if value_propagation {
			IntUniqueValue::post(slv, vars.clone());
		}
		let domain_propagation = self.domain_propagation();
		let mut bounds_propagation = self.bounds_propagation();
		if !value_propagation && !bounds_propagation && !domain_propagation {
			warn!(
				"all propagation algorithms are disabled for `int_unique` constraint, override with bounds propagation to ensure consistency"
			);
			bounds_propagation = true;
		}
		if bounds_propagation {
			IntUniqueBounds::post(slv, vars.clone());
		}
		if domain_propagation {
			IntUniqueDomain::post(slv, vars);
		}
		Ok(())
	}
}

impl<E> Propagator<E> for IntUnique
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, ctx: &mut E::NotificationContext<'_>) {
		self.value_prop.advise_of_backtrack(ctx);
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		match event {
			IntEvent::Fixed => self.value_prop.advise_of_int_change(ctx, data, event),
			IntEvent::Bounds => self.bounds_prop.advise_of_int_change(ctx, data, event),
			_ => unreachable!("IntUnique should only be advised of Fixed and Bounds events"),
		}
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		self.value_prop.initialize(ctx);
		self.bounds_prop.initialize(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		if self.value_prop.has_pending_actions() {
			self.value_prop.propagate(ctx)?;
		}
		self.bounds_prop.propagate(ctx)
	}
}

#[cfg(test)]
mod tests {
	use tracing_test::traced_test;

	use crate::{IntSet, model::Model};

	#[test]
	#[traced_test]
	fn test_gapped_domain_regression() {
		let mut prb = Model::default();
		let prev: Vec<_> = [
			IntSet::from_iter([15..=15, 20..=20]),
			(20..=20).into(),
			IntSet::from_iter([15..=15, 20..=20]),
		]
		.into_iter()
		.map(|domain| prb.new_int_decision(domain))
		.collect();

		assert!(prb.unique(prev.iter().copied()).post().is_err());
	}

	#[test]
	#[traced_test]
	fn test_lowering_gapped_fixed_sound() {
		use itertools::Itertools;

		use crate::solver::Solver;

		let mut prb = Model::default();
		let vars: Vec<_> = [
			IntSet::from_iter([1..=2, 4..=6]),
			IntSet::from_iter([1..=1, 3..=4, 6..=6]),
			IntSet::from_iter([2..=2, 5..=5]),
			IntSet::from_iter([3..=3, 5..=5]),
			IntSet::from(3..=6),
			(2..=2).into(),
		]
		.into_iter()
		.map(|domain| prb.new_int_decision(domain))
		.collect();
		prb.unique(vars.iter().copied())
			.post()
			.expect("post failed");

		let (mut slv, map): (Solver, _) = prb.lower().to_solver().expect("to_solver failed");
		let views: Vec<_> = vars.iter().map(|&v| map.get(&mut slv, v)).collect();
		slv.assert_all_solutions(&views, |sol| sol.iter().all_unique());
	}
}
