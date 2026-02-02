//! Structures and algorithms for the Boolean array element constraint, which
//! enforces that a resulting variable equals an element of an array of Boolean
//! decision variables, chosen by an index variable.

use std::iter::once;

use crate::{
	IntVal,
	actions::{
		BoolInitActions, BoolSimplificationActions, IntDecisionActions, IntInitActions,
		IntInspectionActions, IntPropagationActions, ReasoningEngine,
	},
	constraints::{
		BoolModelActions, Constraint, IntModelActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::view::View,
	solver::{IntLitMeaning, activation_list::IntPropCond},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Representation of the `array_element` constraint with an array of Boolean
/// decision variables within a model.
///
/// This constraint enforces that a result Boolean decision variable takes the
/// value equal the element of the given array of Boolean decision variables at
/// the index given by the index integer decision variable.
pub struct BoolDecisionArrayElement {
	/// The array of Boolean decision variables
	pub(crate) array: Vec<View<bool>>,
	/// The index variable
	pub(crate) index: View<IntVal>,
	/// The resulting variable
	pub(crate) result: View<bool>,
}

impl<E> Constraint<E> for BoolDecisionArrayElement
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
	View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		Self::propagate(self, ctx)?;
		// Unify if the index is already fixed
		if let Some(i) = self.index.val(ctx) {
			self.array[i as usize].unify(ctx, self.result)?;
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let result = slv.solver_view(self.result);
		let index = slv.solver_view(self.index);

		// Evaluate result literal
		let arr: Vec<_> = self.array.iter().map(|&v| slv.solver_view(v)).collect();

		for (i, &l) in arr.iter().enumerate() {
			// Evaluate array literal
			let idx_eq = index.lit(slv, IntLitMeaning::Eq(i as IntVal));
			// add clause (idx = i + 1 /\ arr[i]) => val
			slv.add_clause([!idx_eq, !l, result])?;
			// add clause (idx = i + 1 /\ !arr[i]) => !val
			slv.add_clause([!idx_eq, l, !result])?;
		}

		// add clause (arr[1] /\ arr[2] /\ ... /\ arr[n]) => val
		slv.add_clause(arr.iter().map(|&l| !l).chain(once(result)))?;
		// add clause (!arr[1] /\ !arr[2] /\ ... /\ !arr[n]) => !val
		slv.add_clause(arr.into_iter().chain(once(!result)))?;
		Ok(())
	}
}

impl<E> Propagator<E> for BoolDecisionArrayElement
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
	View<bool>: BoolModelActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		for &b in &self.array {
			b.enqueue_when_fixed(ctx);
		}
		self.index.enqueue_when(ctx, IntPropCond::Fixed);
		self.result.enqueue_when_fixed(ctx);
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// Fix the bounds of the index is to the length of the array
		self.index.tighten_min(ctx, 0, vec![])?;
		self.index
			.tighten_max(ctx, self.array.len() as IntVal - 1, vec![])?;

		// TODO: Do more propagation
		Ok(())
	}
}
