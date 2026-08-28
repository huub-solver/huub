//! Decision variable types and helpers for [`Model`].

pub(crate) mod boolean;
pub(crate) mod integer;

use crate::{DeepClone, solver::Polarity};

/// A typed handle to a decision variable in a model.
#[derive(Clone, Copy, Debug, DeepClone, Eq, Hash, PartialEq)]
#[deepclone(bound = "T: DecisionReference, T::Ref: Clone")]
pub struct Decision<T: DecisionReference>(#[deepclone(clone)] pub(crate) T::Ref);

/// Marker trait for types that can be used as model decision references.
pub trait DecisionReference: private::Sealed + 'static {
	/// The underlying reference type stored in [`Decision`].
	type Ref;
}

/// Accumulated, signed polarity evidence for a single decision variable.
///
/// Positive weights indicate a preference for larger values, negative weights a
/// preference for smaller values. The magnitude captures the quantity of
/// evidence (e.g. the number of constraints, or a coefficient).
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct PolarityScore {
	/// Signed evidence collected from the objective.
	objective: i32,
	/// Signed evidence collected from constraints.
	constraint: i32,
}

/// The priority tier of a piece of polarity evidence collected during the
/// [`analyze`](crate::constraints::Constraint::analyze) stage.
///
/// Evidence from the objective strictly dominates evidence from constraints:
/// any nonzero objective signal decides the polarity on its own, and constraint
/// evidence is only consulted when the objective tier is silent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Tier {
	/// Evidence derived from a constraint (lower priority).
	Constraint,
	/// Evidence derived from the objective (higher priority).
	Objective,
}

impl PolarityScore {
	/// Record one unit of evidence in the given `tier` for the given direction.
	pub(crate) fn observe(&mut self, tier: Tier, polarity: Polarity) {
		let field = match tier {
			Tier::Objective => &mut self.objective,
			Tier::Constraint => &mut self.constraint,
		};
		let weight = match polarity {
			Polarity::Positive => 1,
			Polarity::Negative => -1,
		};
		*field = field.saturating_add(weight);
	}

	/// Collapse the accumulated evidence into a single preferred direction, or
	/// `None` if the evidence is balanced.
	///
	/// Objective evidence strictly dominates: the constraint tier is only
	/// consulted when the objective tier is silent.
	pub(crate) fn resolve(&self) -> Option<Polarity> {
		let decisive = if self.objective != 0 {
			self.objective
		} else {
			self.constraint
		};
		match decisive.signum() {
			1 => Some(Polarity::Positive),
			-1 => Some(Polarity::Negative),
			_ => None,
		}
	}
}

/// Sealing helpers for model decision reference traits.
mod private {
	/// Helper trait that ensures that the [`DecisionStorage`] trait cannot be
	/// implemented outside of this crate.
	pub trait Sealed {}
}
