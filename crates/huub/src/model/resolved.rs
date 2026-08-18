//! Resolved model handles that no longer carry aliasing ambiguity.

use std::{num::NonZero, ops::Not};

use crate::{
	Cloner, DeepClone, IntVal,
	actions::IntInspectionActions,
	model::{
		Decision, Model, View,
		decision::integer::Domain,
		view::{boolean::BoolView, integer::IntView},
	},
};

/// Wrapper for model values whose aliases have been resolved against a model.
///
/// This type marks a model handle whose alias chain has already been followed
/// against the current model state. The claim only holds at the moment it is
/// made, so a mutating operation must keep the wrapper up to date or discard
/// it. `Clone` exists only because
/// [`IntOperations`](crate::actions::IntOperations) and
/// [`BoolOperations`](crate::actions::BoolOperations) require it: store the
/// unresolved handle and resolve again where needed, rather than keeping a
/// clone.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Resolved<T>(pub(crate) T);

impl Decision<IntVal> {
	/// Resolve this decision into a view that no longer references aliases.
	pub(crate) fn resolve_alias(self, model: &Model) -> Resolved<View<IntVal>> {
		View::from(self).resolve_alias(model)
	}
}

impl Decision<bool> {
	/// Resolve this decision into a view that no longer references aliases.
	pub(crate) fn resolve_alias(self, model: &Model) -> Resolved<View<bool>> {
		View::from(self).resolve_alias(model)
	}
}

impl Resolved<Decision<IntVal>> {
	/// Return the storage index of the resolved decision.
	pub(crate) fn idx(&self) -> usize {
		self.0.idx()
	}
}

impl<T> Resolved<T> {
	/// Return the wrapped resolved value.
	pub(crate) fn into_inner(self) -> T {
		self.0
	}
}

impl Resolved<View<IntVal>> {
	/// Return the underlying canonical decision when the resolved view is
	/// backed by an integer decision variable.
	pub(crate) fn integer_decision(&self) -> Option<Resolved<Decision<IntVal>>> {
		match self.0.0 {
			IntView::Linear(lin) => Some(Resolved(lin.var)),
			IntView::Const(_) | IntView::Bool(_) => None,
		}
	}
}

impl Resolved<View<bool>> {
	/// Return the underlying canonical decision when the resolved view is
	/// backed by a Boolean decision variable, rather than a constant or a
	/// literal derived from an integer comparison.
	pub(crate) fn decision(&self) -> Option<Resolved<Decision<bool>>> {
		match self.0.0 {
			BoolView::Decision(d) => Some(Resolved(d)),
			BoolView::Const(_)
			| BoolView::IntEq(..)
			| BoolView::IntGreaterEq(..)
			| BoolView::IntLess(..)
			| BoolView::IntNotEq(..) => None,
		}
	}
}

impl<T> DeepClone for Resolved<T> {
	fn deep_clone_in(&self, _: &mut Cloner) -> Self {
		unreachable!(
			"resolved views should not be cloned as it can then no longer guarantee it stays resolved."
		)
	}
}

impl<T: Not> Not for Resolved<T> {
	type Output = Resolved<T::Output>;

	fn not(self) -> Self::Output {
		Resolved(!self.0)
	}
}

impl View<IntVal> {
	/// Resolve any aliasing in the IntDecision, ensuring the result is a
	/// IntDecision that if it is a `Var` or `Linear`, then the domain is not an
	/// alias.
	pub(crate) fn resolve_alias(self, model: &Model) -> Resolved<Self> {
		use IntView::*;

		let mut view = self;
		let mut scale = 1;
		let mut offset = 0;
		loop {
			match view.0 {
				Const(c) => {
					return Resolved((c * scale + offset).into());
				}
				_ if scale == 0 => {
					return Resolved(offset.into());
				}
				Linear(lin) => match model.int_vars[lin.var.idx()].domain {
					Domain::Domain(_) => {
						return Resolved(View(Linear(lin * NonZero::new(scale).unwrap() + offset)));
					}
					Domain::Alias(alias) => {
						view = alias;
						offset += scale * lin.offset;
						scale *= lin.scale.get();
					}
				},
				Bool(lin) => {
					let var = lin.var.resolve_alias(model).into_inner();
					if let BoolView::Const(b) = var.0 {
						return Resolved(View(Const(
							lin.transform_val(b as IntVal) * scale + offset,
						)));
					}
					return Resolved(View(Bool(lin * NonZero::new(scale).unwrap() + offset)));
				}
			}
		}
	}
}

impl View<bool> {
	/// Resolve any aliasing in the BoolDecision, ensuring the result is a
	/// BoolDecision that if it is a `Lit`, then it is not an alias.
	pub(crate) fn resolve_alias(self, model: &Model) -> Resolved<Self> {
		use BoolView::*;

		let mut result = self;
		// If the current Lit is an alias, then resolve it.
		while let Decision(lit) = result.0 {
			if let Some(alias) = model.bool_vars[lit.idx()].alias {
				debug_assert_ne!(alias, result);
				debug_assert_ne!(alias, !result);
				result = if lit.is_negated() { !alias } else { alias };
			} else {
				break;
			}
		}
		// If the current literal is an integer view, check whether it is
		// already fixed.
		match result.0 {
			IntEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return Resolved(false.into());
				} else if val == lb && val == ub {
					return Resolved(true.into());
				}
			}
			IntGreaterEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if lb >= val {
					return Resolved(true.into());
				} else if ub < val {
					return Resolved(false.into());
				}
			}
			IntLess(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if ub < val {
					return Resolved(true.into());
				} else if lb >= val {
					return Resolved(false.into());
				}
			}
			IntNotEq(iv, val) => {
				let (lb, ub) = iv.bounds(model);
				if val < lb || val > ub {
					return Resolved(true.into());
				} else if val == lb && val == ub {
					return Resolved(false.into());
				}
			}
			_ => {}
		}
		Resolved(result)
	}
}
