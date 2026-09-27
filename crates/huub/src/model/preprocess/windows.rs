//! The logging of changes to the constraints of the model, in windows around
//! the posting of FlatZinc constraints and the simplification of constraints.

use std::fmt::Write;

use crate::{
	constraints::{Constraint, SimplificationStatus},
	model::{
		ConstraintId, Model, View,
		preprocess::{
			fzt::{FztConstraint, FztContext, FztError},
			normalize::lin_norm_equal,
			registry,
			rule::{PreprocessRule, StepKind},
			spelling,
			state::{FznOutcome, Output, Window, WindowKind},
		},
	},
};

impl Model {
	/// Record that search assumes the literals `lits` to hold, as stated by
	/// the `huub_assume` constraint being posted.
	pub(crate) fn trace_assume(&mut self, lits: Vec<View<bool>>) {
		if !self.trace_active() {
			return;
		}
		if let Some(w) = self.trace.recording_mut().unwrap().windows.last_mut() {
			w.assumed.push(lits);
		}
	}
	/// Render the constraint `con` (or the given object, if it is not in the
	/// model) as a trace item under a fresh trace identifier, returning the
	/// identifier, the item, and the constraint.
	pub(super) fn trace_constraint_item(
		&mut self,
		con: ConstraintId,
		obj: Option<&dyn Constraint<Model>>,
	) -> Result<(u32, String, FztConstraint), FztError> {
		let c = obj
			.or_else(|| self.constraints[con.index()].as_deref())
			.expect("a constraint is logged while it is in the model or being simplified");
		let item = registry::to_fzt(c, &FztContext::new(self))?;
		let t = self.trace.recording_mut().unwrap();
		let id = t.fresh_id();
		t.origin[con.index()] = Some(id);
		Ok((id, format!("constraint {item} :: trace_id({id});"), item))
	}
	/// Log the steps for the constraint `con` that has been posted.
	pub(crate) fn trace_constraint_posted(&mut self, con: ConstraintId) -> Result<(), FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(());
		};
		if t.origin.len() <= con.index() {
			t.origin.resize(con.index() + 1, None);
		}
		if let Some(w) = t.windows.last_mut() {
			w.posted.push(con);
			return Ok(());
		}
		// Constraints posted outside of any window are added right away.
		self.trace_flush();
		let (id, item, _) = self.trace_constraint_item(con, None)?;
		let text = format!("add #{id} by preserve\n  {item}");
		self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
		Ok(())
	}
	/// Whether the initial simplification of the constraint `con` is deferred
	/// until the current window closes.
	///
	/// During the posting of a FlatZinc constraint, the constraints that are
	/// created are only simplified after all of them have been logged, so that
	/// the steps of the simplification refer to constraints that have been
	/// introduced.
	pub(crate) fn trace_defer_simplification(&mut self, con: ConstraintId) -> bool {
		if !self.trace_active() {
			return false;
		}
		match self.trace.recording_mut().unwrap().windows.last_mut() {
			Some(
				w @ Window {
					kind: WindowKind::FznPosting,
					..
				},
			) => {
				w.deferred.push(con);
				true
			}
			_ => false,
		}
	}
	/// Close the window of the extraction of a view from, or the posting of,
	/// the FlatZinc constraint with trace identifier `fzn`, logging what
	/// became of the constraint.
	///
	/// For a posting, `rewrite_rule` justifies the replacement of the FlatZinc
	/// constraint by the constraints that were posted for it, given their
	/// `.fzt` representations; `del_rule` justifies its removal when nothing
	/// was posted.
	///
	/// Returns the constraints whose initial simplification was deferred, which
	/// the caller must now simplify.
	pub(crate) fn trace_fzn_close(
		&mut self,
		outcome: FznOutcome,
		rewrite_rule: impl FnOnce(&[FztConstraint]) -> PreprocessRule,
		del_rule: PreprocessRule,
	) -> Result<Vec<ConstraintId>, FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(Vec::new());
		};
		let w = t.windows.pop().expect("window was not opened");
		t.suppressed = None;
		debug_assert!(matches!(
			w.kind,
			WindowKind::FznPosting | WindowKind::FznView
		));
		let fzn = w.hint.unwrap();
		self.trace_flush();
		match outcome {
			FznOutcome::Conflict => {
				let text = format!("unsat by preserve hint #{fzn}");
				self.trace_emit(StepKind::Unsat, Some(PreprocessRule::Preserve), text);
				return Ok(w.deferred);
			}
			FznOutcome::Failed => return Ok(w.deferred),
			FznOutcome::Processed | FznOutcome::Unprocessed => {}
		}
		let mut outputs = Vec::with_capacity(w.posted.len() + w.assumed.len());
		for &con in &w.posted {
			let Some(c) = self.constraints[con.index()].as_deref() else {
				continue;
			};
			let item = registry::to_fzt(c, &FztContext::new(self))?;
			outputs.push((Output::Constraint(con), item));
		}
		for lits in w.assumed {
			let item = FztConstraint::new(
				spelling::ASSUME,
				vec![FztContext::new(self).bools(lits.iter().copied())],
			);
			outputs.push((Output::Assumption(lits), item));
		}
		if outcome == FznOutcome::Unprocessed {
			// The constraint remains, and anything posted is added as implied
			// by it.
			for (out, item) in outputs {
				let t = self.trace.recording_mut().unwrap();
				let id = t.fresh_id();
				t.record_output(id, out);
				let text = format!(
					"add #{id} by preserve hint #{fzn}\n  constraint {item} :: trace_id({id});"
				);
				self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
			}
			return Ok(w.deferred);
		}
		if outputs.is_empty() {
			let rule = if del_rule.fits(StepKind::Del) {
				del_rule
			} else {
				PreprocessRule::Preserve
			};
			let text = format!("del #{fzn} by {}", rule.as_str());
			self.trace_emit(StepKind::Del, Some(rule), text);
			return Ok(w.deferred);
		}
		let items: Vec<_> = outputs.iter().map(|(_, item)| item.clone()).collect();
		let rule = rewrite_rule(&items);
		let rule = if rule.fits(StepKind::Rewrite) {
			rule
		} else {
			PreprocessRule::Preserve
		};
		let t = self.trace.recording_mut().unwrap();
		let mut ids = Vec::with_capacity(outputs.len());
		let mut cont = String::new();
		for (out, item) in outputs {
			let id = t.fresh_id();
			t.record_output(id, out);
			ids.push(format!("#{id}"));
			write!(cont, "\n  constraint {item} :: trace_id({id});").unwrap();
		}
		let text = format!(
			"rewrite #{fzn} => {} by {}{cont}",
			ids.join(" "),
			rule.as_str()
		);
		self.trace_emit(StepKind::Rewrite, Some(rule), text);
		Ok(w.deferred)
	}
	/// Open the window of the extraction of a view from (if `view`), or the
	/// posting of, the FlatZinc constraint at index `fzn`, whose steps are
	/// justified by `rule`.
	pub(crate) fn trace_fzn_open(&mut self, fzn: usize, view: bool, rule: PreprocessRule) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		t.windows.push(Window {
			kind: if view {
				WindowKind::FznView
			} else {
				WindowKind::FznPosting
			},
			hint: Some(fzn as u32 + 1),
			rule,
			posted: Vec::new(),
			assumed: Vec::new(),
			deferred: Vec::new(),
		});
	}
	/// Close the window of the simplification of a constraint, which ended with
	/// `status` (or a conflict), logging what became of the constraint.
	pub(crate) fn trace_simplify_close(
		&mut self,
		obj: &dyn Constraint<Model>,
		status: Result<SimplificationStatus, ()>,
	) -> Result<(), FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(());
		};
		let w = t.windows.pop().expect("window was not opened");
		t.suppressed = None;
		let WindowKind::Simplify {
			con,
			debug,
			item: before,
		} = w.kind
		else {
			unreachable!("closing a window that is not a simplification")
		};
		let id = w.hint.unwrap();
		self.trace_flush();
		let status = match status {
			Ok(status) => status,
			Err(()) => {
				let text = format!("unsat by preserve hint #{id}");
				self.trace_emit(StepKind::Unsat, Some(PreprocessRule::Preserve), text);
				return Ok(());
			}
		};
		let mut outputs = Vec::new();
		let replaced = match status {
			SimplificationStatus::Subsumed => true,
			SimplificationStatus::NoFixpoint => {
				// A constraint whose own representation did not change is only
				// affected by the substitutions, which the checker performs
				// itself.
				let after = registry::to_fzt(obj, &FztContext::new(self))?;
				if after != before && format!("{obj:?}") != debug {
					outputs.push(self.trace_constraint_item(con, Some(obj))?);
					true
				} else {
					false
				}
			}
		};
		for &posted in &w.posted {
			if self.constraints[posted.index()].is_none() {
				continue;
			}
			outputs.push(self.trace_constraint_item(posted, None)?);
		}
		if replaced {
			let kind = if outputs.is_empty() {
				StepKind::Del
			} else {
				StepKind::Rewrite
			};
			let rule = match (w.rule, outputs.as_slice()) {
				// A claim of `lin-norm` is only made when the normal forms are
				// indeed equal, which can fail when a simplification relies on
				// the domains, e.g. to evaluate a literal view.
				(PreprocessRule::LinNorm, [(_, _, after)])
					if lin_norm_equal(&before, after) == Some(false) =>
				{
					PreprocessRule::Preserve
				}
				(rule, _) if rule.fits(kind) => rule,
				_ => PreprocessRule::Preserve,
			};
			let text = if outputs.is_empty() {
				format!("del #{id} by {}", rule.as_str())
			} else {
				let ids: Vec<_> = outputs.iter().map(|(n, _, _)| format!("#{n}")).collect();
				let items: Vec<_> = outputs.iter().map(|(_, i, _)| format!("\n  {i}")).collect();
				format!(
					"rewrite #{id} => {} by {}{}",
					ids.join(" "),
					rule.as_str(),
					items.concat()
				)
			};
			self.trace_emit(kind, Some(rule), text);
		} else {
			for (n, item, _) in outputs {
				let text = format!("add #{n} by preserve hint #{id}\n  {item}");
				self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
			}
		}
		Ok(())
	}
	/// Open the window of the simplification of the constraint `con`, returning
	/// whether the simplification is traced.
	pub(crate) fn trace_simplify_open(
		&mut self,
		con: ConstraintId,
		obj: &dyn Constraint<Model>,
	) -> Result<bool, FztError> {
		if !self.trace_active() {
			return Ok(false);
		}
		self.trace_flush();
		let Some(Some(id)) = self
			.trace
			.recording()
			.unwrap()
			.origin
			.get(con.index())
			.copied()
		else {
			return Err(FztError::UnloggedConstraint);
		};
		let item = registry::to_fzt(obj, &FztContext::new(self))?;
		self.trace.recording_mut().unwrap().windows.push(Window {
			kind: WindowKind::Simplify {
				con,
				debug: format!("{obj:?}"),
				item,
			},
			hint: Some(id),
			rule: PreprocessRule::Preserve,
			posted: Vec::new(),
			assumed: Vec::new(),
			deferred: Vec::new(),
		});
		Ok(true)
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		DeepClone,
		actions::ReasoningEngine,
		constraints::{Constraint, Propagator, SimplificationStatus},
		lower::{LoweringContext, LoweringError},
		model::{Model, preprocess::FztError},
	};

	/// A constraint without a representation in the `.fzt` model language.
	#[derive(Clone, Debug, DeepClone)]
	struct Unwritable;

	/// A constraint that cannot be written ends the trace, and the error is
	/// returned when the trace is finished.
	#[test]
	fn unwritable_constraint_fails_the_trace() {
		let mut prb = Model::default();
		prb.trace_start(0, None);
		assert!(prb.trace_active());
		let _ = prb.post_constraint(Unwritable).unwrap();
		assert!(!prb.trace_active());
		assert!(matches!(
			prb.trace_finish(),
			Err(FztError::UnsupportedConstraint { .. })
		));
	}

	impl<E: ReasoningEngine> Constraint<E> for Unwritable {
		fn simplify(
			&mut self,
			_: &mut E::PropagationContext<'_>,
		) -> Result<SimplificationStatus, E::Conflict> {
			Ok(SimplificationStatus::NoFixpoint)
		}

		fn to_solver(&self, _: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
			Ok(())
		}
	}

	impl<E: ReasoningEngine> Propagator<E> for Unwritable {
		fn initialize(&mut self, _: &mut E::InitializationContext<'_>) {}

		fn propagate(&mut self, _: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
			Ok(())
		}
	}
}
