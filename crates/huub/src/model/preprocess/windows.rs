//! The logging of changes to the constraints of the model, in windows around
//! the posting of FlatZinc constraints and the simplification of constraints.

use std::fmt::Write;

use crate::{
	constraints::{Constraint, SimplificationStatus},
	model::{
		ConstraintId, Model, View,
		preprocess::{
			edges::{is_difference_logic, split_rule},
			fzt::{FztConstraint, FztContext, FztError},
			normalize::lin_norm_equal,
			registry,
			rule::{PreprocessRule, StepKind},
			spelling,
			state::{Event, FznOutcome, Output, Window, WindowKind, hint_text},
		},
	},
};

impl Model {
	/// Record that search assumes the literals `lits` to hold, as stated by
	/// the `huub_assume` constraint being posted.
	pub(crate) fn trace_assume(&mut self, lits: Vec<View<bool>>) {
		if !self.trace_active() || !self.trace_posting() {
			return;
		}
		self.trace_flush();
		let item = FztConstraint::new(
			spelling::ASSUME,
			vec![FztContext::new(self).bools(lits.iter().copied())],
		);
		let t = self.trace.recording_mut().unwrap();
		let id = t.fresh_id();
		let output = Output::Assumption(lits);
		t.record_output(id, output.clone());
		let w = t.windows.last_mut().unwrap();
		w.events.push(Event::Introduced { id, output, item });
	}
	/// Whether the innermost window is the posting of a FlatZinc constraint.
	fn trace_posting(&self) -> bool {
		self.trace
			.recording()
			.and_then(|t| t.windows.last())
			.is_some_and(|w| matches!(w.kind, WindowKind::FznPosting))
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
		// The difference logic graph is not a constraint of the trace: its
		// edges are.
		if self.constraints[con.index()]
			.as_deref()
			.is_some_and(is_difference_logic)
		{
			return Ok(());
		}
		if self.trace_posting() {
			// The constraint is introduced now, so that the steps of its
			// simplification, which follows at once, can refer to it.
			self.trace_flush();
			let (id, _, item) = self.trace_constraint_item(con, None)?;
			let output = Output::Constraint(con);
			let t = self.trace.recording_mut().unwrap();
			let w = t.windows.last_mut().unwrap();
			w.events.push(Event::Introduced { id, output, item });
			return Ok(());
		}
		let t = self.trace.recording_mut().unwrap();
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
	/// Close the window of the extraction of a view from, or the posting of,
	/// the FlatZinc constraint with trace identifier `fzn`, logging what
	/// became of the constraint.
	///
	/// For a posting, `rewrite_rule` justifies the replacement of the FlatZinc
	/// constraint by the constraints that were posted for it, given their
	/// `.fzt` representations; `del_rule` justifies its removal when nothing
	/// was posted.
	///
	/// # How the steps are ordered
	///
	/// A constraint is simplified as soon as it is posted, exactly as it is
	/// when no trace is recorded, so the steps of its simplification happen
	/// before the posting of the FlatZinc constraint has finished. They refer
	/// to the constraint that was posted, which the checker only knows once
	/// the FlatZinc constraint has been replaced by what was posted for it,
	/// and the replacement is only complete when the posting has finished.
	///
	/// The steps are therefore kept, and written when the window closes, in an
	/// order that is only different from the order in which they happened if
	/// that does not change what a step means. A step depends on the steps
	/// that happened before it that it may have read the result of:
	///
	/// - a step of the simplification of a constraint depends on the
	///   introduction of that constraint;
	/// - the introduction of a constraint, and any other change that the
	///   posting makes, depends on every step that happened before it, since
	///   the posting reads the state of the model to decide what to post, and
	///   the reads of that code cannot be observed.
	///
	/// The introductions, together with the removal of the FlatZinc constraint
	/// they replace, form one step, so they can only be written together if
	/// the steps between them do not depend on one of them and are not
	/// depended on by another. Given the dependencies above, that is exactly
	/// when no step of a simplification happened before the last change that
	/// the posting makes. Then the steps are written as the posting's own
	/// steps, the replacement of the FlatZinc constraint, and the steps of the
	/// simplifications, which is the order in which a trace is written when the
	/// simplification of a constraint is postponed until the posting has
	/// finished.
	///
	/// Otherwise the steps are written in the order in which they happened, and
	/// the FlatZinc constraint is replaced in stages.
	pub(crate) fn trace_fzn_close(
		&mut self,
		outcome: FznOutcome,
		rewrite_rule: impl FnOnce(&[FztConstraint]) -> PreprocessRule,
		del_rule: PreprocessRule,
	) -> Result<(), FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(());
		};
		let w = t.windows.pop().expect("window was not opened");
		t.suppressed = None;
		debug_assert!(matches!(
			w.kind,
			WindowKind::FznPosting | WindowKind::FznView
		));
		let fzn = w.hint.unwrap();
		self.trace_flush();
		if outcome == FznOutcome::Failed {
			return Ok(());
		}
		let events = w.events;
		let introduced: Vec<_> = events
			.iter()
			.filter_map(|e| match e {
				Event::Introduced { id, output, item } => Some((*id, output.clone(), item.clone())),
				Event::Step { .. } => None,
			})
			.collect();
		// The posting made no change after the last simplification step started
		// if no step of a simplification precedes a change of the posting.
		let last_change = events.iter().rposition(|e| match e {
			Event::Introduced { .. } => true,
			Event::Step { nested, .. } => !nested,
		});
		let interleaved = last_change.is_some_and(|last| {
			events[..last]
				.iter()
				.any(|e| matches!(e, Event::Step { nested: true, .. }))
		});

		let staged = interleaved
			|| matches!(outcome, FznOutcome::Conflict | FznOutcome::Unprocessed)
			// Nothing was introduced, so there is nothing to wait for.
			|| introduced.is_empty();
		if !staged {
			let items: Vec<_> = introduced.iter().map(|(_, _, item)| item.clone()).collect();
			let rule = rewrite_rule(&items);
			let edges = introduced
				.iter()
				.filter(|(_, out, _)| matches!(out, Output::Edge(_)))
				.count();
			let rule = match w.split {
				Some(split) if items.len() == 2 && edges == 2 => split,
				_ if rule.fits(StepKind::Rewrite) => rule,
				_ => PreprocessRule::Preserve,
			};
			for e in &events {
				if let Event::Step {
					kind,
					rule,
					text,
					nested: false,
				} = e
				{
					self.trace_emit_now(*kind, *rule, text.clone());
				}
			}
			let ids: Vec<_> = introduced
				.iter()
				.map(|(id, _, _)| format!("#{id}"))
				.collect();
			let mut cont = String::new();
			for (id, _, item) in &introduced {
				write!(cont, "\n  constraint {item} :: trace_id({id});").unwrap();
			}
			let text = format!(
				"rewrite #{fzn} => {} by {}{cont}",
				ids.join(" "),
				rule.as_str()
			);
			self.trace_emit_now(StepKind::Rewrite, Some(rule), text);
			for e in &events {
				if let Event::Step {
					kind,
					rule,
					text,
					nested: true,
				} = e
				{
					self.trace_emit_now(*kind, *rule, text.clone());
				}
			}
			return Ok(());
		}

		// TODO: the steps below fall back to `preserve`, which the checker can
		// only discharge with a solver. The checker has no form of the
		// `identity`, `lin-norm`, `reif-split`, and `eq-split` rules for a
		// constraint that is replaced in stages, i.e. one `add` per constraint
		// that is posted, justified by the FlatZinc constraint, and a `del` of
		// the FlatZinc constraint that is justified by the constraints that
		// remain. Once it does, justify these steps with the rule that the
		// replacement would have had (see the branch above), where the
		// constraints that were posted still have the form that they had when
		// they were introduced.
		let mut last_unsat = false;
		for e in &events {
			match e {
				Event::Introduced { id, item, .. } => {
					let text = format!(
						"add #{id} by preserve hint #{fzn}\n  constraint {item} :: trace_id({id});"
					);
					self.trace_emit_now(StepKind::Add, Some(PreprocessRule::Preserve), text);
					last_unsat = false;
				}
				Event::Step {
					kind, rule, text, ..
				} => {
					self.trace_emit_now(*kind, *rule, text.clone());
					last_unsat = *kind == StepKind::Unsat;
				}
			}
		}
		match outcome {
			FznOutcome::Conflict => {
				// A simplification that ended in a conflict concluded it
				// itself.
				if !last_unsat {
					let text = format!("unsat by preserve hint #{fzn}");
					self.trace_emit_now(StepKind::Unsat, Some(PreprocessRule::Preserve), text);
				}
			}
			FznOutcome::Processed => {
				if introduced.is_empty() {
					let rule = if del_rule.fits(StepKind::Del) {
						del_rule
					} else {
						PreprocessRule::Preserve
					};
					let text = format!("del #{fzn} by {}", rule.as_str());
					self.trace_emit_now(StepKind::Del, Some(rule), text);
				} else {
					// What is left of what was posted, which implies the
					// FlatZinc constraint together with the domains.
					let live = self.trace_live_since(w.first_id);
					let text = format!("del #{fzn} by preserve{}", hint_text(&live));
					self.trace_emit_now(StepKind::Del, Some(PreprocessRule::Preserve), text);
				}
			}
			// The FlatZinc constraint remains.
			FznOutcome::Failed | FznOutcome::Unprocessed => {}
		}
		Ok(())
	}
	/// The trace identifiers, from `first` on, of the constraints and
	/// assumptions that are part of the model.
	fn trace_live_since(&self, first: u32) -> Vec<u32> {
		let t = self.trace.recording().unwrap();
		let mut live: Vec<u32> = self
			.constraints
			.iter()
			.enumerate()
			.filter(|(_, c)| c.is_some())
			.filter_map(|(i, _)| t.origin.get(i).copied().flatten())
			.chain(t.dl_edges.iter().copied().flatten())
			.chain(t.assumptions.iter().map(|(id, _)| *id))
			.filter(|&id| id >= first)
			.collect();
		live.sort_unstable();
		live.dedup();
		live
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
			posted_edges: Vec::new(),
			events: Vec::new(),
			first_id: t.next_id,
			split: None,
		});
	}
	/// Close the window of the simplification of a constraint, which ended with
	/// `status` (or a conflict), logging what became of the constraint.
	pub(crate) fn trace_simplify_close(
		&mut self,
		obj: &dyn Constraint<Model>,
		status: Result<SimplificationStatus, ()>,
	) -> Result<(), FztError> {
		let result = self.trace_simplify_close_steps(obj, status);
		if let Some(t) = self.trace.recording_mut() {
			t.simplifying -= 1;
		}
		result
	}
	/// Log what became of the constraint whose simplification ended.
	fn trace_simplify_close_steps(
		&mut self,
		obj: &dyn Constraint<Model>,
		status: Result<SimplificationStatus, ()>,
	) -> Result<(), FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(());
		};
		let w = t.windows.pop().expect("window was not opened");
		t.suppressed = None;
		if matches!(w.kind, WindowKind::DifferenceLogic) {
			self.trace.recording_mut().unwrap().windows.push(w);
			return self.trace_dl_simplify_close(status.is_err());
		}
		let split = split_rule(&w);
		let WindowKind::Simplify { con, item: before } = w.kind else {
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
				// A constraint that is only affected by the substitutions of
				// unifications has not changed: the checker performs them
				// itself.
				let ctx = FztContext::new(self);
				let after = registry::to_fzt(obj, &ctx)?;
				let unchanged = ctx.substitute(&before);
				if after != unchanged && lin_norm_equal(&unchanged, &after) != Some(true) {
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
		for (edge, item) in w.posted_edges {
			let t = self.trace.recording_mut().unwrap();
			let id = t.fresh_id();
			t.set_edge(edge, Some(id));
			let text = format!("constraint {item} :: trace_id({id});");
			outputs.push((id, text, item));
		}
		if replaced {
			let kind = if outputs.is_empty() {
				StepKind::Del
			} else {
				StepKind::Rewrite
			};
			let rule = match (w.rule, outputs.as_slice()) {
				(_, [_, _]) if split.is_some() => split.unwrap(),
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
		if is_difference_logic(obj) {
			self.trace_dl_simplify_open();
			return Ok(true);
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
			kind: WindowKind::Simplify { con, item },
			hint: Some(id),
			rule: PreprocessRule::Preserve,
			posted: Vec::new(),
			posted_edges: Vec::new(),
			events: Vec::new(),
			first_id: 0,
			split: None,
		});
		self.trace.recording_mut().unwrap().simplifying += 1;
		Ok(true)
	}
}

#[cfg(test)]
mod tests {
	use std::sync::{Arc, Mutex};

	use crate::{
		DeepClone,
		actions::ReasoningEngine,
		constraints::{Constraint, Propagator, SimplificationStatus},
		lower::{LoweringContext, LoweringError},
		model::{
			Model,
			preprocess::{FztError, PreprocessEvent, PreprocessSink},
		},
	};

	/// A sink that drops everything it receives.
	#[derive(Debug)]
	struct Discard;

	impl PreprocessSink for Discard {
		fn event(&mut self, _: PreprocessEvent) {}
	}

	/// A constraint without a representation in the `.fzt` model language.
	#[derive(Clone, Debug, DeepClone)]
	struct Unwritable;

	/// A constraint that cannot be written ends the trace, and the error is
	/// returned when the trace is finished.
	#[test]
	fn unwritable_constraint_fails_the_trace() {
		let mut prb = Model::default();
		prb.trace_start(0, None, Arc::new(Mutex::new(Discard)));
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
