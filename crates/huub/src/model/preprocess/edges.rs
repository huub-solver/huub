//! The logging of changes to the edges of the difference logic graph.
//!
//! The graph is a single constraint of the [`Model`], but its edges are what
//! the checker knows as constraints: each edge has a trace identifier of its
//! own, and the changes that the graph makes to its edges are logged as steps
//! on those identifiers. The shortest paths through the unconditional edges
//! justify them (see [`PreprocessRule::Dl`]), so the steps do not refer to the
//! paths.

use std::{any::Any, mem};

use crate::{
	constraints::{Constraint, difference_logic::DifferenceLogicModel},
	model::{
		ConstraintId, Model,
		preprocess::{
			fzt::{FztConstraint, FztContext, FztError},
			normalize::lin_norm_equal,
			registry,
			rule::{PreprocessRule, StepKind},
			state::{Event, Output, Window, WindowKind, hint_text},
		},
	},
};

/// The rule that justifies the replacement of a constraint by the edges
/// posted in the window `w`, if they are its two parts.
pub(super) fn split_rule(w: &Window) -> Option<PreprocessRule> {
	match w.split {
		Some(rule) if w.posted_edges.len() == 2 && w.posted.is_empty() => Some(rule),
		_ => None,
	}
}

/// Whether `c` is the constraint that holds the difference logic graph.
pub(super) fn is_difference_logic(c: &dyn Constraint<Model>) -> bool {
	let any: &dyn Any = c;
	any.is::<DifferenceLogicModel>()
}

impl Model {
	/// Log that the edge `edge` of the difference logic graph was created,
	/// where `item` is its representation in the `.fzt` model language.
	///
	/// During a window, the edge is part of what the window logs when it
	/// closes.
	pub(crate) fn trace_dl_edge(&mut self, edge: usize, item: FztConstraint) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		match t.windows.last().map(|w| &w.kind) {
			Some(WindowKind::FznPosting) => {
				self.trace_flush();
				let t = self.trace.recording_mut().unwrap();
				let id = t.fresh_id();
				t.set_edge(edge, Some(id));
				let output = Output::Edge(edge);
				let w = t.windows.last_mut().unwrap();
				w.events.push(Event::Introduced { id, output, item });
			}
			Some(_) => t
				.windows
				.last_mut()
				.unwrap()
				.posted_edges
				.push((edge, item)),
			None => {
				self.trace_flush();
				let t = self.trace.recording_mut().unwrap();
				let id = t.fresh_id();
				t.set_edge(edge, Some(id));
				let text = format!("add #{id} by preserve\n  constraint {item} :: trace_id({id});");
				self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
			}
		}
	}

	/// Log that the edge `edge` of the difference logic graph left the model,
	/// where `before` is its representation, and `gated` whether it has a
	/// condition.
	///
	/// An edge that is not gated is entailed by the other unconditional edges
	/// and the domains, unless it was replaced by the constraints that were
	/// posted in the window since the last removal.
	pub(crate) fn trace_dl_removed(&mut self, edge: usize, before: &FztConstraint, gated: bool) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		let Some(id) = t.dl_edges.get(edge).copied().flatten() else {
			return;
		};
		t.dl_edges[edge] = None;
		let pending = t
			.windows
			.last_mut()
			.map(|w| mem::take(&mut w.posted))
			.unwrap_or_default();
		self.trace_flush();
		let mut outputs = Vec::with_capacity(pending.len());
		for con in pending {
			let Some(c) = self.constraints[con.index()].as_deref() else {
				continue;
			};
			match registry::to_fzt(c, &FztContext::new(self)) {
				Ok(item) => outputs.push((Output::Constraint(con), item)),
				Err(err) => {
					self.trace = crate::model::preprocess::TraceState::Failed(err);
					return;
				}
			}
		}
		let rule = match outputs.as_slice() {
			[] if gated => PreprocessRule::LinValid,
			[] => PreprocessRule::Dl,
			[(_, after)] if lin_norm_equal(before, after) == Some(true) => PreprocessRule::LinNorm,
			_ => PreprocessRule::Preserve,
		};
		self.trace_replace(Some(id), outputs, rule);
	}

	/// Log that the gated edge `edge` is removed because the constraint `item`,
	/// which is its condition-free version, is entailed by the other
	/// unconditional edges.
	pub(crate) fn trace_dl_weaken(&mut self, edge: usize, item: FztConstraint) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		let Some(id) = t.dl_edges.get(edge).copied().flatten() else {
			return;
		};
		t.dl_edges[edge] = None;
		let fresh = t.fresh_id();
		self.trace_flush();
		let text = format!("add #{fresh} by dl\n  constraint {item} :: trace_id({fresh});");
		self.trace_emit(StepKind::Add, Some(PreprocessRule::Dl), text);
		let text = format!("del #{id} by imp-weaken hint #{fresh}");
		self.trace_emit(StepKind::Del, Some(PreprocessRule::ImpWeaken), text);
		let text = format!("del #{fresh} by dl");
		self.trace_emit(StepKind::Del, Some(PreprocessRule::Dl), text);
	}

	/// Log that the condition of the gated edge `edge` is about to be falsified
	/// because the constraint `item`, the negation of the edge, is entailed by
	/// the unconditional edges, returning the identifier of that constraint.
	///
	/// The next domain change of a Boolean decision is the falsification, and
	/// must be followed by [`Self::trace_dl_falsify_close`].
	pub(crate) fn trace_dl_falsify_open(
		&mut self,
		edge: usize,
		item: FztConstraint,
	) -> Option<u32> {
		let t = self.trace.recording_mut()?;
		let id = t.dl_edges.get(edge).copied().flatten()?;
		let fresh = t.fresh_id();
		t.forced = Some((PreprocessRule::ImpContra, vec![id, fresh]));
		self.trace_flush();
		let text = format!("add #{fresh} by dl\n  constraint {item} :: trace_id({fresh});");
		self.trace_emit(StepKind::Add, Some(PreprocessRule::Dl), text);
		Some(fresh)
	}

	/// Log the removal of the gated edge `edge` and of the negation `negation`
	/// (see [`Self::trace_dl_falsify_open`]), once its condition has been
	/// falsified, unless the falsification ended in a conflict.
	pub(crate) fn trace_dl_falsify_close(
		&mut self,
		edge: usize,
		negation: Option<u32>,
		falsified: bool,
	) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		t.forced = None;
		let (Some(negation), true) = (negation, falsified) else {
			return;
		};
		let Some(id) = t.dl_edges.get(edge).copied().flatten() else {
			return;
		};
		t.dl_edges[edge] = None;
		let text = format!("del #{id} by lin-valid");
		self.trace_emit(StepKind::Del, Some(PreprocessRule::LinValid), text);
		let text = format!("del #{negation} by dl");
		self.trace_emit(StepKind::Del, Some(PreprocessRule::Dl), text);
	}

	/// Log that the edges `edges` were replaced by the constraints posted in
	/// the window since the last removal, which together encode them.
	pub(crate) fn trace_dl_dissolved(&mut self, edges: &[usize]) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		let ids: Vec<u32> = edges
			.iter()
			.filter_map(|&e| t.dl_edges.get(e).copied().flatten())
			.collect();
		for &e in edges {
			if e < t.dl_edges.len() {
				t.dl_edges[e] = None;
			}
		}
		let pending = t
			.windows
			.last_mut()
			.map(|w| mem::take(&mut w.posted))
			.unwrap_or_default();
		self.trace_flush();
		let hint = hint_text(&ids);
		let mut added = Vec::with_capacity(pending.len());
		for con in pending {
			let Some(c) = self.constraints[con.index()].as_deref() else {
				continue;
			};
			let item = match registry::to_fzt(c, &FztContext::new(self)) {
				Ok(item) => item,
				Err(err) => {
					self.trace = crate::model::preprocess::TraceState::Failed(err);
					return;
				}
			};
			let t = self.trace.recording_mut().unwrap();
			let id = t.fresh_id();
			t.record_output(id, Output::Constraint(con));
			added.push(id);
			let text =
				format!("add #{id} by preserve{hint}\n  constraint {item} :: trace_id({id});");
			self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
		}
		let hint = hint_text(&added);
		for id in ids {
			let text = format!("del #{id} by preserve{hint}");
			self.trace_emit(StepKind::Del, Some(PreprocessRule::Preserve), text);
		}
	}

	/// Record that the edges that are created next in the current window are
	/// the two parts of one constraint, whose replacement `rule` justifies.
	pub(crate) fn trace_dl_split(&mut self, rule: PreprocessRule) {
		if let Some(w) = self
			.trace
			.recording_mut()
			.and_then(|t| t.windows.last_mut())
		{
			w.split = Some(rule);
		}
	}

	/// The trace identifier of the constraint `con`, if it has one.
	pub(crate) fn trace_origin(&self, con: ConstraintId) -> Option<u32> {
		self.trace
			.recording()?
			.origin
			.get(con.index())
			.copied()
			.flatten()
	}

	/// Open a window around the conversion of a constraint into edges of the
	/// difference logic graph, where `replaces` is the trace identifier of the
	/// constraint that is converted.
	pub(crate) fn trace_dl_open(&mut self, replaces: Option<u32>) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		t.windows.push(Window {
			kind: WindowKind::DifferenceLogicPosting(replaces),
			hint: replaces,
			rule: PreprocessRule::Preserve,
			posted: Vec::new(),
			posted_edges: Vec::new(),
			events: Vec::new(),
			first_id: 0,
			split: None,
		});
	}

	/// Close the window opened by [`Self::trace_dl_open`], logging what became
	/// of the constraint that was converted.
	pub(crate) fn trace_dl_close(&mut self) -> Result<(), FztError> {
		let Some(t) = self.trace.recording_mut() else {
			return Ok(());
		};
		let w = t.windows.pop().expect("window was not opened");
		let WindowKind::DifferenceLogicPosting(replaces) = w.kind else {
			unreachable!("closing a window that is not a conversion into edges")
		};
		let split = split_rule(&w);
		self.trace_flush();
		// A constraint that became a single edge keeps its identifier: the edge
		// is the constraint, up to the normal form of its representation.
		if let (Some(id), [(edge, _)], []) =
			(replaces, w.posted_edges.as_slice(), w.posted.as_slice())
		{
			self.trace
				.recording_mut()
				.unwrap()
				.set_edge(*edge, Some(id));
			return Ok(());
		}
		let mut outputs = Vec::with_capacity(w.posted.len() + w.posted_edges.len());
		for &con in &w.posted {
			let Some(c) = self.constraints[con.index()].as_deref() else {
				continue;
			};
			let item = registry::to_fzt(c, &FztContext::new(self))?;
			outputs.push((Output::Constraint(con), item));
		}
		for (edge, item) in w.posted_edges {
			outputs.push((Output::Edge(edge), item));
		}
		self.trace_replace(replaces, outputs, split.unwrap_or(PreprocessRule::Preserve));
		Ok(())
	}

	/// Log the replacement of the constraint with trace identifier `old`, if
	/// any, by `outputs`, or their addition if there is no such constraint.
	pub(super) fn trace_replace(
		&mut self,
		old: Option<u32>,
		outputs: Vec<(Output, FztConstraint)>,
		rule: PreprocessRule,
	) {
		let t = self.trace.recording_mut().unwrap();
		let mut ids = Vec::with_capacity(outputs.len());
		let mut items = String::new();
		for (out, item) in outputs {
			let id = t.fresh_id();
			t.record_output(id, out);
			ids.push(id);
			items.push_str(&format!("\n  constraint {item} :: trace_id({id});"));
		}
		match old {
			None => {
				for (id, item) in ids.iter().zip(items.split("\n  ").skip(1)) {
					let text = format!("add #{id} by preserve\n  {item}");
					self.trace_emit(StepKind::Add, Some(PreprocessRule::Preserve), text);
				}
			}
			Some(old) if ids.is_empty() => {
				let rule = if rule.fits(StepKind::Del) {
					rule
				} else {
					PreprocessRule::LinValid
				};
				let text = format!("del #{old} by {}", rule.as_str());
				self.trace_emit(StepKind::Del, Some(rule), text);
			}
			Some(old) => {
				let list: Vec<_> = ids.iter().map(|id| format!("#{id}")).collect();
				let text = format!(
					"rewrite #{old} => {} by {}{items}",
					list.join(" "),
					rule.as_str()
				);
				self.trace_emit(StepKind::Rewrite, Some(rule), text);
			}
		}
	}

	/// Open the window of the simplification of the difference logic graph.
	pub(super) fn trace_dl_simplify_open(&mut self) {
		self.trace_flush();
		self.trace.recording_mut().unwrap().windows.push(Window {
			kind: WindowKind::DifferenceLogic,
			hint: None,
			rule: PreprocessRule::Dl,
			posted: Vec::new(),
			posted_edges: Vec::new(),
			events: Vec::new(),
			first_id: 0,
			split: None,
		});
		self.trace.recording_mut().unwrap().simplifying += 1;
	}

	/// Close the window of the simplification of the difference logic graph,
	/// which ended in a conflict if `conflict`.
	pub(super) fn trace_dl_simplify_close(&mut self, conflict: bool) -> Result<(), FztError> {
		let w = self
			.trace
			.recording_mut()
			.unwrap()
			.windows
			.pop()
			.expect("window was not opened");
		self.trace.recording_mut().unwrap().suppressed = None;
		self.trace_flush();
		if conflict {
			self.trace_emit(
				StepKind::Unsat,
				Some(PreprocessRule::Dl),
				"unsat by dl".to_owned(),
			);
			return Ok(());
		}
		let mut outputs = Vec::new();
		for &con in &w.posted {
			let Some(c) = self.constraints[con.index()].as_deref() else {
				continue;
			};
			let item = registry::to_fzt(c, &FztContext::new(self))?;
			outputs.push((Output::Constraint(con), item));
		}
		for (edge, item) in w.posted_edges {
			outputs.push((Output::Edge(edge), item));
		}
		self.trace_replace(None, outputs, PreprocessRule::Preserve);
		Ok(())
	}
}
