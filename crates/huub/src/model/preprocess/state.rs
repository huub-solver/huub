//! The recording state of the preprocessing trace, and the emission of its
//! steps.

use std::{
	mem,
	num::NonZero,
	sync::{Arc, Mutex},
};

use rustc_hash::FxHashMap;

use crate::{
	IntSet, IntVal,
	model::{
		ConstraintId, Decision, Model, View,
		decision::integer::Domain,
		preprocess::{
			fzt::{DeclaredDomain, FztConstraint, FztContext, FztError, fzt_domain},
			rule::{PreprocessRule, StepKind},
			sink::{PreprocessEvent, PreprocessSink},
		},
		view::{boolean::BoolView, integer::IntView},
	},
};

/// A decision that became fixed while domain changes were not logged.
#[derive(Clone, Copy, Debug)]
pub(super) enum Fixed {
	/// A Boolean decision.
	Bool(Decision<bool>),
	/// An integer decision.
	Int(Decision<IntVal>),
}

/// The outcome of posting a FlatZinc constraint or extracting a view from it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FznOutcome {
	/// The constraint was found to be unsatisfiable.
	Conflict,
	/// An error that is not a conclusion about the model occurred.
	Failed,
	/// The constraint has been processed.
	Processed,
	/// The constraint has been left for later processing.
	Unprocessed,
}

/// The objective variable after it has been unified away.
///
/// The objective has to remain a variable, so it is kept in the model with its
/// domain at the time of the unification, together with the defining
/// constraint `o = t`, where `t` is the term that replaced it.
#[derive(Clone, Debug)]
pub(super) struct Kept {
	/// The trace identifier of the defining constraint.
	pub(super) id: u32,
	/// The domain of the objective variable at the unification.
	pub(super) domain: Option<IntSet>,
}

/// A constraint of the model at the start of search that replaces a FlatZinc
/// constraint.
#[derive(Clone, Debug)]
pub(super) enum Output {
	/// An edge of the difference logic graph, by index.
	Edge(usize),
	/// A `huub_assume` constraint over the given literals, which search
	/// enforces as assumptions.
	Assumption(Vec<View<bool>>),
	/// A constraint of the [`Model`].
	Constraint(ConstraintId),
}

/// Recording state of the preprocessing trace, owned by the [`Model`] while a
/// trace is requested.
#[derive(Clone, Debug)]
pub(crate) struct PreprocessTrace {
	/// The receiver of the trace.
	pub(super) sink: Arc<Mutex<dyn PreprocessSink>>,
	/// The number of steps that have been emitted.
	pub(super) steps: u64,
	/// The next fresh trace identifier.
	pub(super) next_id: u32,
	/// The trace identifier of each constraint of the model, indexed by
	/// [`ConstraintId`].
	pub(super) origin: Vec<Option<u32>>,
	/// The trace identifier of each edge of the difference logic graph, indexed
	/// by edge, while the edge is part of the model.
	///
	/// The graph is a single constraint of the model, so its edges are the
	/// constraints that the trace knows.
	pub(super) dl_edges: Vec<Option<u32>>,
	/// The FlatZinc names of the integer decisions.
	pub(super) int_names: Vec<Option<String>>,
	/// The FlatZinc names of the Boolean decisions.
	pub(super) bool_names: Vec<Option<String>>,
	/// The decision that has a FlatZinc name, for each name of an integer
	/// decision.
	pub(super) int_by_name: FxHashMap<String, Decision<IntVal>>,
	/// The decision that has a FlatZinc name, for each name of a Boolean
	/// decision.
	pub(super) bool_by_name: FxHashMap<String, Decision<bool>>,
	/// The number of integer decisions whose introduction has been logged (or
	/// that have a FlatZinc name).
	pub(super) announced_int: usize,
	/// The number of Boolean decisions whose introduction has been logged (or
	/// that have a FlatZinc name).
	pub(super) announced_bool: usize,
	/// The FlatZinc name of the objective variable, if any.
	pub(super) objective: Option<String>,
	/// The objective variable after it was unified away, and kept (see
	/// [`Kept`]).
	pub(super) kept: Option<Kept>,
	/// The literals that search assumes to hold, with the trace identifier of
	/// the `huub_assume` constraint that states them in the model at the start
	/// of search.
	///
	/// Assumptions are not constraints of the [`Model`], but search enforces
	/// them, so the model at the start of search includes them.
	pub(super) assumptions: Vec<(u32, Vec<View<bool>>)>,
	/// FlatZinc variables that do not have a decision in the model, with their
	/// declared domains.
	pub(super) unmaterialized: Vec<(String, DeclaredDomain)>,
	/// The windows in which the steps currently happen, innermost last.
	pub(super) windows: Vec<Window>,
	/// The number of simplifications that are in progress.
	pub(super) simplifying: u32,
	/// While set, domain changes are not logged, since they are part of a
	/// unification step that is logged afterwards. The decisions that become
	/// fixed are collected instead.
	pub(super) suppressed: Option<Vec<Fixed>>,
	/// The justification of the next domain change of a Boolean decision, if
	/// it is not the one of the window.
	pub(super) forced: Option<(PreprocessRule, Vec<u32>)>,
}

/// The state of the preprocessing trace of a [`Model`].
#[derive(Clone, Debug, Default)]
pub(crate) enum TraceState {
	/// The trace could not be completed.
	///
	/// This state is entered where the error cannot be returned to the code
	/// that changed the model (e.g. a domain setter or the simplification of a
	/// constraint), and the error is returned when the trace is finished.
	/// Nothing is logged after it.
	Failed(FztError),
	/// No trace is requested.
	#[default]
	Off,
	/// The trace is being recorded.
	Recording(Box<PreprocessTrace>),
}

/// A window of the preprocessing in which steps happen for a common reason.
#[derive(Clone, Debug)]
pub(super) struct Window {
	/// What happens in the window.
	pub(super) kind: WindowKind,
	/// The constraint that the steps in the window are derived from.
	pub(super) hint: Option<u32>,
	/// The rule that justifies the steps in the window.
	pub(super) rule: PreprocessRule,
	/// The constraints posted during the window.
	pub(super) posted: Vec<ConstraintId>,
	/// The edges of the difference logic graph created during the window, with
	/// their `.fzt` representations.
	pub(super) posted_edges: Vec<(usize, FztConstraint)>,
	/// What happened during the posting of a FlatZinc constraint, in the order
	/// in which it happened (see [`Event`]).
	pub(super) events: Vec<Event>,
	/// The next trace identifier when the window was opened, so that the
	/// constraints that are introduced in the window are those that have a
	/// greater one.
	pub(super) first_id: u32,
	/// The rule that justifies the replacement of a constraint by the edges
	/// created in the window, if they are the two parts of one constraint.
	pub(super) split: Option<PreprocessRule>,
}

/// Something that happened during the posting of a FlatZinc constraint.
///
/// The posting is executed exactly as it is when no trace is recorded, so a
/// constraint is simplified as soon as it is posted, and the steps of that
/// simplification happen before the posting has finished. The events are kept
/// until the window closes, when the steps are written in an order that the
/// checker can replay (see `Model::trace_fzn_close`).
#[derive(Clone, Debug)]
pub(super) enum Event {
	/// A constraint, edge, or assumption was introduced.
	Introduced {
		/// The trace identifier it was given.
		id: u32,
		/// What was introduced.
		output: Output,
		/// Its representation when it was introduced.
		item: FztConstraint,
	},
	/// A step was logged.
	Step {
		/// The kind of the step.
		kind: StepKind,
		/// The rule that justifies the step.
		rule: Option<PreprocessRule>,
		/// The step.
		text: String,
		/// Whether the step is part of the simplification of an introduced
		/// constraint, rather than a change that the posting itself makes.
		nested: bool,
	},
}

/// What happens in a [`Window`].
#[derive(Clone, Debug)]
pub(super) enum WindowKind {
	/// The extraction of a view from a FlatZinc constraint.
	FznView,
	/// The posting of a FlatZinc constraint.
	FznPosting,
	/// The simplification of the difference logic graph, whose steps are
	/// justified by the graph itself.
	DifferenceLogic,
	/// The conversion of a constraint into edges of the difference logic
	/// graph, replacing the constraint with the given trace identifier, if any.
	DifferenceLogicPosting(Option<u32>),
	/// The simplification of a constraint, with its representation before the
	/// simplification.
	Simplify {
		/// The constraint being simplified.
		con: ConstraintId,
		/// The `.fzt` representation of the constraint.
		item: FztConstraint,
	},
}

/// Write a list of trace identifiers as a hint.
pub(super) fn hint_text(hints: &[u32]) -> String {
	if hints.is_empty() {
		String::new()
	} else {
		let ids: Vec<_> = hints.iter().map(|h| format!("#{h}")).collect();
		format!(" hint {}", ids.join(","))
	}
}

impl Model {
	/// Whether a preprocessing trace is being recorded.
	pub(crate) fn trace_active(&self) -> bool {
		self.trace.recording().is_some()
	}
	/// Emit a step of the trace.
	///
	/// During the posting of a FlatZinc constraint, the step is kept until the
	/// window closes.
	pub(super) fn trace_emit(
		&mut self,
		kind: StepKind,
		rule: Option<PreprocessRule>,
		text: String,
	) {
		let t = self.trace.recording_mut().unwrap();
		let nested = t.simplifying > 0;
		if let Some(w) = t
			.windows
			.iter_mut()
			.find(|w| matches!(w.kind, WindowKind::FznPosting))
		{
			w.events.push(Event::Step {
				kind,
				rule,
				text,
				nested,
			});
			return;
		}
		self.trace_emit_now(kind, rule, text);
	}
	/// Emit a step of the trace right away.
	pub(super) fn trace_emit_now(
		&mut self,
		kind: StepKind,
		rule: Option<PreprocessRule>,
		text: String,
	) {
		let t = self.trace.recording_mut().unwrap();
		t.steps += 1;
		let seq = t.steps;
		tracing::trace!(
			target: "preprocess",
			seq,
			kind = kind.as_str(),
			rule = rule.map_or("", PreprocessRule::as_str),
			step = %text,
		);
		t.sink
			.lock()
			.unwrap()
			.event(PreprocessEvent::Step { seq, text });
	}
	/// Signal the end of the trace, returning the first error that prevented
	/// its completion, if any.
	///
	/// Recording stops, so that nothing that happens to the model afterwards
	/// can be mistaken for a step of the trace.
	pub(crate) fn trace_finish(&mut self) -> Result<(), FztError> {
		match mem::take(&mut self.trace) {
			TraceState::Off => Ok(()),
			TraceState::Failed(err) => Err(err),
			TraceState::Recording(t) => {
				let steps = t.steps;
				tracing::trace!(target: "preprocess", end = steps);
				t.sink
					.lock()
					.unwrap()
					.event(PreprocessEvent::EndTrace { steps });
				Ok(())
			}
		}
	}
	/// Log the introduction of the decisions that have been created since the
	/// last call, and that do not represent a FlatZinc variable.
	pub(crate) fn trace_flush(&mut self) {
		let Some(t) = self.trace.recording() else {
			return;
		};
		if t.announced_int == self.int_vars.len() && t.announced_bool == self.bool_vars.len() {
			return;
		}
		let mut steps = Vec::new();
		let ctx = FztContext::new(self);
		for idx in t.announced_int..self.int_vars.len() {
			if matches!(t.int_names.get(idx), Some(Some(_))) {
				continue;
			}
			let domain = match &self.int_vars[idx].domain {
				Domain::Domain(d) => fzt_domain(d),
				Domain::Alias(View(IntView::Const(k))) => format!("{{{k}}}"),
				Domain::Alias(_) => {
					unreachable!("decision was unified before its introduction was logged")
				}
			};
			let name = ctx.int_name(Decision(idx as u32));
			steps.push(format!("add var {name} {domain}"));
		}
		for idx in t.announced_bool..self.bool_vars.len() {
			if matches!(t.bool_names.get(idx), Some(Some(_))) {
				continue;
			}
			let var = Decision(pindakaas::Lit::from_raw(
				NonZero::new(idx as i32 + 1).unwrap(),
			));
			let domain = match self.bool_vars[idx].alias {
				None => "bool".to_owned(),
				Some(View(BoolView::Const(b))) => format!("{{{}}}", b as u8),
				Some(_) => unreachable!("decision was unified before its introduction was logged"),
			};
			let name = ctx.bool_name(var);
			steps.push(format!("add var {name} {domain}"));
		}
		let (int_len, bool_len) = (self.int_vars.len(), self.bool_vars.len());
		let t = self.trace.recording_mut().unwrap();
		t.announced_int = int_len;
		t.announced_bool = bool_len;
		for text in steps {
			self.trace_emit(StepKind::AddVar, None, text);
		}
	}
	/// Emit a raw step, e.g. for the unification of FlatZinc variables before
	/// the creation of their decisions.
	pub(crate) fn trace_raw(&mut self, text: String) {
		if !self.trace_active() {
			return;
		}
		self.trace_flush();
		let kind = match text.split_whitespace().next() {
			Some("unify") => StepKind::Unify,
			Some("dom") => StepKind::Dom,
			Some("del") => StepKind::Del,
			Some("unsat") => StepKind::Unsat,
			_ => unreachable!("unexpected raw step"),
		};
		let rule = text
			.split(" by ")
			.nth(1)
			.and_then(|r| r.split_whitespace().next())
			.and_then(PreprocessRule::from_str);
		self.trace_emit(kind, rule, text);
	}
	/// Set the rule that justifies the next steps in the current window.
	pub(crate) fn trace_rule(&mut self, rule: PreprocessRule) {
		if let Some(w) = self
			.trace
			.recording_mut()
			.and_then(|t| t.windows.last_mut())
		{
			w.rule = rule;
		}
	}
	/// Start recording a preprocessing trace for a FlatZinc instance with
	/// `received` constraints and the objective variable `objective`, which is
	/// delivered to `sink`.
	pub(crate) fn trace_start(
		&mut self,
		received: usize,
		objective: Option<String>,
		sink: Arc<Mutex<dyn PreprocessSink>>,
	) {
		debug_assert!(self.int_vars.is_empty() && self.bool_vars.is_empty());
		self.trace = TraceState::Recording(Box::new(PreprocessTrace {
			sink,
			steps: 0,
			next_id: received as u32 + 1,
			origin: Vec::new(),
			dl_edges: Vec::new(),
			int_names: Vec::new(),
			bool_names: Vec::new(),
			int_by_name: FxHashMap::default(),
			bool_by_name: FxHashMap::default(),
			announced_int: 0,
			announced_bool: 0,
			objective,
			kept: None,
			assumptions: Vec::new(),
			unmaterialized: Vec::new(),
			windows: Vec::new(),
			suppressed: None,
			simplifying: 0,
			forced: None,
		}));
	}
	/// Stop logging domain changes, collecting the decisions that become fixed
	/// instead, until the next unification step is logged.
	pub(crate) fn trace_suppress(&mut self) {
		if self.trace_active() {
			self.trace.recording_mut().unwrap().suppressed = Some(Vec::new());
		}
	}
}

impl PreprocessTrace {
	/// Allocate a fresh trace identifier.
	pub(super) fn fresh_id(&mut self) -> u32 {
		let id = self.next_id;
		self.next_id += 1;
		id
	}

	/// The rule and hint that justify a step of the given kind in the current
	/// window, where `adapt` maps the rule of the window to the rule that fits
	/// the step, or to [`PreprocessRule::Preserve`] if none does.
	pub(super) fn justification(
		&self,
		kind: StepKind,
		adapt: impl FnOnce(PreprocessRule) -> PreprocessRule,
	) -> (PreprocessRule, Vec<u32>) {
		let Some(w) = self.windows.last() else {
			return (PreprocessRule::Preserve, Vec::new());
		};
		let rule = adapt(w.rule);
		if rule != PreprocessRule::Preserve && rule.fits(kind) {
			if !rule.needs_hint() {
				return (rule, Vec::new());
			}
			if let Some(h) = w.hint {
				return (rule, vec![h]);
			}
		}
		(PreprocessRule::Preserve, w.hint.into_iter().collect())
	}

	/// Record that the edge `edge` of the difference logic graph has the trace
	/// identifier `id`, or has left the model.
	pub(super) fn set_edge(&mut self, edge: usize, id: Option<u32>) {
		if self.dl_edges.len() <= edge {
			self.dl_edges.resize(edge + 1, None);
		}
		self.dl_edges[edge] = id;
	}

	/// Record that the constraint `out` has the trace identifier `id`.
	pub(super) fn record_output(&mut self, id: u32, out: Output) {
		match out {
			Output::Assumption(lits) => self.assumptions.push((id, lits)),
			Output::Constraint(con) => self.origin[con.index()] = Some(id),
			Output::Edge(edge) => self.set_edge(edge, Some(id)),
		}
	}
}

impl TraceState {
	/// The recording state, if the trace is being recorded.
	pub(crate) fn recording(&self) -> Option<&PreprocessTrace> {
		match self {
			TraceState::Recording(t) => Some(t),
			TraceState::Failed(_) | TraceState::Off => None,
		}
	}

	/// The recording state, if the trace is being recorded.
	pub(crate) fn recording_mut(&mut self) -> Option<&mut PreprocessTrace> {
		match self {
			TraceState::Recording(t) => Some(t),
			TraceState::Failed(_) | TraceState::Off => None,
		}
	}
}
