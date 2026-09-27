//! The logging of changes to the decisions of the model: domain changes,
//! fixings, unifications, and the names of decisions.

use crate::{
	IntSet, IntVal,
	model::{
		Decision, Model, View,
		decision::integer::Domain,
		deserialize::AnyView,
		preprocess::{
			fzt::{DeclaredDomain, FztContext, fzt_domain},
			rule::{PreprocessRule, StepKind},
			state::{Fixed, Kept, hint_text},
		},
		view::{boolean::BoolView, integer::IntView},
	},
};

/// The domain line of a unification step.
#[derive(Clone, Debug)]
pub(super) enum DomLine {
	/// The domain of the decision in the term, which is written as it is when
	/// the step is logged.
	Of(Fixed),
	/// A domain line that has already been written.
	Text(String),
	/// The domain of the term's decision does not change.
	Unchanged,
}

/// A view that replaces a decision in a unification step, rendered before the
/// unification.
#[derive(Clone, Debug)]
pub(crate) struct UnifyTarget {
	/// The view as a term.
	pub(super) term: String,
	/// The domain line of the step.
	pub(super) dom: DomLine,
}

/// The rule that justifies the replacement of a Boolean decision by `target`
/// (resolved), given that the rule of the window is `rule`.
pub(super) fn bool_unify_rule(rule: PreprocessRule, target: View<bool>) -> PreprocessRule {
	match (rule, target.0) {
		// `lin-affine` allows the justifying equation to be scaled, `lin-neg`
		// does not, so a scaled equation only justifies the positive case.
		(PreprocessRule::LinAffine, BoolView::Decision(l)) if !l.is_negated() => rule,
		(PreprocessRule::LinNeg, BoolView::Decision(l)) if l.is_negated() => rule,
		(
			PreprocessRule::LinLit,
			BoolView::IntEq(..)
			| BoolView::IntNotEq(..)
			| BoolView::IntGreaterEq(..)
			| BoolView::IntLess(..),
		) => rule,
		_ => PreprocessRule::Preserve,
	}
}

/// The domain with which a FlatZinc variable of the given declared domain is
/// kept when it is the objective.
pub(super) fn declared_keep_domain(domain: &DeclaredDomain) -> Option<IntSet> {
	match domain {
		DeclaredDomain::Int(d) => d.clone(),
		DeclaredDomain::Bool => Some((0..=1).into()),
	}
}

impl Model {
	/// Log that the Boolean decision `var` has become fixed.
	pub(crate) fn trace_bool_fixed(&mut self, var: Decision<bool>) {
		if !self.trace_active() {
			return;
		}
		let var = var.var();
		if let Some(fixed) = &mut self.trace.recording_mut().unwrap().suppressed {
			fixed.push(Fixed::Bool(var));
			return;
		}
		self.trace_flush();
		let t = self.trace.recording().unwrap();
		let (rule, hints) = t.justification(StepKind::Dom, |r| r);
		let ctx = FztContext::new(self);
		let name = ctx.bool_name(var);
		let Some(View(BoolView::Const(val))) = self.bool_vars[var.idx()].alias else {
			unreachable!("logged fixing of a Boolean decision that is not fixed")
		};
		let text = format!(
			"dom {name} <- {{{}}} by {}{}",
			val as u8,
			rule.as_str(),
			hint_text(&hints)
		);
		self.trace_emit(StepKind::Dom, Some(rule), text);
		self.trace_bool_singleton(var);
	}
	/// Log the replacement of the fixed Boolean decision `var` by its value.
	pub(super) fn trace_bool_singleton(&mut self, var: Decision<bool>) {
		let ctx = FztContext::new(self);
		let name = ctx.bool_name(var);
		let Some(View(BoolView::Const(val))) = self.bool_vars[var.idx()].alias else {
			unreachable!()
		};
		let text = format!("unify {name} := {val} by singleton");
		self.trace_emit(StepKind::Unify, Some(PreprocessRule::Singleton), text);
	}
	/// Log that the literal `lit` has been unified with (and its decision is
	/// now an alias of) another view.
	pub(crate) fn trace_bool_unified(&mut self, lit: Decision<bool>) {
		if !self.trace_active() {
			return;
		}
		let var = lit.var();
		let alias = self.bool_vars[var.idx()]
			.alias
			.expect("logged unification of a Boolean decision that is not aliased");
		let ctx = FztContext::new(self);
		let name = ctx.bool_name(var);
		let resolved = ctx.resolve_bool(alias);
		let term = ctx.bool_term(alias);
		let t = self.trace.recording().unwrap();
		let (rule, hints) = t.justification(StepKind::Unify, |r| bool_unify_rule(r, resolved));
		let text = format!(
			"unify {name} := {term} by {}{}",
			rule.as_str(),
			hint_text(&hints)
		);
		self.trace_emit(StepKind::Unify, Some(rule), text);
	}
	/// Log that the integer decision `var` has changed its domain.
	pub(crate) fn trace_int_changed(&mut self, var: Decision<IntVal>) {
		if !self.trace_active() {
			return;
		}
		let fixed = match &self.int_vars[var.idx()].domain {
			Domain::Domain(_) => None,
			Domain::Alias(View(IntView::Const(k))) => Some(*k),
			Domain::Alias(_) => unreachable!("logged domain change of an unified decision"),
		};
		if let Some(list) = &mut self.trace.recording_mut().unwrap().suppressed {
			if fixed.is_some() {
				list.push(Fixed::Int(var));
			}
			return;
		}
		self.trace_flush();
		let t = self.trace.recording().unwrap();
		let (rule, hints) = t.justification(StepKind::Dom, |r| r);
		let ctx = FztContext::new(self);
		let domain = match fixed {
			None => {
				let Domain::Domain(d) = &self.int_vars[var.idx()].domain else {
					unreachable!()
				};
				fzt_domain(d)
			}
			Some(k) => format!("{{{k}}}"),
		};
		let text = format!(
			"dom {} <- {domain} by {}{}",
			ctx.int_name(var),
			rule.as_str(),
			hint_text(&hints)
		);
		self.trace_emit(StepKind::Dom, Some(rule), text);
		if let Some(k) = fixed {
			self.trace_int_singleton(var, k);
		}
	}
	/// Resume logging domain changes after the domain of the integer decision
	/// `var` was restricted, logging the change only if it fixed `var`.
	///
	/// The first step of a unification restricts the domain of the decision
	/// that is replaced, which only matters to the trace if it fixes the
	/// decision: otherwise the decision is replaced right after.
	pub(crate) fn trace_int_fixed_suppressed(&mut self, var: Decision<IntVal>) {
		if !self.trace_active() {
			return;
		}
		let t = self.trace.recording_mut().unwrap();
		t.suppressed = None;
		if let Domain::Alias(View(IntView::Const(_))) = self.int_vars[var.idx()].domain {
			self.trace_int_changed(var);
		}
	}
	/// Log the replacement of the fixed integer decision `var` by its value
	/// `k`.
	pub(super) fn trace_int_singleton(&mut self, var: Decision<IntVal>, k: IntVal) {
		let name = FztContext::new(self).int_name(var).into_owned();
		let keep = self.trace_keep(&name, Some((k..=k).into()));
		let text = format!("unify {name} := {k}{keep} by singleton");
		self.trace_emit(StepKind::Unify, Some(PreprocessRule::Singleton), text);
	}
	/// Log that the integer decision `var`, whose domain was `domain`, has been
	/// replaced by `target` (a view rendered by [`Self::trace_unify_target`]
	/// before the unification).
	pub(crate) fn trace_int_unified(
		&mut self,
		var: Decision<IntVal>,
		target: UnifyTarget,
		view: View<IntVal>,
		domain: &IntSet,
	) {
		if !self.trace_active() {
			return;
		}
		let name = FztContext::new(self).int_name(var).into_owned();
		let t = self.trace.recording().unwrap();
		let justification = t.justification(StepKind::Unify, |r| match (r, view.0) {
			(PreprocessRule::LinAffine, IntView::Linear(_) | IntView::Bool(_)) => r,
			_ => PreprocessRule::Preserve,
		});
		self.trace_unify(&name, Some(domain.clone()), target, justification);
	}
	/// Return the ` keep #n` annotation of a unification step that replaces
	/// the variable `name`, which is required when `name` is the objective
	/// variable. The objective is kept with the given domain.
	pub(super) fn trace_keep(&mut self, name: &str, domain: Option<IntSet>) -> String {
		let t = self.trace.recording_mut().unwrap();
		if t.kept.is_none() && t.objective.as_deref() == Some(name) {
			let id = t.fresh_id();
			t.kept = Some(Kept { id, domain });
			format!(" keep #{id}")
		} else {
			String::new()
		}
	}
	/// Give the Boolean decision `var` the FlatZinc name `name`.
	///
	/// This must happen right after the decision is created, before any
	/// other step is logged.
	pub(crate) fn trace_name_bool(&mut self, var: Decision<bool>, name: &str) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		let idx = var.idx();
		if t.bool_names.len() <= idx {
			t.bool_names.resize(idx + 1, None);
		}
		t.bool_names[idx] = Some(name.to_owned());
	}
	/// Give the integer decision `var` the FlatZinc name `name`.
	///
	/// This must happen right after the decision is created, before any
	/// other step is logged.
	pub(crate) fn trace_name_int(&mut self, var: Decision<IntVal>, name: &str) {
		let Some(t) = self.trace.recording_mut() else {
			return;
		};
		let idx = var.idx();
		if t.int_names.len() <= idx {
			t.int_names.resize(idx + 1, None);
		}
		t.int_names[idx] = Some(name.to_owned());
	}
	/// Log the replacement of the FlatZinc variable `name` in a group of
	/// FlatZinc variables that are equal, before their decision is created.
	///
	/// `dom` is the domain of the variable that replaces it after the
	/// replacement, if it changes.
	pub(crate) fn trace_name_merged(
		&mut self,
		name: &str,
		domain: &DeclaredDomain,
		term: String,
		dom: Option<(String, String)>,
		justification: (PreprocessRule, Vec<u32>),
	) {
		if !self.trace_active() {
			return;
		}
		let target = UnifyTarget {
			term,
			dom: match dom {
				Some((var, d)) => DomLine::Text(format!("dom {var} <- {d}")),
				None => DomLine::Unchanged,
			},
		};
		self.trace_unify(name, declared_keep_domain(domain), target, justification);
	}
	/// Log the replacement of the FlatZinc variable `name`, with declared
	/// domain `domain`, by the constant `k`, which happens when its declared
	/// domain is `{k}`.
	pub(crate) fn trace_name_singleton(&mut self, name: &str, domain: &DeclaredDomain, k: IntVal) {
		if !self.trace_active() {
			return;
		}
		let target = UnifyTarget {
			term: k.to_string(),
			dom: DomLine::Unchanged,
		};
		self.trace_unify(
			name,
			declared_keep_domain(domain),
			target,
			(PreprocessRule::Singleton, Vec::new()),
		);
	}
	/// Log the replacement of the FlatZinc variable `name`, with declared
	/// domain `domain` and without a decision of its own, by the view `view`
	/// (rendered by [`Self::trace_unify_target`] before the replacement).
	///
	/// The replacement is justified by the rule of the current window, if it
	/// fits the shape of the view.
	pub(crate) fn trace_name_unified(
		&mut self,
		name: &str,
		domain: &DeclaredDomain,
		target: UnifyTarget,
		view: AnyView,
	) {
		if !self.trace_active() {
			return;
		}
		let ctx = FztContext::new(self);
		let justification = self
			.trace
			.recording()
			.unwrap()
			.justification(StepKind::Unify, |r| match view {
				AnyView::Int(v) => match (r, v.0) {
					(PreprocessRule::LinAffine, IntView::Linear(_) | IntView::Bool(_)) => r,
					_ => PreprocessRule::Preserve,
				},
				AnyView::Bool(b) => bool_unify_rule(r, ctx.resolve_bool(b)),
			});
		self.trace_unify(name, declared_keep_domain(domain), target, justification);
	}
	/// Log the unification steps for the decisions that became fixed while
	/// domain changes were not logged.
	pub(super) fn trace_singletons(&mut self, fixed: Vec<Fixed>) {
		for f in fixed {
			match f {
				Fixed::Bool(var) => self.trace_bool_singleton(var),
				Fixed::Int(var) => {
					let Domain::Alias(View(IntView::Const(k))) = self.int_vars[var.idx()].domain
					else {
						unreachable!()
					};
					self.trace_int_singleton(var, k);
				}
			}
		}
	}
	/// Log the replacement of the variable `name` by `target`, justified by
	/// `justification`, and the replacement of the decisions that became fixed
	/// while domain changes were not logged.
	///
	/// When `name` is the objective variable, it is kept with the domain
	/// `keep_domain`.
	pub(super) fn trace_unify(
		&mut self,
		name: &str,
		keep_domain: Option<IntSet>,
		target: UnifyTarget,
		justification: (PreprocessRule, Vec<u32>),
	) {
		let fixed = self
			.trace
			.recording_mut()
			.unwrap()
			.suppressed
			.take()
			.unwrap_or_default();
		self.trace_flush();
		let keep = self.trace_keep(name, keep_domain);
		let ctx = FztContext::new(self);
		let dom = match target.dom {
			DomLine::Of(Fixed::Int(y)) => {
				let d = match &self.int_vars[y.idx()].domain {
					Domain::Domain(d) => fzt_domain(d),
					Domain::Alias(View(IntView::Const(k))) => format!("{{{k}}}"),
					Domain::Alias(_) => unreachable!("the decision in the term was unified"),
				};
				format!("\n  dom {} <- {d}", ctx.int_name(y))
			}
			DomLine::Of(Fixed::Bool(b)) => match self.bool_vars[b.idx()].alias {
				None => String::new(),
				Some(View(BoolView::Const(v))) => {
					format!("\n  dom {} <- {{{}}}", ctx.bool_name(b), v as u8)
				}
				Some(_) => unreachable!("the decision in the term was unified"),
			},
			DomLine::Text(text) => format!("\n  {text}"),
			DomLine::Unchanged => String::new(),
		};
		let (rule, hints) = justification;
		let text = format!(
			"unify {name} := {}{keep} by {}{}{dom}",
			target.term,
			rule.as_str(),
			hint_text(&hints)
		);
		self.trace_emit(StepKind::Unify, Some(rule), text);
		self.trace_singletons(fixed);
	}
	/// Render the view `view`, which is about to replace a decision, as the
	/// target of a unification step.
	///
	/// This must happen before the domain of the view is restricted, since a
	/// restriction may fix the decision in the view, after which it is no
	/// longer part of the term.
	pub(crate) fn trace_unify_target(&self, view: AnyView) -> UnifyTarget {
		let ctx = FztContext::new(self);
		let lit_base = |b: View<bool>| match ctx.resolve_bool(b).0 {
			BoolView::Decision(l) => DomLine::Of(Fixed::Bool(l.var())),
			BoolView::IntEq(x, _)
			| BoolView::IntNotEq(x, _)
			| BoolView::IntGreaterEq(x, _)
			| BoolView::IntLess(x, _) => DomLine::Of(Fixed::Int(x)),
			BoolView::Const(_) => DomLine::Unchanged,
		};
		match view {
			AnyView::Int(v) => {
				let resolved = ctx.resolve_int(v);
				UnifyTarget {
					term: ctx.int_term(resolved),
					dom: match resolved.0 {
						IntView::Linear(lin) => DomLine::Of(Fixed::Int(lin.var)),
						IntView::Bool(lin) => lit_base(lin.var),
						IntView::Const(_) => DomLine::Unchanged,
					},
				}
			}
			AnyView::Bool(b) => UnifyTarget {
				term: ctx.bool_term(b),
				dom: lit_base(b),
			},
		}
	}
}
