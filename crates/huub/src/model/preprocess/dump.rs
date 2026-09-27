//! The emission of the model at the start of search.

use std::{borrow::Cow, num::NonZero};

use crate::{
	IntVal,
	model::{
		Decision, Model, View,
		decision::integer::Domain,
		deserialize::AnyView,
		preprocess::{
			fzt::{DeclaredDomain, FztConstraint, FztContext, FztError, fzt_declared, fzt_domain},
			registry, spelling,
		},
		view::integer::IntView,
	},
};

impl Model {
	/// Emit the model at the start of search on the `start_model` target.
	///
	/// `names` maps each FlatZinc variable with a decision to its view, and
	/// `goal` is the objective of the instance.
	pub(crate) fn trace_start_model<'n>(
		&mut self,
		names: impl IntoIterator<Item = (&'n str, AnyView)>,
		goal: Option<&crate::model::deserialize::Goal<View<IntVal>>>,
	) -> Result<(), FztError> {
		use crate::model::{deserialize::Goal, preprocess::state::TraceState};

		match &self.trace {
			TraceState::Off => return Ok(()),
			TraceState::Failed(err) => return Err(err.clone()),
			TraceState::Recording(_) => {}
		}
		self.trace_flush();
		let t = self.trace.recording().unwrap();
		let ctx = FztContext::new(self);
		let mut items = Vec::new();

		// The decisions that are still part of the model, sorted by name for a
		// reproducible model, since the order in which the decisions are
		// created is not.
		let mut vars = Vec::new();
		for (idx, dcn) in self.int_vars.iter().enumerate() {
			if let Domain::Domain(d) = &dcn.domain {
				let name = ctx.int_name(Decision(idx as u32));
				vars.push((name, fzt_domain(d)));
			}
		}
		for (idx, dcn) in self.bool_vars.iter().enumerate() {
			if dcn.alias.is_none() {
				let var = Decision(pindakaas::Lit::from_raw(
					NonZero::new(idx as i32 + 1).unwrap(),
				));
				vars.push((ctx.bool_name(var), "bool".to_owned()));
			}
		}
		// FlatZinc variables that Huub never created are left unconstrained.
		for (name, domain) in &t.unmaterialized {
			vars.push((Cow::Borrowed(name.as_str()), fzt_declared(domain)));
		}
		vars.sort();
		items.extend(
			vars.into_iter()
				.map(|(name, domain)| format!("var {domain}: {name};")),
		);

		// The objective, and its defining constraint if it has been unified
		// away.
		let objective = match (goal, &t.objective) {
			(None, _) => None,
			(Some(Goal::Minimize(v) | Goal::Maximize(v)), Some(name)) => {
				let dir = match goal.unwrap() {
					Goal::Minimize(_) => "minimize",
					Goal::Maximize(_) => "maximize",
				};
				match &t.kept {
					Some(kept) => {
						let domain = kept
							.domain
							.as_ref()
							.map_or_else(|| "int".to_owned(), fzt_domain);
						items.push(format!("var {domain}: {name};"));
						items.push(format!(
							"constraint int_lin_eq([1, -1], [{name}, {}], 0) :: trace_id({});",
							ctx.int(*v),
							kept.id
						));
					}
					None => match ctx.resolve_int(*v).0 {
						IntView::Linear(lin)
							if lin.scale.get() == 1
								&& lin.offset == 0 && ctx.int_name(lin.var) == name.as_str() => {}
						_ => {
							// The objective variable must be represented by a
							// decision of its own, or have been kept.
							return Err(FztError::UnsupportedObjective);
						}
					},
				}
				Some(format!("solve {dir} {name};"))
			}
			(Some(_), None) => return Err(FztError::UnsupportedObjective),
		};

		// The constraints.
		for (idx, c) in self.constraints.iter().enumerate() {
			let Some(c) = c else { continue };
			let Some(Some(id)) = t.origin.get(idx) else {
				return Err(FztError::UnloggedConstraint);
			};
			let item = registry::to_fzt(&**c, &ctx)?;
			items.push(format!("constraint {item} :: trace_id({id});"));
		}
		// The assumptions, which search enforces although they are not
		// constraints of the model.
		for (id, lits) in &t.assumptions {
			let item = FztConstraint::new(spelling::ASSUME, vec![ctx.bools(lits.iter().copied())]);
			items.push(format!("constraint {item} :: trace_id({id});"));
		}

		// The backward map, sorted by name for a reproducible model.
		let kept_name = t.kept.as_ref().and(t.objective.as_deref());
		let mut psi: Vec<(String, String)> = names
			.into_iter()
			.map(|(name, view)| {
				let term = if Some(name) == kept_name {
					name.to_owned()
				} else {
					match view {
						AnyView::Bool(b) => ctx.bool_term(b),
						AnyView::Int(i) => ctx.int_term(i),
					}
				};
				(name.to_owned(), term)
			})
			.collect();
		psi.extend(
			t.unmaterialized
				.iter()
				.map(|(name, _)| (name.clone(), name.clone())),
		);
		psi.sort();
		for (name, term) in psi {
			items.push(format!("psi {name} := {term};"));
		}
		items.push(objective.unwrap_or_else(|| "solve satisfy;".to_owned()));

		for item in &items {
			tracing::trace!(target: "start_model", item = %item);
		}
		tracing::trace!(target: "start_model", end = items.len() as u64);
		Ok(())
	}
	/// Record the FlatZinc variables that do not have a decision in the model.
	pub(crate) fn trace_unmaterialized(&mut self, vars: Vec<(String, DeclaredDomain)>) {
		if let Some(t) = self.trace.recording_mut() {
			t.unmaterialized = vars;
		}
	}
}
