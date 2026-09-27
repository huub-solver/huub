//! Logging of the preprocessing that turns a received FlatZinc instance into
//! the [`Model`](crate::model::Model) that search starts from.
//!
//! When the `preprocess` tracing target is enabled while a FlatZinc instance is
//! read, the [`Model`](crate::model::Model) records every change it undergoes
//! between reading the instance and the start of search (unifications, domain
//! changes, and the addition, rewriting, and removal of constraints) as a step
//! on the `preprocess` target. At the start of search the model itself is
//! emitted, one item per event, on the `start_model` target. The two outputs
//! are written in the trace and `.fzt` formats of the `fzn-drcp-check`
//! preprocessing checker, which replays the steps from the received instance
//! and requires the result to equal the emitted model.
//!
//! Every step carries a justification: either a rule that the checker decides
//! itself, or [`PreprocessRule::Preserve`], a claim that the step preserves the
//! solutions, which the checker discharges by brute force. Changes are logged
//! where the model mutates (the domain setters, unification, and the posting
//! and simplification of constraints), so a change made by code that is not
//! aware of the trace is still logged, justified by
//! [`PreprocessRule::Preserve`]. Constraints can name a tailored rule for the
//! changes they make through
//! [`SimplificationActions::justify`](crate::actions::SimplificationActions::justify).
//!
//! Recording is off unless a trace was requested, and each hook then costs a
//! single check.

#![cfg_attr(
	not(feature = "flatzinc"),
	expect(
		dead_code,
		reason = "a trace is only recorded while a FlatZinc instance is read"
	)
)]

mod decisions;
mod dump;
mod fzt;
mod normalize;
mod registry;
mod rule;
pub(crate) mod spelling;
mod state;
mod windows;

pub(crate) use crate::model::preprocess::state::TraceState;
#[cfg(feature = "flatzinc")]
pub(crate) use crate::model::preprocess::{
	fzt::{DeclaredDomain, fzt_domain},
	normalize::lin_norm_equal,
	state::FznOutcome,
};
pub use crate::model::preprocess::{
	fzt::{FztArg, FztConstraint, FztContext, FztError, FztTerm},
	rule::PreprocessRule,
};
