//! The delivery of the preprocessing trace to the code that asked for it.

use std::fmt::Debug;

/// An event of the preprocessing trace.
///
/// The steps of the trace and the items of the model at the start of search are
/// written in the `.trace` and `.fzt` formats of the `fzn-drcp-check`
/// preprocessing checker, one step or item per event. Both are closed by an
/// event that states how many were delivered, which lets the receiver check
/// that none were lost.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum PreprocessEvent {
	/// The steps of the trace are complete.
	EndTrace {
		/// The number of steps.
		steps: u64,
	},
	/// The model at the start of search is complete.
	EndStartModel {
		/// The number of items.
		items: u64,
	},
	/// An item of the model at the start of search.
	StartModelItem(String),
	/// A step of the trace.
	Step {
		/// The number of the step, which starts at 1.
		seq: u64,
		/// The step.
		text: String,
	},
}

/// The receiver of a preprocessing trace.
///
/// A sink is given to
/// [`HuubFlatZinc::lower_with_preprocess_trace`](crate::model::deserialize::flatzinc::HuubFlatZinc::lower_with_preprocess_trace),
/// and receives the events while the instance is lowered. A model that is
/// cloned shares its sink with the clone.
pub trait PreprocessSink: Debug + Send {
	/// Receive an event of the trace.
	fn event(&mut self, event: PreprocessEvent);
}
