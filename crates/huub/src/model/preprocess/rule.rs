//! The rules that justify the steps of the preprocessing trace.

/// Rule that justifies a step of the preprocessing trace.
///
/// The names follow the rule catalogue of the preprocessing checker. Apart from
/// [`PreprocessRule::Preserve`], each rule is decided by the checker itself,
/// and applies to one kind of step only. A rule that does not apply to a step
/// is replaced by [`PreprocessRule::Preserve`] when the step is logged.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum PreprocessRule {
	/// A rewrite to a syntactically equal constraint.
	Identity,
	/// A rewrite between two linear constraints with the same normal form.
	LinNorm,
	/// A unification `x := c*y + a` justified by a linear equation between `x`
	/// and `y`.
	LinAffine,
	/// A unification `b := [x op k]` justified by a reified linear constraint
	/// over `x`.
	LinLit,
	/// A unification `b := !a` justified by `a + b = 1`.
	LinNeg,
	/// A unification `x := k` of a decision whose domain is `{k}`.
	Singleton,
	/// A domain change justified by a linear constraint over a single
	/// decision.
	LinUnary,
	/// The removal of a linear constraint that the domains entail.
	LinValid,
	/// The conclusion that a linear constraint cannot be satisfied.
	LinUnsat,
	/// A claim that the step preserves the solutions, which the checker
	/// discharges by brute force.
	Preserve,
}

/// The kind of a step in the preprocessing trace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StepKind {
	/// The addition of a constraint.
	Add,
	/// The introduction of a new variable.
	AddVar,
	/// The removal of a constraint.
	Del,
	/// A domain change.
	Dom,
	/// The replacement of a constraint by zero or more constraints.
	Rewrite,
	/// The replacement of a variable by a term.
	Unify,
	/// The conclusion that the model has no solutions.
	Unsat,
}

impl PreprocessRule {
	/// The name of the rule in the trace format.
	pub fn as_str(self) -> &'static str {
		match self {
			PreprocessRule::Identity => "identity",
			PreprocessRule::LinNorm => "lin-norm",
			PreprocessRule::LinAffine => "lin-affine",
			PreprocessRule::LinLit => "lin-lit",
			PreprocessRule::LinNeg => "lin-neg",
			PreprocessRule::Singleton => "singleton",
			PreprocessRule::LinUnary => "lin-unary",
			PreprocessRule::LinValid => "lin-valid",
			PreprocessRule::LinUnsat => "lin-unsat",
			PreprocessRule::Preserve => "preserve",
		}
	}

	/// Whether the rule applies to a step of the given kind.
	pub(super) fn fits(self, kind: StepKind) -> bool {
		match self {
			PreprocessRule::Identity | PreprocessRule::LinNorm => kind == StepKind::Rewrite,
			PreprocessRule::LinAffine
			| PreprocessRule::LinLit
			| PreprocessRule::LinNeg
			| PreprocessRule::Singleton => kind == StepKind::Unify,
			PreprocessRule::LinUnary => kind == StepKind::Dom,
			PreprocessRule::LinValid => kind == StepKind::Del,
			PreprocessRule::LinUnsat => kind == StepKind::Unsat,
			PreprocessRule::Preserve => true,
		}
	}

	/// Parse the name of a rule in the trace format.
	pub(super) fn from_str(s: &str) -> Option<Self> {
		Some(match s {
			"identity" => PreprocessRule::Identity,
			"lin-norm" => PreprocessRule::LinNorm,
			"lin-affine" => PreprocessRule::LinAffine,
			"lin-lit" => PreprocessRule::LinLit,
			"lin-neg" => PreprocessRule::LinNeg,
			"singleton" => PreprocessRule::Singleton,
			"lin-unary" => PreprocessRule::LinUnary,
			"lin-valid" => PreprocessRule::LinValid,
			"lin-unsat" => PreprocessRule::LinUnsat,
			"preserve" => PreprocessRule::Preserve,
			_ => return None,
		})
	}

	/// Whether the rule refers to the constraint that justifies the step.
	pub(super) fn needs_hint(self) -> bool {
		matches!(
			self,
			PreprocessRule::LinAffine
				| PreprocessRule::LinLit
				| PreprocessRule::LinNeg
				| PreprocessRule::LinUnary
				| PreprocessRule::LinUnsat
		)
	}
}

impl StepKind {
	/// The name of the kind of step in the trace format.
	pub(super) fn as_str(self) -> &'static str {
		match self {
			StepKind::Add => "add",
			StepKind::AddVar => "add var",
			StepKind::Del => "del",
			StepKind::Dom => "dom",
			StepKind::Rewrite => "rewrite",
			StepKind::Unify => "unify",
			StepKind::Unsat => "unsat",
		}
	}
}
