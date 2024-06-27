#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum IntEvent {
	Fixed,
	LowerBound,
	UpperBound,
	Bounds,
	Domain,
}

impl IntEvent {
	pub(crate) fn is_activated_by(&self, other: &IntEvent) -> bool {
		use IntEvent::*;
		matches!(
			(self, other),
			(_, Fixed)
				| (LowerBound, LowerBound)
				| (LowerBound, Bounds)
				| (UpperBound, UpperBound)
				| (UpperBound, Bounds)
				| (Bounds, LowerBound)
				| (Bounds, UpperBound)
				| (Bounds, Bounds)
				| (Domain, _)
		)
	}
}
