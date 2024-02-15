pub enum IntEvent {
	Fixed,
	LowerBound,
	UpperBound,
	#[allow(dead_code)] // TODO
	Bounds,
	Domain,
}

impl IntEvent {
	pub fn is_activated_by(&self, other: &IntEvent) -> bool {
		use IntEvent::*;
		match (self, other) {
			(_, Fixed) => true,
			(LowerBound, LowerBound) => true,
			(LowerBound, Bounds) => true,
			(UpperBound, UpperBound) => true,
			(UpperBound, Bounds) => true,
			(Bounds, LowerBound) => true,
			(Bounds, UpperBound) => true,
			(Bounds, Bounds) => true,
			(Domain, _) => true,
			_ => false,
		}
	}
}
