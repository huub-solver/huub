use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub(crate) struct OptField<const B: usize, T> {
	value: [T; B],
}

impl<const B: usize, T> OptField<B, T> {
	#[inline]
	pub(crate) fn get(&self) -> Option<&T> {
		self.value.first()
	}
}
impl<T> OptField<1, T> {
	pub(crate) fn new(value: T) -> Self {
		Self { value: [value] }
	}
}

impl<T: Default> Default for OptField<1, T> {
	fn default() -> Self {
		Self {
			value: [T::default()],
		}
	}
}
impl<T> Default for OptField<0, T> {
	fn default() -> Self {
		Self { value: [] }
	}
}

impl<const B: usize, T: PartialEq> PartialEq for OptField<B, T> {
	fn eq(&self, other: &Self) -> bool {
		self.value == other.value
	}
}
impl<const B: usize, T: Eq> Eq for OptField<B, T> {}

impl<const B: usize, T: Clone> Clone for OptField<B, T> {
	fn clone(&self) -> Self {
		Self {
			value: self.value.clone(),
		}
	}
}
impl<const B: usize, T: Hash> Hash for OptField<B, T> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.value.iter().for_each(|v| v.hash(state));
	}
}
