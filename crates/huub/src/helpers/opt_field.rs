//! Compile time optional field implementation.

use std::hash::{Hash, Hasher};

#[derive(Debug)]
/// Compile time optional field.
///
/// This is used to represent fields that may or may not be present in a struct,
/// based on a compile time constant.
///
/// Note that `B` is a `usize` constant because of implementation limitations in
/// Rust. It should, however, be a `bool` and only the values `0` and `1` should
/// be used.
pub(crate) struct OptField<const B: usize, T> {
	/// Content of the field, if any.
	value: [T; B],
}

impl<T> OptField<1, T> {
	/// Creates a new `OptField` with the given value.
	pub(crate) fn new(value: T) -> Self {
		Self { value: [value] }
	}
}

impl<const B: usize, T> OptField<B, T> {
	#[inline]
	/// Return the value of the `OptField`, if it exists.
	pub(crate) fn get(&self) -> Option<&T> {
		self.value.first()
	}
}

impl<const B: usize, T: Clone> Clone for OptField<B, T> {
	fn clone(&self) -> Self {
		Self {
			value: self.value.clone(),
		}
	}
}

impl<T> Default for OptField<0, T> {
	fn default() -> Self {
		Self { value: [] }
	}
}

impl<T: Default> Default for OptField<1, T> {
	fn default() -> Self {
		Self {
			value: [T::default()],
		}
	}
}

impl<const B: usize, T: Eq> Eq for OptField<B, T> {}

impl<const B: usize, T: Hash> Hash for OptField<B, T> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.value.iter().for_each(|v| v.hash(state));
	}
}

impl<const B: usize, T: PartialEq> PartialEq for OptField<B, T> {
	fn eq(&self, other: &Self) -> bool {
		self.value == other.value
	}
}

#[cfg(test)]
mod tests {
	use std::hash::{DefaultHasher, Hash, Hasher};

	use super::OptField;

	#[test]
	fn test_optfield_new() {
		let opt_field = OptField::new(42);
		assert_eq!(opt_field.get(), Some(&42));
	}

	#[test]
	fn test_optfield_default() {
		let opt_field: OptField<0, i32> = OptField::default();
		assert_eq!(opt_field.get(), None);

		let opt_field: OptField<1, i32> = OptField::default();
		assert_eq!(opt_field.get(), Some(&0));
	}

	#[test]
	fn test_optfield_clone() {
		let opt_field = OptField::new(42);
		let cloned = opt_field.clone();
		assert_eq!(opt_field.get(), cloned.get());
		let opt_field: OptField<0, bool> = OptField::default();
		let cloned = opt_field.clone();
		assert_eq!(opt_field.get(), cloned.get());
	}

	#[test]
	fn test_optfield_eq() {
		let opt_field1 = OptField::new(42);
		let opt_field2 = OptField::new(42);
		assert_eq!(opt_field1, opt_field2);

		let opt_field3 = OptField::new(43);
		assert_ne!(opt_field1, opt_field3);

		let opt_field1: OptField<0, i32> = OptField::default();
		let opt_field2: OptField<0, i32> = OptField::default();
		assert_eq!(opt_field1, opt_field2);
	}

	#[test]
	fn test_optfield_hash() {
		let opt_field = OptField::new(42);
		let mut hasher = DefaultHasher::new();
		opt_field.hash(&mut hasher);
		let hash1 = hasher.finish();

		let opt_field2 = OptField::new(42);
		let mut hasher2 = DefaultHasher::new();
		opt_field2.hash(&mut hasher2);
		let hash2 = hasher2.finish();

		assert_eq!(hash1, hash2);
	}
}
