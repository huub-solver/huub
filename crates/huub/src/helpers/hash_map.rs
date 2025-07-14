//! This module provides [`Hasher`] implementations that are more performant
//! compared to the default [`Hasher`] used by [`HashMap`]. These
//! implementations are specialized for the number of bits used by the key (only
//! accepting one field), and are not cryptographically secure.

use std::{
	collections::HashMap,
	hash::{BuildHasher, Hasher},
	num::Wrapping,
};

/// Trivial builder that creates a [`FastHash32`] hasher.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct BuildFastHash32;

/// Trivial builder that creates a [`FastHash64`] hasher.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct BuildFastHash64;

/// Fast [`Hasher`] for 32-bit values, suitable for non-cryptographic use.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct FastHash32 {
	/// Incumbent hash value
	hash: Wrapping<u32>,
}

/// Fast [`Hasher`] for 64-bit values, suitable for non-cryptographic use.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct FastHash64 {
	/// Incumbent hash value
	hash: Wrapping<u64>,
}

/// Type alias for a [`HashMap`] that will **only accept 32-bit keys**, using an
/// specialized hash function optimized for performance. This is only suitable
/// for non-cryptographic use.
pub(crate) type FastMap32<K, V> = HashMap<K, V, BuildFastHash32>;

/// Type alias for a [`HashMap`] that will **only accept 64-bit keys**, using an
/// specialized hash function optimized for performance. This is only suitable
/// for non-cryptographic use.
pub(crate) type FastMap64<K, V> = HashMap<K, V, BuildFastHash64>;

impl BuildHasher for BuildFastHash32 {
	type Hasher = FastHash32;

	fn build_hasher(&self) -> Self::Hasher {
		FastHash32 { hash: Wrapping(0) }
	}
}

impl Hasher for FastHash32 {
	fn finish(&self) -> u64 {
		self.hash.0 as u64
	}

	fn write(&mut self, bytes: &[u8]) {
		debug_assert_eq!(bytes.len(), 4, "unable to hash non 32-bit values");
		let x = u32::from_ne_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
		self.write_u32(x);
	}

	fn write_u32(&mut self, x: u32) {
		// Fast hash function from hash prospector project: https://github.com/skeeto/hash-prospector
		debug_assert_eq!(self.hash, Wrapping(0), "unable to hash multiple values");
		self.hash = Wrapping(x);
		self.hash ^= self.hash >> 16;
		self.hash *= 0x7feb352d;
		self.hash ^= self.hash >> 15;
		self.hash *= 0x846ca68b;
		self.hash ^= self.hash >> 16;
	}
}

impl BuildHasher for BuildFastHash64 {
	type Hasher = FastHash64;

	fn build_hasher(&self) -> Self::Hasher {
		FastHash64 { hash: Wrapping(0) }
	}
}

impl Hasher for FastHash64 {
	fn finish(&self) -> u64 {
		self.hash.0
	}

	fn write(&mut self, bytes: &[u8]) {
		debug_assert_eq!(bytes.len(), 8, "unable to hash non 64-bit values");
		let x = u64::from_ne_bytes([
			bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
		]);
		self.write_u64(x);
	}

	fn write_u64(&mut self, x: u64) {
		// Fast hash function from https://stackoverflow.com/a/12996028/1351597
		debug_assert_eq!(self.hash, Wrapping(0), "unable to hash multiple values");
		self.hash = Wrapping(x);
		self.hash ^= self.hash >> 30;
		self.hash *= 0xbf58476d1ce4e5b9;
		self.hash ^= self.hash >> 27;
		self.hash *= 0x94d049bb133111eb;
		self.hash ^= self.hash >> 31;
	}
}
