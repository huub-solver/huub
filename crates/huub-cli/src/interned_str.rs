//! Module that implements string interning.
//!
//! This module provides a central [`InternedStr`] used in the entire
//! application. [`InternedStr`] are guaranteed to be uniquely stored, as such
//! they are memory efficient and can be instantly compared.

use std::{
	fmt::{self, Display},
	hash::{Hash, Hasher},
	mem,
	ops::Deref,
	ptr,
	sync::{LazyLock, Mutex},
};

use rustc_hash::FxHashSet;
use serde::{
	Deserialize, Deserializer, Serialize, Serializer,
	de::{Error, Visitor},
};

/// Central [`Interner`] used in the entire application.
static INTERNER: LazyLock<Mutex<Interner>> =
	LazyLock::new(|| Mutex::new(Interner::with_capacity(32768)));

#[derive(Debug, Clone, Copy, Ord, PartialOrd)]
/// A representation of a string that is interned in the [`Interner`].
pub(crate) struct InternedStr {
	/// The permanent reference to the stored string
	inner: &'static str,
}

/// Structure used to ensure that strings are uniquely stored and can be
/// compared based on index/pointer equality.
struct Interner {
	/// Map from strings to the index used to create [`InternedStr`].
	known_strs: FxHashSet<&'static str>,
	/// Buffer currently used to store new strings.
	cur_buf: String,
	/// Buffers that could no longer be used to store new strings.
	full_buf: Vec<Box<str>>,
}

impl Default for InternedStr {
	fn default() -> Self {
		Interner::EMPTY
	}
}

impl Deref for InternedStr {
	type Target = str;

	fn deref(&self) -> &Self::Target {
		self.inner
	}
}

impl<'de> Deserialize<'de> for InternedStr {
	fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
		struct StrVisitor;

		impl<'de> Visitor<'de> for StrVisitor {
			type Value = InternedStr;

			fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
				formatter.write_str("a &str")
			}

			fn visit_str<E: Error>(self, s: &str) -> Result<InternedStr, E> {
				Ok(InternedStr::from(s))
			}
		}

		deserializer.deserialize_str(StrVisitor)
	}
}

impl Display for InternedStr {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.deref().fmt(f)
	}
}

impl Eq for InternedStr {}

impl From<&str> for InternedStr {
	fn from(value: &str) -> Self {
		INTERNER.lock().unwrap().intern(value)
	}
}

impl From<String> for InternedStr {
	fn from(value: String) -> Self {
		INTERNER.lock().unwrap().intern(&value)
	}
}

impl Hash for InternedStr {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.deref().hash(state);
	}
}

impl PartialEq for InternedStr {
	fn eq(&self, other: &Self) -> bool {
		ptr::eq(self.inner, other.inner)
	}
}

impl Serialize for InternedStr {
	#[inline]
	fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
		self.deref().serialize(serializer)
	}
}

impl Interner {
	/// Reference to the empty string.
	const EMPTY: InternedStr = InternedStr { inner: "" };

	/// Allocates a new string in the interner's buffer.
	fn alloc(&mut self, s: &str) -> &'static str {
		// New string will exceed the current capacity, so we need to allocate a new
		// buffer.
		let cap = self.cur_buf.capacity();
		if self.cur_buf.len() + s.len() > cap {
			let new_cap = (cap.max(s.len()) + 1).next_power_of_two();
			let new_buf = String::with_capacity(new_cap);
			let old_buf = mem::replace(&mut self.cur_buf, new_buf);
			self.full_buf.push(old_buf.into_boxed_str());
		}
		// Add the string to the current buffer, and return a reference to the newly
		// added string
		let interned: *const str = {
			let start = self.cur_buf.len();
			let _buf_ptr = self.cur_buf.as_ptr();
			self.cur_buf.push_str(s);
			// (DEBUG): ensure that the buffer is not realloated.
			debug_assert_eq!(_buf_ptr, self.cur_buf.as_ptr());
			&self.cur_buf[start..]
		};

		// SAFETY: The buffers in the interner are guaranteed to exists for the full
		// application lifetime.
		unsafe { &*interned }
	}

	/// Store a given string if not already stored, return a reference to the
	/// stored representation.
	fn intern(&mut self, s: &str) -> InternedStr {
		// Check whether the string is already interned, and return it if so.
		if let Some(inner) = self.known_strs.get(s) {
			return InternedStr { inner };
		}

		// Allocate the new string in the interner's buffer and update the mapping.
		let inner = self.alloc(s);
		debug_assert_eq!(inner, s);
		let _inserted = self.known_strs.insert(inner);
		debug_assert!(_inserted);

		// (DEBUG) sanity check: interning would now return the same (inner) string
		let ret = InternedStr { inner };
		debug_assert_eq!(self.intern(inner), ret);
		ret
	}

	/// Create a new interner with the given capacity.
	fn with_capacity(cap: usize) -> Interner {
		let cap = cap.next_power_of_two();
		// Note that symbol_lookup and str_lookup are initialized with the empty
		// string.
		Interner {
			known_strs: FxHashSet::from_iter([""]),
			cur_buf: String::with_capacity(cap),
			full_buf: Vec::new(),
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{
		hash::{Hash, Hasher},
		ops::Deref,
		ptr,
	};

	use rustc_hash::FxHasher;

	use crate::interned_str::{INTERNER, InternedStr};

	#[test]
	fn copy() {
		let a = InternedStr::from("clone-me");
		let b = a;
		assert_eq!(a, b);
		assert!(ptr::eq::<str>(&*a, &*b));
	}

	#[test]
	fn deref_and_to_string() {
		let s = InternedStr::from("display-me");
		assert_eq!(&*s, "display-me");

		let disp = s.to_string();
		assert_eq!(disp, "display-me");
	}

	#[test]
	fn empty_string() {
		let d = InternedStr::default();
		assert_eq!(&*d, "");

		let empty = InternedStr::from("");
		assert_eq!(&*empty, &*d);
		assert_eq!(d, empty);
		assert!(ptr::eq::<str>(&*d, &*empty));
	}

	#[test]
	fn hash_consistency() {
		let s = InternedStr::from("hash-me");

		let mut ha = FxHasher::default();
		s.hash(&mut ha);
		let ih = ha.finish();

		let mut hb = FxHasher::default();
		"hash-me".hash(&mut hb);
		let sh = hb.finish();

		assert_eq!(ih, sh, "InternedStr hash should match underlying str hash");
	}

	#[test]
	fn intern_different() {
		let a = InternedStr::from("apple");
		let b = InternedStr::from("banana");

		// Different content => different &str pointers
		let sa: &str = a.deref();
		let sb: &str = b.deref();
		assert!(!ptr::eq(sa, sb));

		// Ord/PartialOrd forward to &str ordering
		assert!(a < b);
		assert_eq!(a.cmp(&b), "apple".cmp("banana"));
	}

	#[test]
	fn intern_identical() {
		let a = InternedStr::from("hello");
		let b = InternedStr::from("hello");

		// Equality should hold
		assert_eq!(a, b);

		// The deref'ed &str must be the exact same pointer for the same text
		let sa: &str = &a;
		let sb: &str = &b;
		assert!(
			ptr::eq(sa, sb),
			"expected same pointer for identical interned strings"
		);
	}

	#[test]
	fn serialize_and_deserialize() {
		let original = InternedStr::from("serde-me");

		// Serialize should just be the string
		let json = serde_json::to_string(&original).unwrap();
		assert_eq!(json, "\"serde-me\"");

		// Deserializing must produce an interned instance equal to "serde-me"
		let de: InternedStr = serde_json::from_str(&json).unwrap();
		assert_eq!(de, original);

		// Pointer identity should match the already-interned string
		assert!(ptr::eq::<str>(&*de, &*original));
	}

	#[test]
	fn str_and_string_identical() {
		let a = InternedStr::from("same");
		let b = InternedStr::from(String::from("same"));

		assert_eq!(a, b);
		assert!(ptr::eq::<str>(&*a, &*b));
	}

	#[test]
	fn valid_refernce_across_growth() {
		// Capture a pointer to a small, initial interned string.
		let anchor = InternedStr::from("anchor");
		let anchor_ptr: &str = &anchor;

		// Force multiple buffer growths by interning a lot of data.
		// We push well beyond 32 KiB (initial capacity in the interner).
		for i in 0..10_000 {
			// Varying content to avoid reusing the same interned entry
			let s = format!("item-{}-xxxxxxxxxxxxxxxx", i); // ~24+ chars each
			let _ = InternedStr::from(s);
		}
		assert!(!INTERNER.lock().unwrap().full_buf.is_empty());

		// The originally returned &'static str must still be valid and at the same
		// location
		assert_eq!(&*anchor, "anchor");
		assert_eq!(anchor_ptr, "anchor");
	}
}
