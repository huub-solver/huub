//! Byte conversions used by the trailing infrastructure.

/// Lossless conversion to and from eight bytes for trailing storage.
///
/// Implementations should be cheap casts that avoid allocation or parsing, and
/// the byte order is an implementation detail rather than a serialization
/// format guarantee.
pub trait Bytes {
	/// Construct the value from its eight-byte representation.
	fn from_bytes(bytes: [u8; 8]) -> Self;
	/// Convert the value into its eight-byte representation.
	fn to_bytes(self) -> [u8; 8];
}

impl Bytes for bool {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes) != 0
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as u64).to_ne_bytes()
	}
}

impl Bytes for f32 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		f64::from_ne_bytes(bytes) as f32
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as f64).to_ne_bytes()
	}
}

impl Bytes for f64 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		f64::from_ne_bytes(bytes)
	}

	fn to_bytes(self) -> [u8; 8] {
		self.to_ne_bytes()
	}
}

impl Bytes for i16 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		i64::from_ne_bytes(bytes) as i16
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as i64).to_ne_bytes()
	}
}

impl Bytes for i32 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		i64::from_ne_bytes(bytes) as i32
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as i64).to_ne_bytes()
	}
}

impl Bytes for i64 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		i64::from_be_bytes(bytes)
	}

	fn to_bytes(self) -> [u8; 8] {
		self.to_be_bytes()
	}
}

impl Bytes for i8 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		i64::from_ne_bytes(bytes) as i8
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as i64).to_ne_bytes()
	}
}

impl Bytes for isize {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		i64::from_ne_bytes(bytes) as isize
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as i64).to_ne_bytes()
	}
}

impl Bytes for u16 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes) as u16
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as u64).to_ne_bytes()
	}
}

impl Bytes for u32 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes) as u32
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as u64).to_ne_bytes()
	}
}

impl Bytes for u64 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes)
	}

	fn to_bytes(self) -> [u8; 8] {
		self.to_ne_bytes()
	}
}

impl Bytes for u8 {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes) as u8
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as u64).to_ne_bytes()
	}
}

impl Bytes for usize {
	fn from_bytes(bytes: [u8; 8]) -> Self {
		u64::from_ne_bytes(bytes) as usize
	}

	fn to_bytes(self) -> [u8; 8] {
		(self as u64).to_ne_bytes()
	}
}
