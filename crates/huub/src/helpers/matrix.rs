//! This module provides a `Matrix` struct, which is a basic, generic container
//! multi-dimensional data within this crate.
//! storing elements in a row-major layout. This design makes it cache-friendly
//! for row-wise access patterns.
//!
//! ## Use Cases
//!
//! This `Matrix` is most useful when the data you are working with is
//! inherently multi-dimensional and you need a convenient way to access
//! elements using multi-dimensional indices (e.g., `matrix[[x, y, z]]`).
//! For example, it is used to represent collections of n-dimensional objects in
//! geometric packing or scheduling constraints.
//!
//! ## Design Considerations
//!
//! It is important to note that this is a data container and not a library for
//! numerical analysis or linear algebra. It does not provide operations like
//! matrix multiplication or inversion. The primary goal of this implementation
//! is to provide a simple, type-safe, and convenient abstraction for
//! for n-dimensional data. It is backed by a single, flat `Box<[T]>` array,

use std::{
	iter::repeat_with,
	ops::{Index, IndexMut},
};

/// A generic n-dimensional matrix.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Matrix<const DIMS: usize, T> {
	/// The data stored in the matrix in a row-major layout.
	data: Box<[T]>,
	/// The length of each dimensions of the matrix.
	dimensions: [usize; DIMS],
}

impl<T> Matrix<2, T> {
	/// Returns a slice representing a row of the matrix.
	pub(crate) fn row(&self, row: usize) -> &[T] {
		let start = row * self.len(1);
		let end = start + self.len(1);
		&self.data[start..end]
	}

	/// Returns an iterator over the rows of the matrix.
	pub(crate) fn row_iter(&self) -> impl Iterator<Item = &[T]> {
		self.data.chunks_exact(self.len(1))
	}
}

impl<const D: usize, T> Matrix<D, T> {
	/// Converts a multi-dimensional index into a 1D index for the underlying
	/// data array.
	fn internal_index(&self, index: [usize; D]) -> usize {
		let mut idx = 0;
		let mut mult = 1;
		for (i, &dim) in self.dimensions.iter().enumerate().rev() {
			idx += index[i] * mult;
			mult *= dim;
		}
		idx
	}

	/// Returns an iterator over the elements of the matrix.
	pub(crate) fn iter_elem(&self) -> impl Iterator<Item = &T> {
		self.data.iter()
	}

	/// Returns the length of a given dimension.
	pub(crate) fn len(&self, dim: usize) -> usize {
		self.dimensions[dim]
	}

	/// Creates a new matrix with the given dimensions and data read in
	/// row-major layout.
	///
	/// # Panics
	///
	/// Panics if the number of elements in `data` does not equal the product of
	/// the `dimensions`.
	pub(crate) fn new(dimensions: [usize; D], data: Box<[T]>) -> Self {
		assert_eq!(dimensions.iter().product::<usize>(), data.len());
		Self { data, dimensions }
	}

	/// Creates a new matrix with the given dimensions and filled with default
	/// values.
	pub(crate) fn with_dimensions(dimensions: [usize; D]) -> Self
	where
		T: Default,
	{
		let size = dimensions.iter().product();
		Self::new(
			dimensions,
			repeat_with(|| T::default()).take(size).collect(),
		)
	}
}

impl<const D: usize, T> Index<[usize; D]> for Matrix<D, T> {
	type Output = T;

	fn index(&self, index: [usize; D]) -> &Self::Output {
		&self.data[self.internal_index(index)]
	}
}

impl<const D: usize, T> IndexMut<[usize; D]> for Matrix<D, T> {
	fn index_mut(&mut self, index: [usize; D]) -> &mut Self::Output {
		&mut self.data[self.internal_index(index)]
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::matrix::Matrix;

	#[test]
	fn test_index_2d_new_data() {
		// 2x3 matrix, row-major layout: idx = col + row * 3
		let dims = [2, 3];
		let data: Box<[i32]> = (0..(dims.iter().product::<usize>() as i32))
			.collect::<Vec<_>>()
			.into_boxed_slice();
		let m = Matrix::new(dims, data);

		for r in 0..dims[0] {
			for c in 0..dims[1] {
				let expected = (r * dims[1] + c) as i32;
				assert_eq!(m[[r, c]], expected, "2D index mismatch at [{}, {}]", r, c);
			}
		}
	}

	#[test]
	fn test_index_3d_new_data() {
		// 2x3x4 matrix, row-major with dims [i, j, k]
		// idx = k + j * 4 + i * (3 * 4) = k + j*4 + i*12
		let dims = [2, 3, 4];
		let total = dims.iter().product::<usize>();
		let data: Box<[i32]> = (0..(total as i32)).collect::<Vec<_>>().into_boxed_slice();
		let m = Matrix::new(dims, data);

		for i in 0..dims[0] {
			for j in 0..dims[1] {
				for k in 0..dims[2] {
					let expected = (k + j * dims[2] + i * (dims[1] * dims[2])) as i32;
					assert_eq!(
						m[[i, j, k]],
						expected,
						"3D index mismatch at [{}, {}, {}]",
						i,
						j,
						k
					);
				}
			}
		}
	}

	#[test]
	fn test_index_mut_2d_with_dimensions() {
		let dims = [3, 4];
		let mut m: Matrix<2, i32> = Matrix::with_dimensions(dims);

		// fill using index_mut
		for r in 0..dims[0] {
			for c in 0..dims[1] {
				m[[r, c]] = (r as i32) * 100 + (c as i32);
			}
		}

		// verify
		for r in 0..dims[0] {
			for c in 0..dims[1] {
				assert_eq!(m[[r, c]], (r as i32) * 100 + (c as i32));
			}
		}
	}

	#[test]
	fn test_index_mut_3d_with_dimensions() {
		let dims = [2, 2, 3];
		let mut m: Matrix<3, i32> = Matrix::with_dimensions(dims);

		// fill using index_mut with a unique function of indices
		for i in 0..dims[0] {
			for j in 0..dims[1] {
				for k in 0..dims[2] {
					m[[i, j, k]] = (i as i32) * 1000 + (j as i32) * 100 + (k as i32);
				}
			}
		}

		// verify
		for i in 0..dims[0] {
			for j in 0..dims[1] {
				for k in 0..dims[2] {
					assert_eq!(
						m[[i, j, k]],
						(i as i32) * 1000 + (j as i32) * 100 + (k as i32)
					);
				}
			}
		}
	}
}
