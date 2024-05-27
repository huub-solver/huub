use std::{
	cmp::{max, min},
	ops::RangeInclusive,
};

use flatzinc_serde::RangeList;

use crate::IntVal;

/// Compute the RangeList that is i diff j
pub(crate) fn diff_range_list(i: &RangeList<IntVal>, j: &RangeList<IntVal>) -> RangeList<IntVal> {
	if i.is_empty() {
		return RangeList::from_iter([]);
	}
	let mut i = i.iter().peekable();
	let mut j = j.iter().peekable();
	let mut ranges = Vec::new();
	let mut max: IntVal = *i.peek().unwrap().start();
	loop {
		if i.peek().is_none() {
			break;
		}
		let mut min = max + 1;
		max = *i.peek().unwrap().end();
		if min > *i.peek().unwrap().end() {
			let _ = i.next();
			if let Some(r) = i.peek() {
				min = *r.start();
				max = *r.end();
			} else {
				break;
			}
		}
		while let Some(r) = j.peek() {
			if r.end() < i.peek().unwrap().start() {
				let _ = j.next();
			} else {
				break;
			}
		}
		if let Some(r) = j.peek() {
			if *r.start() <= max {
				// Interval min..max must be shurk
				if min >= *r.start() && max <= *r.end() {
					// Interval min..max is completely covered by r
					continue;
				}
				if *r.start() <= min {
					// Interval min..max overlaps on the left
					min = r.end() + 1;
					// Search for max
					let _ = j.next();
					if let Some(r) = j.peek() {
						if *r.start() <= max {
							max = r.start() - 1;
						}
					}
				} else {
					// Interval overlaps on the right
					max = r.start() - 1;
				}
			}
		}
		ranges.push(min..=max);
	}
	RangeList::from_iter(ranges)
}

pub(crate) fn intersect_range_list(
	i: &RangeList<IntVal>,
	j: &RangeList<IntVal>,
) -> RangeList<IntVal> {
	let mut lhs = i.iter().peekable();
	let mut rhs = j.iter().peekable();
	let mut ranges = Vec::new();
	while let (Some(l), Some(r)) = (lhs.peek(), rhs.peek()) {
		match overlap(l, r) {
			RangeOrdering::Less => {
				let _ = lhs.next();
			}
			RangeOrdering::Greater => {
				let _ = rhs.next();
			}
			RangeOrdering::Overlap => {
				ranges.push(max(*l.start(), *r.start())..=min(*l.end(), *r.end()));
				if l.end() <= r.end() {
					let _ = lhs.next();
				} else {
					let _ = rhs.next();
				}
			}
		}
	}
	ranges.into_iter().collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RangeOrdering {
	/// A compared range is strictly less than another.
	Less = -1,
	/// A compared range overlaps with another.
	Overlap = 0,
	/// A compared range is strictly greater than another.
	Greater = 1,
}

fn overlap<T: Ord>(r1: &RangeInclusive<T>, r2: &RangeInclusive<T>) -> RangeOrdering {
	if r1.end() < r2.start() {
		RangeOrdering::Less
	} else if r2.end() < r1.start() {
		RangeOrdering::Greater
	} else {
		RangeOrdering::Overlap
	}
}
