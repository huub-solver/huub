//! Module containing the representation of integer variables within the solver.

use std::{
	collections::hash_map::{self, VacantEntry},
	iter::{Map, Peekable},
	ops::{Index, IndexMut, RangeBounds, RangeInclusive},
};

use itertools::Itertools;
use pindakaas::{
	solver::propagation::ExternalPropagation, ClauseDatabaseTools, Lit as RawLit, Var as RawVar,
	VarRange,
};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	actions::{BoolInspectionActions, TrailingActions},
	solver::{trail::TrailedInt, BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner},
	IntSetVal, IntVal, LinearTransform, NonZeroIntVal, Solver,
};

/// An entry in the [`DirectStorage`] that can be used to access the
/// representation of an equality condition, or insert a new literal to
/// represent the condition otherwise.
enum DirectEntry<'a> {
	/// The condition is already stored in the [`DirectStorage`].
	Occupied(BoolViewInner),
	/// The condition is not yet stored in the [`DirectStorage`].
	Vacant(VacantEntry<'a, IntVal, RawVar>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// The structure that stores the equality conditions. Equality conditions can
/// either be eagerly crated, and stored as a range of variables, or lazily
/// created and stored in a [`HashMap`] once created.
pub(crate) enum DirectStorage {
	/// Variables for all equality conditions are eagerly created and stored in
	/// order
	Eager(VarRange),
	/// Variables for equality conditions are lazily created and stored in a
	/// hashmap
	Lazy(FxHashMap<IntVal, RawVar>),
}

#[derive(Clone, Debug)]
/// Type used resolve (possible) values in the domain to order literals and
/// their tightest literal meaning.
///
/// Used as the return type of [`OrderStorage::resolve_val`].
struct DomainLocation<'a> {
	/// Tightest value for the less-than literal
	less_val: IntVal,
	/// Tightest value for the greater-than or equal-to literal
	greater_eq_val: IntVal,
	/// Offset of the literal in the variable range.
	offset: usize,
	/// Iterator in the domain that point to the range in which the value is
	/// located.
	range_iter: RangeIter<'a>,
}

/// A type to represent when certain literals are created
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EncodingType {
	/// The literal is created before solving starts
	Eager,
	/// The literal is created the first time it is mentioned
	Lazy,
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// The structure used to store information about an integer variable within
/// the solver.
pub(crate) struct IntVar {
	/// The direct encoding of the integer variable.
	///
	/// Literals in this encoding are used to reason about whether an integer
	/// variable takes a certain value.
	pub(crate) direct_encoding: DirectStorage,
	/// The domain of the integer variable at the time of its creation.
	pub(crate) domain: RangeList<IntVal>,
	/// The order encoding of the integer variable.
	///
	/// Literals in this encoding are used to reason about the bounds of the
	/// integer variable.
	pub(crate) order_encoding: OrderStorage,
	/// A Trailed integer representing the current upper bound of the integer
	/// variable.
	///
	/// Note that the lower bound is tracked within [`Self::order_encoding`].
	upper_bound: TrailedInt,
}

#[derive(Debug)]
/// The definition given to a lazily created literal.
pub(crate) struct LazyLitDef {
	/// The meaning that the literal is meant to represent.
	pub(crate) meaning: IntLitMeaning,
	/// The variable that represent:
	/// - if `meaning` is `LitMeaning::Less(j)`, then `prev` contains the
	///   literal `< i` where `i` is the value right before `j` in the storage.
	/// - if `meaning` is `LitMeaning::Eq(k)`, then `prev` contains the literal
	///   `<j`.
	pub(crate) prev: Option<RawVar>,
	/// The variable that represent the literal `< k` where `k` is the value
	/// right after the value represented by the literal.
	pub(crate) next: Option<RawVar>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// A storage structure to manage lazily created order literals for an integer
/// variable.
pub(crate) struct LazyOrderStorage {
	/// The index of the node with the minimum value in the storage.
	min_index: u32,
	/// The index of the node with the maximum value in the storage.
	max_index: u32,
	/// The index of the node that currently represents the lower bound of the
	/// integer variable.
	lb_index: TrailedInt,
	/// The index of the node that currently represents the upper bound of the
	/// integer variable.
	ub_index: TrailedInt,
	/// The storage of all currently created nodes containing the order literals
	/// for the integer variable.
	storage: Vec<OrderNode>,
}

#[derive(Debug)]
/// An entry in [`OrderStorage`] that can be used to access the representation
/// of an inequality condition, or insert a new literal to represent the
/// condition otherwise.
enum OrderEntry<'a> {
	/// Entry already exists and was eagerly created.
	Eager(&'a VarRange, usize),
	/// Entry already exists and was lazily created.
	Occupied {
		/// Reference to the storage where the entry is stored.
		storage: &'a mut LazyOrderStorage,
		/// The index of the node in the storage that the entry points to.
		index: u32,
		/// An iterator pointing at the range in the domain in which the value
		/// of which the value of the entry is part.
		range_iter: RangeIter<'a>,
	},
	/// Entry does not exist and can be lazily created.
	Vacant {
		/// Reference to the storage where the new entry will be created.
		storage: &'a mut LazyOrderStorage,
		/// The index of the node that contains the value right before the new
		/// entry that will be created.
		prev_index: IntVal,
		/// An iterator pointing at the range in the domain in which the value
		/// of which the value of the new entry is part.
		range_iter: RangeIter<'a>,
		/// The value for which the entry will be created.
		val: IntVal,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Type used to store individual entries in [`LazyOrderStorage`].
///
/// ## Warning
///
/// Because the values for literals of `≥` literals are part of the domains, the
/// values included in the node are that for the meaning of the `≥` literal.
/// However, the positive [`RawVar`] is used to represent a `<` literal (because
/// of standard phasing in SAT solvers), which might have a stronger meaning
/// than `< val` because of gaps in the original domain.
pub(crate) struct OrderNode {
	/// The value for which `!var` represents `x ≥ val`.
	val: IntVal,
	/// The variable representing `!(x ≥ val)`.
	var: RawVar,
	/// Whether there is a node with a value less than `val`.
	has_prev: bool,
	/// The index of the node with a value less than `val`.
	prev: u32,
	/// Whether there is a node with a value greater than `val`.
	has_next: bool,
	/// The index of the node with a value greater than `val`.
	next: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(
	variant_size_differences,
	reason = "TODO: Investigate if using Box improves performance"
)]
/// The storage used to store the variables for the inequality conditions.
pub(crate) enum OrderStorage {
	/// Variables for all inequality conditions are eagerly created and stored
	/// in order.
	Eager {
		/// A trailed integer that represents the currently lower bound of the
		/// variable.
		lower_bound: TrailedInt,
		/// The range of Boolean variables that represent the inequality
		/// conditions.
		storage: VarRange,
	},
	/// Variables for inequality conditions are lazily created and specialized
	/// node structure, a [`LazyOrderStorage`].
	Lazy(LazyOrderStorage),
}

/// Type alias for an iterator that yields the ranges of a [`RangeList`], which
/// is used to represent the domains of an integer variable.
type RangeIter<'a> = Peekable<
	Map<
		<&'a RangeList<IntVal> as IntoIterator>::IntoIter,
		fn(RangeInclusive<&'a IntVal>) -> RangeInclusive<IntVal>,
	>,
>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A direction to search in.
enum SearchDirection {
	/// Search from low to high.
	Increasing,
	/// Search from high to low.
	Decreasing,
}

impl DirectEntry<'_> {
	/// Extract the [`BoolViewInner`] if the entry is occupied, or insert a new
	/// variable using the given function.
	fn or_insert_with(self, f: impl FnOnce() -> RawVar) -> BoolViewInner {
		match self {
			DirectEntry::Occupied(bv) => bv,
			DirectEntry::Vacant(no_entry) => {
				let v = f();
				let _ = no_entry.insert(v);
				BoolViewInner::Lit(v.into())
			}
		}
	}
}

impl DirectStorage {
	/// Locate the position in the [`DirectStorage`] that would be used to store
	/// the representation of the condition `= i`. The method will return a
	/// [`DirectEntry`] object that can be used to access the condition as a
	/// [`BoolViewInner`] if it already exists, or insert a new literal to
	/// represent the condition otherwise.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn entry(&mut self, domain: &RangeList<IntVal>, i: IntVal) -> DirectEntry<'_> {
		match self {
			DirectStorage::Eager(vars) => {
				// Calculate the offset in the VarRange
				let mut offset = Some(-1); // -1 to account for the lower bound
				for r in domain.iter() {
					if i < *r.start() {
						offset = None;
						break;
					} else if r.contains(&i) {
						offset = Some(offset.unwrap() + i - r.start());
						break;
					} else {
						offset = Some(offset.unwrap() + r.end() - r.start() + 1);
					}
				}
				if let Some(offset) = offset {
					debug_assert!(
						(offset as usize) < vars.len(),
						"var range offset, {}, must be in [{}, {})",
						offset,
						0,
						vars.len(),
					);
					DirectEntry::Occupied(BoolViewInner::Lit(vars.index(offset as usize).into()))
				} else {
					DirectEntry::Occupied(BoolViewInner::Const(false))
				}
			}
			DirectStorage::Lazy(map) => match map.entry(i) {
				hash_map::Entry::Occupied(entry) => {
					DirectEntry::Occupied(BoolViewInner::Lit((*entry.get()).into()))
				}
				hash_map::Entry::Vacant(no_entry) => {
					if domain.contains(&i) {
						DirectEntry::Vacant(no_entry)
					} else {
						DirectEntry::Occupied(BoolViewInner::Const(false))
					}
				}
			},
		}
	}

	/// Return the [`BoolViewInner`] that represent the condition `= i`, if it
	/// already exists.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn find(&self, domain: &RangeList<IntVal>, i: IntVal) -> Option<BoolViewInner> {
		match self {
			DirectStorage::Eager(vars) => {
				// Calculate the offset in the VarRange
				let mut offset = Some(-1); // -1 to account for the lower bound
				for r in domain.iter() {
					if i < *r.start() {
						offset = None;
						break;
					} else if r.contains(&i) {
						offset = Some(offset.unwrap() + i - r.start());
						break;
					} else {
						offset = Some(offset.unwrap() + r.end() - r.start() + 1);
					}
				}
				Some(if let Some(offset) = offset {
					debug_assert!(
						(offset as usize) < vars.len(),
						"var range offset, {}, must be in [{}, {})",
						offset,
						0,
						vars.len(),
					);
					BoolViewInner::Lit(vars.index(offset as usize).into())
				} else {
					BoolViewInner::Const(false)
				})
			}
			DirectStorage::Lazy(map) => map
				.get(&i)
				.map(|v| BoolViewInner::Lit((*v).into()))
				.or_else(|| {
					if !domain.contains(&i) {
						Some(BoolViewInner::Const(false))
					} else {
						None
					}
				}),
		}
	}
}

impl IntVar {
	/// Access the Boolean literal with the given meaning, creating it if it is
	/// not yet available.
	pub(crate) fn bool_lit(
		&mut self,
		lit_req: IntLitMeaning,
		mut new_var: impl FnMut(LazyLitDef) -> RawVar,
	) -> (BoolView, IntLitMeaning) {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();

		// Use the order literals when requesting an equality literal of the global
		// bounds.
		let mut lit_req = match lit_req {
			IntLitMeaning::Eq(i) if i == lb => IntLitMeaning::Less(lb + 1),
			IntLitMeaning::NotEq(i) if i == lb => IntLitMeaning::GreaterEq(lb + 1),
			IntLitMeaning::Eq(i) if i == ub => IntLitMeaning::GreaterEq(ub),
			IntLitMeaning::NotEq(i) if i == ub => IntLitMeaning::Less(ub),
			_ => lit_req,
		};

		let bv = BoolView(match lit_req {
			IntLitMeaning::Eq(i) | IntLitMeaning::NotEq(i) if i < lb || i > ub => {
				BoolViewInner::Const(matches!(lit_req, IntLitMeaning::NotEq(_)))
			}
			IntLitMeaning::Eq(i) | IntLitMeaning::NotEq(i) => {
				let bv = self
					.direct_encoding
					.entry(&self.domain, i)
					.or_insert_with(|| {
						let (entry, prev) =
							self.order_encoding.entry(&self.domain, i).0.or_insert_with(
								|val, prev, next| {
									new_var(LazyLitDef {
										meaning: IntLitMeaning::Less(val),
										prev,
										next,
									})
								},
							);
						let next = entry
							.next_value()
							.or_insert_with(|val, prev, next| {
								new_var(LazyLitDef {
									meaning: IntLitMeaning::Less(val),
									prev,
									next,
								})
							})
							.1;
						new_var(LazyLitDef {
							meaning: IntLitMeaning::Eq(i),
							prev: Some(prev),
							next: Some(next),
						})
					});
				if matches!(lit_req, IntLitMeaning::NotEq(_)) {
					!bv
				} else {
					bv
				}
			}
			IntLitMeaning::GreaterEq(i) | IntLitMeaning::Less(i) if i <= lb => {
				BoolViewInner::Const(matches!(lit_req, IntLitMeaning::GreaterEq(_)))
			}
			IntLitMeaning::GreaterEq(i) | IntLitMeaning::Less(i) if i > ub => {
				BoolViewInner::Const(matches!(lit_req, IntLitMeaning::Less(_)))
			}
			IntLitMeaning::GreaterEq(i) | IntLitMeaning::Less(i) => {
				let (entry, lt, geq) = self.order_encoding.entry(&self.domain, i);
				let var: RawLit = entry
					.or_insert_with(|val, prev, next| {
						new_var(LazyLitDef {
							meaning: IntLitMeaning::Less(val),
							prev,
							next,
						})
					})
					.1
					.into();
				BoolViewInner::Lit(if matches!(lit_req, IntLitMeaning::GreaterEq(_)) {
					lit_req = IntLitMeaning::GreaterEq(geq);
					!var
				} else {
					lit_req = IntLitMeaning::Less(lt);
					var
				})
			}
		});

		(bv, lit_req)
	}

	/// Try and find an (already) existing Boolean literal with the given
	/// meaning
	pub(crate) fn get_bool_lit(&self, lit_req: IntLitMeaning) -> Option<(BoolView, IntLitMeaning)> {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();

		// Use the order literals when requesting an equality literal of the global
		// bounds.
		let mut lit_req = match lit_req {
			IntLitMeaning::Eq(i) if i == lb => IntLitMeaning::Less(lb + 1),
			IntLitMeaning::NotEq(i) if i == lb => IntLitMeaning::GreaterEq(lb + 1),
			IntLitMeaning::Eq(i) if i == ub => IntLitMeaning::GreaterEq(ub),
			IntLitMeaning::NotEq(i) if i == ub => IntLitMeaning::Less(ub),
			_ => lit_req,
		};

		let bv = BoolView(match lit_req {
			IntLitMeaning::Eq(i) if i < lb || i > ub => BoolViewInner::Const(false),
			IntLitMeaning::Eq(i) => self.direct_encoding.find(&self.domain, i)?,
			IntLitMeaning::GreaterEq(i) if i <= lb => BoolViewInner::Const(true),
			IntLitMeaning::GreaterEq(i) if i > ub => BoolViewInner::Const(false),
			IntLitMeaning::GreaterEq(i) => {
				let (var, _, geq) = self.order_encoding.find(&self.domain, i)?;
				lit_req = IntLitMeaning::GreaterEq(geq);
				BoolViewInner::Lit(!var)
			}
			IntLitMeaning::Less(i) if i <= lb => BoolViewInner::Const(false),
			IntLitMeaning::Less(i) if i > ub => BoolViewInner::Const(true),
			IntLitMeaning::Less(i) => {
				let (var, lt, _) = self.order_encoding.find(&self.domain, i)?;
				lit_req = IntLitMeaning::Less(lt);
				BoolViewInner::Lit(var.into())
			}
			IntLitMeaning::NotEq(i) if i < lb || i > ub => BoolViewInner::Const(true),
			IntLitMeaning::NotEq(i) => !self.direct_encoding.find(&self.domain, i)?,
		});
		Some((bv, lit_req))
	}

	/// Returns the lower and upper bounds of the current state of the integer
	/// variable.
	pub(crate) fn get_bounds(&self, trail: &impl TrailingActions) -> (IntVal, IntVal) {
		let lb = match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => trail.get_trailed_int(*lower_bound),
			OrderStorage::Lazy(storage) => {
				let low = trail.get_trailed_int(storage.lb_index);
				if low >= 0 {
					storage.storage[low as usize].val
				} else {
					*self.domain.lower_bound().unwrap()
				}
			}
		};
		(lb, trail.get_trailed_int(self.upper_bound))
	}

	/// Returns the boolean view associated with `≥ v` if it exists or weaker
	/// version otherwise.
	///
	/// ## Warning
	/// This function assumes that `v <= lb`.
	pub(crate) fn get_greater_eq_lit_or_weaker<T>(&self, trail: &T, v: IntVal) -> (BoolView, IntVal)
	where
		T: TrailingActions,
		RawLit: BoolInspectionActions<T>,
	{
		debug_assert!(v <= self.get_lower_bound(trail));
		if v <= *self.domain.lower_bound().unwrap() {
			return (BoolView(BoolViewInner::Const(true)), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation { offset, .. } = OrderStorage::resolve_val(&self.domain, v);
				(BoolView(BoolViewInner::Lit(!storage.index(offset))), v)
			}
			OrderStorage::Lazy(storage) => {
				let mut ret = (BoolView(BoolViewInner::Const(true)), v);
				let lb_index = trail.get_trailed_int(storage.lb_index);
				let mut index = if lb_index < 0 {
					return ret;
				} else {
					lb_index as usize
				};
				while storage.storage[index].val >= v {
					let node = &storage.storage[index];
					let lit = BoolView(BoolViewInner::Lit(!node.var));
					if let Some(v) = lit.get_val(trail) {
						debug_assert!(v);
						ret = (lit, node.val);
					}
					if !node.has_prev {
						break;
					}
					index = node.prev as usize;
				}
				ret
			}
		}
	}

	/// Returns the boolean view associated with `< v` if it exists or weaker
	/// version otherwise.
	///
	/// ## Warning
	/// This function assumes that `v >= ub`.
	pub(crate) fn get_less_lit_or_weaker<T>(&self, trail: &T, v: IntVal) -> (BoolView, IntVal)
	where
		T: TrailingActions,
		RawLit: BoolInspectionActions<T>,
	{
		debug_assert!(v >= self.get_upper_bound(trail));
		if v > *self.domain.upper_bound().unwrap() {
			return (BoolView(BoolViewInner::Const(true)), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation { offset, .. } = OrderStorage::resolve_val(&self.domain, v);
				let bv = BoolView(BoolViewInner::Lit(storage.index(offset).into()));
				(bv, v)
			}
			OrderStorage::Lazy(storage) => {
				let mut ret = (BoolView(BoolViewInner::Const(true)), v);
				let ub_index = trail.get_trailed_int(storage.ub_index);
				let mut index = if ub_index < 0 {
					return ret;
				} else {
					ub_index as usize
				};
				while storage.storage[index].val <= v {
					let node = &storage.storage[index];
					let lit = BoolView(BoolViewInner::Lit(node.var.into()));
					if let Some(v) = lit.get_val(trail) {
						debug_assert!(v);
						ret = (lit, node.val);
					}
					if !node.has_next {
						break;
					}
					index = node.next as usize;
				}
				ret
			}
		}
	}

	/// Returns the lower bound of the current state of the integer variable.
	pub(crate) fn get_lower_bound<T>(&self, trail: &T) -> IntVal
	where
		T: TrailingActions,
		RawLit: BoolInspectionActions<T>,
	{
		match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => trail.get_trailed_int(*lower_bound),
			OrderStorage::Lazy(storage) => {
				let low = trail.get_trailed_int(storage.lb_index);
				if low >= 0 {
					storage.storage[low as usize].val
				} else {
					*self.domain.lower_bound().unwrap()
				}
			}
		}
	}

	/// Returns the boolean view associated with the lower bound of the variable
	/// being this value.
	pub(crate) fn get_lower_bound_lit(&self, trail: &impl TrailingActions) -> BoolView {
		match &self.order_encoding {
			OrderStorage::Eager {
				lower_bound,
				storage,
				..
			} => {
				let lb = trail.get_trailed_int(*lower_bound);
				BoolView(if lb == *self.domain.lower_bound().unwrap() {
					BoolViewInner::Const(true)
				} else {
					let DomainLocation { offset, .. } = OrderStorage::resolve_val(&self.domain, lb);
					BoolViewInner::Lit(!storage.index(offset))
				})
			}
			OrderStorage::Lazy(storage) => {
				let lb_index = trail.get_trailed_int(storage.lb_index);
				BoolView(if lb_index >= 0 {
					BoolViewInner::Lit(!storage[lb_index as u32].var)
				} else {
					BoolViewInner::Const(true)
				})
			}
		}
	}

	/// Returns the upper bound of the current state of the integer variable.
	pub(crate) fn get_upper_bound(&self, trail: &impl TrailingActions) -> IntVal {
		trail.get_trailed_int(self.upper_bound)
	}

	/// Returns the boolean view associated with the upper bound of the variable
	/// being this value.
	pub(crate) fn get_upper_bound_lit(&self, trail: &impl TrailingActions) -> BoolView {
		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let ub = trail.get_trailed_int(self.upper_bound);
				BoolView(if ub == *self.domain.upper_bound().unwrap() {
					BoolViewInner::Const(true)
				} else {
					let DomainLocation { offset, .. } =
						OrderStorage::resolve_val(&self.domain, ub + 1);
					BoolViewInner::Lit(storage.index(offset).into())
				})
			}
			OrderStorage::Lazy(storage) => {
				let ub_index = trail.get_trailed_int(storage.ub_index);
				BoolView(if ub_index >= 0 {
					BoolViewInner::Lit(storage[ub_index as u32].var.into())
				} else {
					BoolViewInner::Const(true)
				})
			}
		}
	}

	/// Returns the meaning of a literal in the context of this integer
	/// variable.
	///
	/// # Warning
	///
	/// This method can only be used with literals that were eagerly created for
	/// this integer variable. Lazy literals should be mapped using
	/// [`BoolToIntMap`].
	pub(crate) fn lit_meaning(&self, lit: RawLit) -> IntLitMeaning {
		let var = lit.var();
		let ret = |l: IntLitMeaning| {
			if lit.is_negated() {
				!l
			} else {
				l
			}
		};

		let OrderStorage::Eager { storage, .. } = &self.order_encoding else {
			unreachable!("lit_meaning called on non-eager variable")
		};
		if storage.contains(&var) {
			let mut offset = storage.find(var).unwrap() as IntVal + 1; // +1 because first value is not encoded
			for r in self.domain.iter() {
				let r_len = r.end() - r.start() + 1;
				if offset < r_len {
					return ret(IntLitMeaning::Less(*r.start() + offset));
				} else if offset == r_len && !lit.is_negated() {
					return IntLitMeaning::Less(*r.start() + offset);
				}
				offset -= r_len;
			}
			unreachable!()
		}
		let DirectStorage::Eager(vars) = &self.direct_encoding else {
			unreachable!("lit_meaning called on non-eager variable")
		};
		debug_assert!(vars.contains(&var));
		let mut offset = vars.find(var).unwrap() as IntVal + 1;
		for r in self.domain.iter() {
			let r_len = r.end() - r.start() + 1;
			if offset < r_len {
				return ret(IntLitMeaning::Eq(*r.start() + offset));
			}
			offset -= r_len;
		}
		unreachable!()
	}

	/// Create a new integer variable within the given solver, which the given
	/// domain. The `order_encoding` and `direct_encoding` parameters determine
	/// whether literals to reason about the integer variables are created
	/// eagerly or lazily.
	pub(crate) fn new_in<Oracle: ExternalPropagation>(
		slv: &mut Solver<Oracle>,
		domain: IntSetVal,
		order_encoding: EncodingType,
		direct_encoding: EncodingType,
	) -> IntView {
		let orig_domain_len = domain.card();
		assert_ne!(
			orig_domain_len,
			Some(0),
			"Unable to create integer variable empty domain"
		);
		if orig_domain_len == Some(1) {
			return IntView(IntViewInner::Const(*domain.lower_bound().unwrap()));
		}
		let lb = *domain.lower_bound().unwrap();
		let ub = *domain.upper_bound().unwrap();
		if orig_domain_len == Some(2) {
			let lit = slv.oracle.new_lit();
			return IntView(IntViewInner::Bool {
				transformer: LinearTransform {
					scale: NonZeroIntVal::new(ub - lb).unwrap(),
					offset: lb,
				},
				lit,
			});
		}
		debug_assert!(
			direct_encoding != EncodingType::Eager || order_encoding == EncodingType::Eager
		);

		let mut engine = slv.engine.borrow_mut();
		let upper_bound = engine.state.trail.track_int(ub);
		let order_encoding = match order_encoding {
			EncodingType::Eager => OrderStorage::Eager {
				lower_bound: engine.state.trail.track_int(lb),
				storage: slv.oracle.new_var_range(
					orig_domain_len.expect(
						"unable to create literals eagerly for domains that exceed usize::MAX",
					) - 1,
				),
			},
			EncodingType::Lazy => OrderStorage::Lazy(LazyOrderStorage {
				min_index: 0,
				max_index: 0,
				lb_index: engine.state.trail.track_int(-1),
				ub_index: engine.state.trail.track_int(-1),
				storage: Vec::default(),
			}),
		};
		let direct_encoding =
			match direct_encoding {
				EncodingType::Eager => DirectStorage::Eager(slv.oracle.new_var_range(
					orig_domain_len.expect(
						"unable to create literals eagerly for domains that exceed usize::MAX",
					) - 2,
				)),
				EncodingType::Lazy => DirectStorage::Lazy(FxHashMap::default()),
			};
		// Drop engine to allow oracle interaction
		drop(engine);

		// Enforce consistency constraints for eager literals
		if let OrderStorage::Eager { storage, .. } = &order_encoding {
			let mut direct_enc_iter = if let DirectStorage::Eager(vars) = &direct_encoding {
				Some(*vars)
			} else {
				None
			}
			.into_iter()
			.flatten();
			for (ord_i, ord_j) in (*storage).tuple_windows() {
				let ord_i: RawLit = ord_i.into(); // x<i
				let ord_j: RawLit = ord_j.into(); // x<j, where j = i + n and n≥1
				slv.oracle.add_clause([!ord_i, ord_j]).unwrap(); // x<i -> x<(i+n)
				if matches!(direct_encoding, DirectStorage::Eager(_)) {
					let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
					slv.oracle.add_clause([!eq_i, !ord_i]).unwrap(); // x=i -> x≥i
					slv.oracle.add_clause([!eq_i, ord_j]).unwrap(); // x=i -> x<(i+n)
					slv.oracle.add_clause([eq_i, ord_i, !ord_j]).unwrap(); // x≠i -> (x<i \/
					                                        // x≥(i+n))
				}
			}
			debug_assert!(direct_enc_iter.next().is_none());
		}

		// Create the resulting integer variable
		let mut engine = slv.engine.borrow_mut();
		let iv = engine.state.int_vars.push(Self {
			direct_encoding,
			domain,
			order_encoding,
			upper_bound,
		});
		// Create propagator activation list
		let r = engine.state.int_activation.push(Default::default());
		debug_assert_eq!(iv, r);

		// Setup the boolean to integer mapping
		if let OrderStorage::Eager { storage, .. } = engine.state.int_vars[iv].order_encoding {
			let mut vars = storage;
			if let DirectStorage::Eager(vars2) = &engine.state.int_vars[iv].direct_encoding {
				debug_assert_eq!(Into::<i32>::into(vars.end()) + 1, vars2.start().into());
				vars = VarRange::new(vars.start(), vars2.end());
			}
			engine.state.bool_to_int.insert_eager(vars, iv);
			engine
				.state
				.trail
				.grow_to_boolvar(vars.clone().next_back().unwrap());
			for l in vars {
				slv.oracle.add_observed_var(l);
			}
		}

		IntView(IntViewInner::VarRef(iv))
	}

	/// Notify that a new lower bound has been propagated for the variable,
	/// returning the previous lower bound.
	///
	/// # Warning
	///
	/// This method assumes the literal for the new lower bound has been created
	/// (and propagated).
	pub(crate) fn notify_lower_bound<T>(&mut self, trail: &mut T, val: IntVal)
	where
		T: TrailingActions,
		RawLit: BoolInspectionActions<T>,
	{
		debug_assert!(self.domain.contains(&val));
		debug_assert!(val > self.get_lower_bound(trail));
		match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => {
				let _ = trail.set_trailed_int(*lower_bound, val);
			}
			OrderStorage::Lazy(
				storage @ LazyOrderStorage {
					min_index,
					lb_index,
					..
				},
			) => {
				let cur_index = trail.get_trailed_int(*lb_index);
				let cur_index = if cur_index < 0 {
					*min_index
				} else {
					cur_index as u32
				};
				debug_assert!(storage[cur_index].val <= val);
				let new_index = storage.find_index(cur_index, SearchDirection::Increasing, val);
				debug_assert_eq!(storage[new_index].val, val);
				let old_index = trail.set_trailed_int(*lb_index, new_index as IntVal);
				debug_assert!(old_index < 0 || cur_index == old_index as u32);
			}
		}
	}

	/// Notify that a new upper bound has been propagated for the variable,
	/// returning the previous upper bound.
	///
	/// # Warning
	///
	/// This method assumes the literal for the new upper bound has been created
	/// (and propagated).
	pub(crate) fn notify_upper_bound(&mut self, trail: &mut impl TrailingActions, val: IntVal) {
		debug_assert!(self.domain.contains(&val));
		debug_assert!(val < self.get_upper_bound(trail));
		let _ = trail.set_trailed_int(self.upper_bound, val);
		if let OrderStorage::Lazy(
			storage @ LazyOrderStorage {
				max_index,
				ub_index,
				..
			},
		) = &self.order_encoding
		{
			let DomainLocation {
				greater_eq_val: val,
				..
			} = OrderStorage::resolve_val(&self.domain, val + 1);
			let cur_index = trail.get_trailed_int(*ub_index);
			let cur_index = if cur_index < 0 {
				*max_index
			} else {
				cur_index as u32
			};
			let new_index = storage.find_index(cur_index, SearchDirection::Decreasing, val);
			debug_assert_eq!(storage[new_index].val, val);
			let old_index = trail.set_trailed_int(*ub_index, new_index as IntVal);
			debug_assert!(old_index < 0 || cur_index == old_index as u32);
		}
	}

	/// Method used to strengthen the meaning of a [`LitMeaning::Less`] literal
	/// when possible through gaps in the domain.
	pub(crate) fn tighten_less_lit(&self, val: IntVal) -> IntVal {
		let ranges = self.domain.iter();
		if ranges.len() == 1 {
			debug_assert!(self.domain.contains(&(val - 1)));
			return val;
		}
		let range = ranges.rev().find(|r| *r.start() < val).unwrap();
		if val > *range.end() {
			*range.end() + 1
		} else {
			val
		}
	}
}

impl LazyOrderStorage {
	/// Find the the index of the node that contains the value or the node
	/// "before" the value.
	fn find_index(&self, start: u32, direction: SearchDirection, val: IntVal) -> u32 {
		let mut i = start;
		match direction {
			SearchDirection::Increasing => {
				while self[i].has_next && self[self[i].next].val <= val {
					i = self[i].next;
				}
			}
			SearchDirection::Decreasing => {
				while self[i].has_prev && self[self[i].prev].val >= val {
					i = self[i].prev;
				}
			}
		}
		i
	}

	/// Returns `true` if the storage is empty, `false` otherwise.
	fn is_empty(&self) -> bool {
		self.storage.is_empty()
	}

	/// Returns the node with the maximum [`OrderNode::val`] present in the
	/// storage, or [`None`] if the storage is empty.
	fn max(&self) -> Option<&OrderNode> {
		if self.is_empty() {
			None
		} else {
			Some(&self[self.max_index])
		}
	}

	/// Returns the node with the minimum [`OrderNode::val`] present in the
	/// storage, or [`None`] if the storage is empty.
	fn min(&self) -> Option<&OrderNode> {
		if self.is_empty() {
			None
		} else {
			Some(&self[self.min_index])
		}
	}
}

impl Index<u32> for LazyOrderStorage {
	type Output = OrderNode;

	fn index(&self, index: u32) -> &Self::Output {
		&self.storage[index as usize]
	}
}

impl IndexMut<u32> for LazyOrderStorage {
	fn index_mut(&mut self, index: u32) -> &mut Self::Output {
		&mut self.storage[index as usize]
	}
}

impl OrderEntry<'_> {
	/// Forward the entry to the entry for next value in the domain.
	///
	/// Note that it is assumed that a next value exists in the domain, and this
	/// method will panic otherwise.
	fn next_value(self) -> Self {
		match self {
			OrderEntry::Eager(vars, offset) => OrderEntry::Eager(vars, offset + 1),
			OrderEntry::Occupied {
				storage,
				index,
				mut range_iter,
			} => {
				let next = storage[index].val + 1;
				let next = if range_iter.peek().unwrap().contains(&next) {
					next
				} else {
					let _ = range_iter.next().unwrap();
					*range_iter.peek().unwrap().start()
				};
				let next_index = storage[index].next;
				if storage[index].has_next && storage[next_index].val == next {
					OrderEntry::Occupied {
						storage,
						index: next_index,
						range_iter,
					}
				} else {
					OrderEntry::Vacant {
						storage,
						prev_index: index as IntVal,
						range_iter,
						val: next,
					}
				}
			}
			OrderEntry::Vacant {
				storage,
				prev_index,
				mut range_iter,
				val,
			} => {
				let next = val + 1;
				let next = if range_iter.peek().unwrap().contains(&next) {
					next
				} else {
					let _ = range_iter.next().unwrap();
					*range_iter.peek().unwrap().start()
				};
				if prev_index >= 0
					&& storage[prev_index as u32].has_next
					&& storage[storage[prev_index as u32].next].val == next
				{
					OrderEntry::Occupied {
						index: storage[prev_index as u32].next,
						storage,
						range_iter,
					}
				} else if !storage.is_empty() && storage.min().unwrap().val == next {
					OrderEntry::Occupied {
						index: storage.min_index,
						storage,
						range_iter,
					}
				} else {
					OrderEntry::Vacant {
						storage,
						prev_index,
						range_iter,
						val: next,
					}
				}
			}
		}
	}
	/// Extract the [`RawVar`] if the entry is occupied, or insert a new
	/// variable using the given function.
	///
	/// Note that the function is called with the integer value `i`, where the
	/// variable will represent `< i`, the previous variable before `i` and the
	/// variable after `i`, if they exist.
	fn or_insert_with(
		self,
		f: impl FnOnce(IntVal, Option<RawVar>, Option<RawVar>) -> RawVar,
	) -> (Self, RawVar) {
		match self {
			OrderEntry::Eager(vars, offset) => {
				// Lookup corresponding variable
				debug_assert!(
					offset < vars.len(),
					"var range offset, {}, must be in [0, {})",
					offset,
					vars.len(),
				);
				(self, vars.index(offset))
			}
			OrderEntry::Occupied {
				storage,
				index,
				range_iter,
			} => {
				let var = storage[index].var;
				(
					OrderEntry::Occupied {
						storage,
						index,
						range_iter,
					},
					var,
				)
			}
			OrderEntry::Vacant {
				storage,
				prev_index,
				mut range_iter,
				val,
			} => {
				// Determine the previous and next node
				let (prev, next) = if prev_index >= 0 {
					let prev = prev_index as u32;
					let next = if storage[prev].has_next {
						Some(storage[prev].next)
					} else {
						None
					};
					(Some(prev), next)
				} else if !storage.is_empty() {
					(None, Some(storage.min_index))
				} else {
					(None, None)
				};
				// Value should have been resolved and now be in the domain
				debug_assert!(range_iter.peek().unwrap().contains(&val));
				// Call function and insert new node
				let var = f(
					val,
					prev.map(|i| storage[i].var),
					next.map(|i| storage[i].var),
				);
				storage.storage.push(OrderNode {
					val,
					var,
					has_prev: prev.is_some(),
					prev: prev.unwrap_or(0),
					has_next: next.is_some(),
					next: next.unwrap_or(0),
				});
				let index = (storage.storage.len() - 1) as u32;
				if let Some(prev) = prev {
					debug_assert!(storage[prev].val < storage.storage.last().unwrap().val);
					storage[prev].has_next = true;
					storage[prev].next = index;
				} else {
					storage.min_index = index;
				}
				if let Some(next) = next {
					debug_assert!(storage[next].val > storage.storage.last().unwrap().val);
					storage[next].has_prev = true;
					storage[next].prev = index;
				} else {
					storage.max_index = index;
				}

				// Return the new entry
				(
					OrderEntry::Occupied {
						index: storage.storage.len() as u32 - 1,
						storage,
						range_iter,
					},
					var,
				)
			}
		}
	}
}

impl OrderStorage {
	/// Locate the position in the [`OrderStorage`] that would be used to store
	/// the representation of the condition `< i`. The method will return a
	/// [`OrderEntry`] object that can be used to access the condition as a
	/// [`RawVar`] if it already exists, or insert a new literal to represent
	/// the condition otherwise. In addition the function returns an `i` and
	/// `j`, such that `i` is the tightest value for which `< i` is equivalent
	/// to `< val` and `j` is the tightest value for which `≥ j` is equivalent
	/// to `≥ val`.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn entry<'a>(
		&'a mut self,
		domain: &'a RangeList<IntVal>,
		val: IntVal,
	) -> (OrderEntry<'a>, IntVal, IntVal) {
		let DomainLocation {
			less_val,
			greater_eq_val: val,
			offset,
			range_iter,
		} = Self::resolve_val(domain, val);

		let entry = match self {
			OrderStorage::Eager { storage, .. } => OrderEntry::Eager(storage, offset),
			OrderStorage::Lazy(storage) => {
				if storage.is_empty() || storage.min().unwrap().val > val {
					OrderEntry::Vacant {
						storage,
						prev_index: -1,
						range_iter,
						val,
					}
				} else if storage.max().unwrap().val < val {
					OrderEntry::Vacant {
						prev_index: storage.max_index as IntVal,
						storage,
						range_iter,
						val,
					}
				} else {
					let i = storage.find_index(storage.min_index, SearchDirection::Increasing, val);
					debug_assert!(storage[i].val <= val);
					if storage[i].val == val {
						OrderEntry::Occupied {
							storage,
							index: i,
							range_iter,
						}
					} else {
						OrderEntry::Vacant {
							storage,
							prev_index: i as IntVal,
							range_iter,
							val,
						}
					}
				}
			}
		};
		(entry, less_val, val)
	}

	/// Return the [`RawVar`] that represent the condition `< val`, or `≥ val`
	/// if negated, if it already exists. In addition the function returns an
	/// `i` and `j`, such that `i` is the tightest value for which `< i` is
	/// equivalent to `< val` and `j` is the tightest value for which `≥ j` is
	/// equivalent to `≥ val`.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn find(&self, domain: &RangeList<IntVal>, val: IntVal) -> Option<(RawVar, IntVal, IntVal)> {
		let DomainLocation {
			less_val,
			greater_eq_val: val,
			offset,
			..
		} = Self::resolve_val(domain, val);

		let var = match self {
			OrderStorage::Eager { storage, .. } => Some(storage.index(offset)),
			OrderStorage::Lazy(storage) => {
				if storage.is_empty()
					|| storage.min().unwrap().val > val
					|| storage.max().unwrap().val < val
				{
					return None;
				}

				let i = storage.find_index(storage.min_index, SearchDirection::Increasing, val);
				if storage[i].val == val {
					Some(storage[i].var)
				} else {
					None
				}
			}
		}?;
		Some((var, less_val, val))
	}

	#[inline]
	/// Returns the lowest integer value `j`, for which `< i` is equivalent to
	/// `< j` in the given `domain. In addition it returns the index of the
	/// range in `domain` in which `j` is located, and calculate the offset of
	/// the representation `< j` in a VarRange when the order literals are
	/// eagerly created.
	fn resolve_val(domain: &RangeList<IntVal>, val: IntVal) -> DomainLocation<'_> {
		let mut offset = -1; // -1 to account for the lower bound
		let mut it = domain.iter().peekable();
		let mut last_val = IntVal::MIN;
		loop {
			let r = it.peek().unwrap();
			if val < *r.start() {
				return DomainLocation {
					less_val: last_val + 1,
					greater_eq_val: *r.start(),
					offset: offset as usize,
					range_iter: it,
				};
			} else if val <= *r.end() {
				offset += val - r.start();
				return DomainLocation {
					less_val: if val == *r.start() { last_val + 1 } else { val },
					greater_eq_val: val,
					offset: offset as usize,
					range_iter: it,
				};
			} else {
				offset += r.end() - r.start() + 1;
			}
			last_val = *it.next().unwrap().end();
		}
	}
}

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

#[cfg(test)]
mod tests {
	use std::{iter::once, num::NonZeroI32};

	use itertools::Itertools;
	use pindakaas::Lit as RawLit;
	use rangelist::RangeList;

	use crate::{
		actions::{IntDecisionActions, IntExplanationActions, IntInspectionActions},
		solver::{
			int_var::{EncodingType, IntVar, IntVarRef},
			BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner,
		},
		Solver,
	};

	fn assert_eager_lits_eq(
		iv: &mut IntVar,
		input: impl IntoIterator<Item = IntLitMeaning>,
		lits: impl IntoIterator<Item = BoolView>,
		output: impl IntoIterator<Item = IntLitMeaning>,
	) {
		for (req, expected) in input.into_iter().zip_eq(lits.into_iter().zip_eq(output)) {
			let out = iv.get_bool_lit(req).expect("lit must be present");
			assert_eq!(out, expected, "given {req:?}");
			let out = iv.bool_lit(req, |_| panic!("all literals should be eagerly created"));
			assert_eq!(out, expected, "given {req:?}");
			if let BoolViewInner::Lit(l) = out.0 .0 {
				assert_eq!(iv.lit_meaning(l), expected.1);
			}
		}
	}

	fn assert_lazy_lits_eq(
		slv: &mut Solver,
		iv: IntVarRef,
		input: impl IntoIterator<Item = IntLitMeaning>,
		lits: impl IntoIterator<Item = BoolView>,
		output: impl IntoIterator<Item = IntLitMeaning>,
	) {
		let view = IntView(IntViewInner::VarRef(iv));
		for (req, expected) in input.into_iter().zip_eq(lits.into_iter().zip_eq(output)) {
			let bv = view.get_lit(slv, req);
			let m = view.get_lit_meaning(slv, bv).unwrap_or(req);
			assert_eq!((bv, m), expected, "given {req:?}");

			let v = &mut slv.engine.borrow_mut().state.int_vars[iv];
			let out = v.get_bool_lit(req).expect("lit must be present");
			assert_eq!(out, expected, "given {req:?}");
		}
	}

	#[test]
	fn eager_continuous_lits() {
		use IntLitMeaning::*;

		let mut slv: Solver = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from(1..=4),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &mut slv.engine.borrow_mut().state.int_vars[a];
		assert_eager_lits_eq(
			a,
			(0..=6).map(Less),
			vec![BoolView::from(false); 2]
				.into_iter()
				.chain(vec![1, 2, 3].into_iter().map(into_lit))
				.chain(vec![BoolView::from(true); 2]),
			(0..=6).map(Less),
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(GreaterEq),
			vec![BoolView::from(true); 2]
				.into_iter()
				.chain(vec![-1, -2, -3].into_iter().map(into_lit))
				.chain(vec![BoolView::from(false); 2]),
			(0..=6).map(GreaterEq),
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(Eq),
			once(BoolView::from(false))
				.chain(vec![1, 4, 5, -3].into_iter().map(into_lit))
				.chain(vec![BoolView::from(false); 2]),
			vec![Eq(0), Less(2), Eq(2), Eq(3), GreaterEq(4), Eq(5), Eq(6)],
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(NotEq),
			once(BoolView::from(true))
				.chain(vec![-1, -4, -5, 3].into_iter().map(into_lit))
				.chain(vec![BoolView::from(true); 2]),
			vec![
				NotEq(0),
				GreaterEq(2),
				NotEq(2),
				NotEq(3),
				Less(4),
				NotEq(5),
				NotEq(6),
			],
		);
	}

	#[test]
	fn eager_gaps_lits() {
		use IntLitMeaning::*;

		let mut slv: Solver = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3, 8..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &mut slv.engine.borrow_mut().state.int_vars[a];
		assert_eager_lits_eq(
			a,
			(2..=10).map(Less),
			vec![1, 2, 3, 3, 3, 3, 3, 4, 5].into_iter().map(into_lit),
			vec![
				Less(2),
				Less(3),
				Less(4),
				Less(4),
				Less(4),
				Less(4),
				Less(4),
				Less(9),
				Less(10),
			],
		);
		assert_eager_lits_eq(
			a,
			(2..=10).map(GreaterEq),
			vec![-1, -2, -3, -3, -3, -3, -3, -4, -5]
				.into_iter()
				.map(into_lit),
			vec![
				GreaterEq(2),
				GreaterEq(3),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(9),
				GreaterEq(10),
			],
		);
		assert_eager_lits_eq(
			a,
			(1..=10).map(Eq),
			vec![1, 6, 7]
				.into_iter()
				.map(into_lit)
				.chain(vec![BoolView::from(false); 4])
				.chain(vec![8, 9, -5].into_iter().map(into_lit)),
			once(Less(2))
				.chain((2..=9).map(Eq))
				.chain(once(GreaterEq(10))),
		);
		assert_eager_lits_eq(
			a,
			(1..=10).map(NotEq),
			vec![-1, -6, -7]
				.into_iter()
				.map(into_lit)
				.chain(vec![BoolView::from(true); 4])
				.chain(vec![-8, -9, 5].into_iter().map(into_lit)),
			once(GreaterEq(2))
				.chain((2..=9).map(NotEq))
				.chain(once(Less(10))),
		);
	}

	fn into_lit(i: i32) -> BoolView {
		BoolView(BoolViewInner::Lit(RawLit::from_raw(
			NonZeroI32::new(i).unwrap(),
		)))
	}

	#[test]
	fn lazy_gaps_lits() {
		use IntLitMeaning::*;

		let mut slv: Solver = Solver::default();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3, 8..=10]),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		assert_lazy_lits_eq(
			&mut slv,
			a,
			(2..=10).map(Less),
			vec![1, 2, 3, 3, 3, 3, 3, 4, 5].into_iter().map(into_lit),
			vec![
				Less(2),
				Less(3),
				Less(4),
				Less(4),
				Less(4),
				Less(4),
				Less(4),
				Less(9),
				Less(10),
			],
		);
		assert_lazy_lits_eq(
			&mut slv,
			a,
			(2..=10).map(GreaterEq),
			vec![-1, -2, -3, -3, -3, -3, -3, -4, -5]
				.into_iter()
				.map(into_lit),
			vec![
				GreaterEq(2),
				GreaterEq(3),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(8),
				GreaterEq(9),
				GreaterEq(10),
			],
		);
		assert_lazy_lits_eq(
			&mut slv,
			a,
			(1..=10).map(Eq),
			vec![1, 6, 7]
				.into_iter()
				.map(into_lit)
				.chain(vec![BoolView::from(false); 4])
				.chain(vec![8, 9, -5].into_iter().map(into_lit)),
			once(Less(2))
				.chain((2..=9).map(Eq))
				.chain(once(GreaterEq(10))),
		);
		assert_lazy_lits_eq(
			&mut slv,
			a,
			(1..=10).map(NotEq),
			vec![-1, -6, -7]
				.into_iter()
				.map(into_lit)
				.chain(vec![BoolView::from(true); 4])
				.chain(vec![-8, -9, 5].into_iter().map(into_lit)),
			once(GreaterEq(2))
				.chain((2..=9).map(NotEq))
				.chain(once(Less(10))),
		);
	}
}
