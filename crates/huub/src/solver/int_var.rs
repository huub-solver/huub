//! Module containing the representation of integer variables within the solver.

use std::{
	collections::{
		hash_map::{self, VacantEntry},
		HashMap,
	},
	iter::{Map, Peekable},
	ops::{Index, IndexMut, RangeBounds, RangeInclusive},
};

use itertools::Itertools;
use pindakaas::{
	solver::propagation::PropagatingSolver, ClauseDatabaseTools, Lit as RawLit, Var as RawVar,
	VarRange,
};
use rangelist::{IntervalIterator, RangeList};

use crate::{
	actions::TrailingActions,
	solver::{
		engine::Engine, trail::TrailedInt, BoolView, BoolViewInner, IntLitMeaning, IntView,
		IntViewInner,
	},
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
	/// Variables for all equality conditions are eagerly created and stored in order
	Eager(VarRange),
	/// Variables for equality conditions are lazily created and stored in a hashmap
	Lazy(HashMap<IntVal, RawVar>),
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
	/// - if `meaning` is `LitMeaning::Less(j)`, then `prev` contains the literal
	///   `< i` where `i` is the value right before `j` in the storage.
	/// - if `meaning` is `LitMeaning::Eq(k)`, then `prev` contains the literal
	///   `<j`.
	pub(crate) prev: Option<RawVar>,
	/// The variable that represent the literal `< k` where `k` is the value right
	/// after the value represented by the literal.
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
		/// An iterator pointing at the range in the domain in which the value of
		/// which the value of the entry is part.
		range_iter: RangeIter<'a>,
	},
	/// Entry does not exist and can be lazily created.
	Vacant {
		/// Reference to the storage where the new entry will be created.
		storage: &'a mut LazyOrderStorage,
		/// The index of the node that contains the value right before the new entry
		/// that will be created.
		prev_index: IntVal,
		/// An iterator pointing at the range in the domain in which the value of
		/// which the value of the new entry is part.
		range_iter: RangeIter<'a>,
		/// The value for which the entry will be created.
		val: IntVal,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Type useed to store individual entries in [`LazyOrderStorage`].
pub(crate) struct OrderNode {
	/// The value for which `var` represents `x < val`.
	val: IntVal,
	/// The variable representing `x < val`.
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
	/// Variables for all inequality conditions are eagerly created and stored in
	/// order.
	Eager {
		/// A trailed integer that represents the currently lower bound of the
		/// variable.
		lower_bound: TrailedInt,
		/// The range of Boolean variables that represent the inequality conditions.
		storage: VarRange,
	},
	/// Variables for inequality conditions are lazily created and specialized
	/// noded structure, a [`LazyOrderStorage`].
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
			DirectStorage::Lazy(map) => map.get(&i).map(|v| BoolViewInner::Lit((*v).into())),
		}
	}
}

impl IntVar {
	/// Access the Boolean literal with the given meaning, creating it if it is
	/// not yet available.
	pub(crate) fn bool_lit(
		&mut self,
		bv: IntLitMeaning,
		mut new_var: impl FnMut(LazyLitDef) -> RawVar,
	) -> BoolView {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();
		let (bv, negate) = self.normalize_lit_meaning(bv, lb, ub);

		let bv = BoolView(match bv {
			IntLitMeaning::Less(i) if i <= lb => BoolViewInner::Const(false),
			IntLitMeaning::Less(i) if i > ub => BoolViewInner::Const(true),
			IntLitMeaning::Less(i) => BoolViewInner::Lit(
				self.order_encoding
					.entry(&self.domain, i)
					.or_insert_with(|val, prev, next| {
						new_var(LazyLitDef {
							meaning: IntLitMeaning::Less(val),
							prev,
							next,
						})
					})
					.1
					.into(),
			),
			IntLitMeaning::Eq(i) if i < lb || i > ub => BoolViewInner::Const(false),
			IntLitMeaning::Eq(i) => {
				self.direct_encoding
					.entry(&self.domain, i)
					.or_insert_with(|| {
						let (entry, prev) = self
							.order_encoding
							.entry(&self.domain, i)
							.or_insert_with(|val, prev, next| {
								new_var(LazyLitDef {
									meaning: IntLitMeaning::Less(val),
									prev,
									next,
								})
							});
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
					})
			}
			_ => unreachable!(),
		});

		if negate {
			!bv
		} else {
			bv
		}
	}

	/// Try and find an (already) existing Boolean literal with the given meaning
	pub(crate) fn get_bool_lit(&self, bv: IntLitMeaning) -> Option<BoolView> {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();
		let (bv, negate) = self.normalize_lit_meaning(bv, lb, ub);

		let bv = BoolView(match bv {
			IntLitMeaning::Less(i) if i <= lb => BoolViewInner::Const(false),
			IntLitMeaning::Less(i) if i > ub => BoolViewInner::Const(true),
			IntLitMeaning::Less(i) => self
				.order_encoding
				.find(&self.domain, i)
				.map(|v| BoolViewInner::Lit(v.into()))?,
			IntLitMeaning::Eq(i) if i < lb || i > ub => BoolViewInner::Const(false),
			IntLitMeaning::Eq(i) => self.direct_encoding.find(&self.domain, i)?,
			_ => unreachable!(),
		});
		if negate { !bv } else { bv }.into()
	}

	/// Returns the lower and upper bounds of the current state of the integer variable.
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

	/// Returns the boolean view associated with `≥ v` if it exists or weaker version otherwise.
	///
	/// ## Warning
	/// This function assumes that `v <= lb`.
	pub(crate) fn get_greater_eq_lit_or_weaker(
		&self,
		trail: &impl TrailingActions,
		v: IntVal,
	) -> (BoolView, IntVal) {
		debug_assert!(v <= self.get_lower_bound(trail));
		if v <= *self.domain.lower_bound().unwrap() {
			return (BoolView(BoolViewInner::Const(true)), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let (_, offset, _) = OrderStorage::resolve_val(&self.domain, v);
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
					if let Some(v) = trail.get_bool_val(lit) {
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

	/// Returns the boolean view associated with `< v` if it exists or weaker version otherwise.
	///
	/// ## Warning
	/// This function assumes that `v >= ub`.
	pub(crate) fn get_less_lit_or_weaker(
		&self,
		trail: &impl TrailingActions,
		v: IntVal,
	) -> (BoolView, IntVal) {
		debug_assert!(v >= self.get_upper_bound(trail));
		if v > *self.domain.upper_bound().unwrap() {
			return (BoolView(BoolViewInner::Const(true)), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let (_, offset, _) = OrderStorage::resolve_val(&self.domain, v);
				(
					BoolView(BoolViewInner::Lit(storage.index(offset).into())),
					v,
				)
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
					if let Some(v) = trail.get_bool_val(lit) {
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
	pub(crate) fn get_lower_bound(&self, trail: &impl TrailingActions) -> IntVal {
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

	/// Returns the boolean view associated with the lower bound of the variable being this value.
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
					let (_, offset, _) = OrderStorage::resolve_val(&self.domain, lb);
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

	/// Returns the boolean view associated with the upper bound of the variable being this value.
	pub(crate) fn get_upper_bound_lit(&self, trail: &impl TrailingActions) -> BoolView {
		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let ub = trail.get_trailed_int(self.upper_bound);
				BoolView(if ub == *self.domain.upper_bound().unwrap() {
					BoolViewInner::Const(true)
				} else {
					let (_, offset, _) = OrderStorage::resolve_val(&self.domain, ub + 1);
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

	/// Returns the meaning of a literal in the context of this integer variable.
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
	/// whether literals to reason about the integer variables are created eagerly
	/// or lazily.
	pub(crate) fn new_in<Oracle: PropagatingSolver<Engine>>(
		slv: &mut Solver<Oracle>,
		domain: IntSetVal,
		order_encoding: EncodingType,
		direct_encoding: EncodingType,
	) -> IntView {
		let orig_domain_len = domain.card();
		assert!(
			orig_domain_len != 0,
			"Unable to create integer variable empty domain"
		);
		if orig_domain_len == 1 {
			return IntView(IntViewInner::Const(*domain.lower_bound().unwrap()));
		}
		let lb = *domain.lower_bound().unwrap();
		let ub = *domain.upper_bound().unwrap();
		if orig_domain_len == 2 {
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

		let upper_bound = slv.engine_mut().state.trail.track_int(ub);
		let order_encoding = match order_encoding {
			EncodingType::Eager => OrderStorage::Eager {
				lower_bound: slv.engine_mut().state.trail.track_int(lb),
				storage: slv.oracle.new_var_range(orig_domain_len - 1),
			},
			EncodingType::Lazy => OrderStorage::Lazy(LazyOrderStorage {
				min_index: 0,
				max_index: 0,
				lb_index: slv.engine_mut().state.trail.track_int(-1),
				ub_index: slv.engine_mut().state.trail.track_int(-1),
				storage: Vec::default(),
			}),
		};
		let direct_encoding = match direct_encoding {
			EncodingType::Eager => {
				DirectStorage::Eager(slv.oracle.new_var_range(orig_domain_len - 2))
			}
			EncodingType::Lazy => DirectStorage::Lazy(HashMap::default()),
		};

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
					slv.oracle.add_clause([eq_i, ord_i, !ord_j]).unwrap(); // x≠i -> (x<i \/ x≥(i+n))
				}
			}
			debug_assert!(direct_enc_iter.next().is_none());
		}

		// Create the resulting integer variable
		let iv = slv.engine_mut().state.int_vars.push(Self {
			direct_encoding,
			domain,
			order_encoding,
			upper_bound,
		});
		// Create propagator activation list
		let r = slv
			.engine_mut()
			.state
			.int_activation
			.push(Default::default());
		debug_assert_eq!(iv, r);

		// Setup the boolean to integer mapping
		if let OrderStorage::Eager { storage, .. } = slv.engine().state.int_vars[iv].order_encoding
		{
			let mut vars = storage;
			if let DirectStorage::Eager(vars2) = &slv.engine().state.int_vars[iv].direct_encoding {
				debug_assert_eq!(Into::<i32>::into(vars.end()) + 1, vars2.start().into());
				vars = VarRange::new(vars.start(), vars2.end());
			}
			slv.engine_mut().state.bool_to_int.insert_eager(vars, iv);
			slv.engine_mut()
				.state
				.trail
				.grow_to_boolvar(vars.clone().next_back().unwrap());
			for l in vars {
				slv.oracle.add_observed_var(l);
			}
		}

		IntView(IntViewInner::VarRef(iv))
	}

	#[inline]
	/// Method used to normalize a [`LitMeaning`] to find perform a lookup.
	///
	/// This method will replace any [`LitMeaning::Eq`] or [`LitMeaning::NotEq`]
	/// meaning asking for the global lower or upper bound with the appropriate
	/// [`LitMeaning::Less`] meaning. It will also negate any
	/// [`LitMeaning::NotEq`] and [`LitMeaning::GreaterEq`] and return a boolean
	/// indicating if the meaning was negated.
	fn normalize_lit_meaning(
		&self,
		mut lit: IntLitMeaning,
		lb: IntVal,
		ub: IntVal,
	) -> (IntLitMeaning, bool) {
		let mut negate = false;
		match lit {
			IntLitMeaning::Eq(i) | IntLitMeaning::NotEq(i) if i == lb => {
				negate = matches!(lit, IntLitMeaning::NotEq(_));
				lit = IntLitMeaning::Less(lb + 1);
			}
			IntLitMeaning::Eq(i) | IntLitMeaning::NotEq(i) if i == ub => {
				negate = matches!(lit, IntLitMeaning::Eq(_));
				lit = IntLitMeaning::Less(ub);
			}
			IntLitMeaning::GreaterEq(_) | IntLitMeaning::NotEq(_) => {
				lit = !lit;
				negate = true;
			}
			_ => {}
		}
		(lit, negate)
	}

	/// Notify that a new lower bound has been propagated for the variable,
	/// returning the previous lower bound.
	///
	/// # Warning
	///
	/// This method assumes the literal for the new lower bound has been created
	/// (and propagated).
	pub(crate) fn notify_lower_bound(
		&mut self,
		trail: &mut impl TrailingActions,
		val: IntVal,
	) -> IntVal {
		match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => trail.set_trailed_int(*lower_bound, val),
			OrderStorage::Lazy(
				storage @ LazyOrderStorage {
					min_index,
					lb_index,
					..
				},
			) => {
				let lb = *self.domain.lower_bound().unwrap();
				if val == lb {
					return lb;
				}
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
				if old_index < 0 {
					lb
				} else {
					storage[cur_index].val
				}
			}
		}
	}

	/// Notify that a new upper bound has been propagated for the variable,
	/// returning the previous upper bound.
	///
	/// # Warning
	///
	/// This method assumes the literal for the new upper bound has been created (and propagated).
	pub(crate) fn notify_upper_bound(
		&mut self,
		trail: &mut impl TrailingActions,
		val: IntVal,
	) -> IntVal {
		let prev_ub = trail.set_trailed_int(self.upper_bound, val);
		if prev_ub == val {
			return val;
		}
		if let OrderStorage::Lazy(
			storage @ LazyOrderStorage {
				max_index,
				ub_index,
				..
			},
		) = &self.order_encoding
		{
			let (val, _, _) = OrderStorage::resolve_val(&self.domain, val + 1);
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
		prev_ub
	}

	/// Method used to tighten the upper bound given when notified by a
	/// [`LitMeaning::Less`] literal.
	pub(crate) fn tighten_upper_bound(&self, val: IntVal) -> IntVal {
		let ranges = self.domain.iter();
		if ranges.len() == 1 {
			return val;
		}
		let range = ranges.rev().find(|r| val >= *r.start()).unwrap();
		if val > *range.end() {
			*range.end()
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
	/// [`RawVar`] if it already exists, or insert a new literal to represent the
	/// condition otherwise.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn entry<'a>(&'a mut self, domain: &'a RangeList<IntVal>, val: IntVal) -> OrderEntry<'a> {
		let (val, offset, range_iter) = Self::resolve_val(domain, val);

		match self {
			OrderStorage::Eager { storage, .. } => OrderEntry::Eager(storage, offset),
			OrderStorage::Lazy(storage) => {
				if storage.is_empty() || storage.min().unwrap().val > val {
					return OrderEntry::Vacant {
						storage,
						prev_index: -1,
						range_iter,
						val,
					};
				} else if storage.max().unwrap().val < val {
					return OrderEntry::Vacant {
						prev_index: storage.max_index as IntVal,
						storage,
						range_iter,
						val,
					};
				}

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
	}

	/// Return the [`RawVar`] that represent the condition `< i`, if it already
	/// exists.
	///
	/// The given `domain` is (in the case of eager creation) used to determine
	/// the offset of the variable in the `VarRange`.
	fn find(&self, domain: &RangeList<IntVal>, val: IntVal) -> Option<RawVar> {
		let (val, offset, _) = Self::resolve_val(domain, val);

		match self {
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
		}
	}
	/// Returns the lowest integer value `j`, for which `< i` is equivalent to `<
	/// j` in the given `domain. In addition it returns the index of the range in
	/// `domain` in which `j` is located, and calculate the offset of the
	/// representation `< j` in a VarRange when the order literals are eagerly
	/// created.
	fn resolve_val(domain: &RangeList<IntVal>, val: IntVal) -> (IntVal, usize, RangeIter) {
		let mut offset = -1; // -1 to account for the lower bound
		let mut it = domain.iter().peekable();
		let mut real_val = val;
		loop {
			let r = it.peek().unwrap();
			if val < *r.start() {
				real_val = *r.start();
				break;
			} else if r.contains(&val) {
				offset += val - r.start();
				break;
			} else {
				offset += r.end() - r.start() + 1;
			}
			let _ = it.next().unwrap();
		}
		(real_val, offset as usize, it)
	}
}

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

#[cfg(test)]
mod tests {
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;

	use crate::{
		solver::{
			int_var::{EncodingType, IntVar},
			BoolView, BoolViewInner, IntLitMeaning, IntView, IntViewInner,
		},
		Solver,
	};

	#[test]
	fn test_retrieve_lit() {
		let get_lit = |lit: BoolView| -> i32 {
			if let BoolView(BoolViewInner::Lit(lit)) = lit {
				lit.into()
			} else {
				unreachable!()
			}
		};
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from(1..=4),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &mut slv.engine_mut().state.int_vars[a];
		let lit = a.get_bool_lit(IntLitMeaning::Less(2)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(IntLitMeaning::GreaterEq(2)).unwrap();
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(IntLitMeaning::Less(3)).unwrap();
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(IntLitMeaning::Less(4)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(IntLitMeaning::GreaterEq(4)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(1)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(2)).unwrap();
		assert_eq!(get_lit(lit), 4);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(3)).unwrap();
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(4)).unwrap();
		assert_eq!(get_lit(lit), -3);

		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3, 8..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &mut slv.engine_mut().state.int_vars[a];
		let lit = a.get_bool_lit(IntLitMeaning::Less(2)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(IntLitMeaning::Less(3)).unwrap();
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(IntLitMeaning::Less(4)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(IntLitMeaning::GreaterEq(4)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(IntLitMeaning::Less(8)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(IntLitMeaning::GreaterEq(8)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(IntLitMeaning::Less(10)).unwrap();
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(IntLitMeaning::GreaterEq(10)).unwrap();
		assert_eq!(get_lit(lit), -5);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(1)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(2)).unwrap();
		assert_eq!(get_lit(lit), 6);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(3)).unwrap();
		assert_eq!(get_lit(lit), 7);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(8)).unwrap();
		assert_eq!(get_lit(lit), 8);
		let lit = a.get_bool_lit(IntLitMeaning::Eq(10)).unwrap();
		assert_eq!(get_lit(lit), -5);

		assert_eq!(
			a.get_bool_lit(IntLitMeaning::Less(11)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::GreaterEq(1)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::Less(1)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::GreaterEq(11)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(IntLitMeaning::Eq(0)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::Eq(11)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::Eq(5)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(IntLitMeaning::NotEq(0)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::NotEq(11)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(IntLitMeaning::NotEq(5)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
	}
}
