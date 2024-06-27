use std::{
	collections::{
		hash_map::{self, VacantEntry},
		HashMap,
	},
	iter::{Map, Peekable},
	ops::{Index, IndexMut, Not, RangeBounds, RangeInclusive},
};

use flatzinc_serde::RangeList;
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatingSolver, PropagatorAccess, Solver as SolverTrait, VarRange},
	Lit as RawLit, Valuation as SatValuation, Var as RawVar,
};

use crate::{
	actions::trailing::TrailingActions,
	solver::{
		engine::trail::TrailedInt,
		view::{BoolViewInner, IntViewInner},
		IntView, SatSolver,
	},
	BoolView, Clause, IntVal, LinearTransform, NonZeroIntVal, Solver,
};

/// A type to represent when certain literals are created
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EncodingType {
	/// The literal is created before solving starts
	Eager,
	/// The literal is created the first time it is mentioned
	Lazy,
}

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct IntVar {
	pub(crate) domain: RangeList<IntVal>,
	pub(crate) order_encoding: OrderStorage,
	pub(crate) direct_encoding: DirectStorage,
}

impl IntVar {
	pub(crate) fn new_in<Sol, Sat>(
		slv: &mut Solver<Sat>,
		domain: RangeList<IntVal>,
		order_encoding: EncodingType,
		direct_encoding: EncodingType,
	) -> IntView
	where
		Sol: PropagatorAccess + SatValuation,
		Sat: SatSolver + SolverTrait<ValueFn = Sol>,
	{
		let orig_domain_len: usize = domain
			.iter()
			.map(|x| (x.end() - x.start() + 1) as usize)
			.sum();
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
			let lit = slv.oracle.new_var().into();
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

		let order_encoding = match order_encoding {
			EncodingType::Eager => OrderStorage::Eager {
				lower_bound: slv.engine_mut().state.trail.track_int(lb),
				upper_bound: slv.engine_mut().state.trail.track_int(ub),
				storage: slv
					.oracle
					.next_var_range(orig_domain_len - 1)
					.expect("Boolean variable pool exhausted"),
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
			EncodingType::Eager => DirectStorage::Eager(
				slv.oracle
					.next_var_range(orig_domain_len - 2)
					.expect("Boolean variable pool exhausted"),
			),
			EncodingType::Lazy => DirectStorage::Lazy(HashMap::default()),
		};

		// Enforce consistency constraints for eager literals
		if let OrderStorage::Eager { storage, .. } = &order_encoding {
			let mut direct_enc_iter = if let DirectStorage::Eager(vars) = &direct_encoding {
				Some(vars.clone())
			} else {
				None
			}
			.into_iter()
			.flatten();
			for (ord_i, ord_j) in storage.clone().tuple_windows() {
				let ord_i: RawLit = ord_i.into();
				let ord_j: RawLit = ord_j.into();
				slv.oracle.add_clause([!ord_j, ord_i]).unwrap(); // ord_j -> ord_i
				if matches!(direct_encoding, DirectStorage::Eager(_)) {
					let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
					slv.oracle.add_clause([!eq_i, ord_i]).unwrap(); // eq_i -> ord_i
					slv.oracle.add_clause([!eq_i, !ord_j]).unwrap(); // eq_i -> !ord_j
					slv.oracle.add_clause([eq_i, !ord_i, ord_j]).unwrap(); // !eq_i -> !ord_i \/ ord_j
				}
			}
			debug_assert!(direct_enc_iter.next().is_none());
		}

		// Create the resulting integer variable
		let iv = slv.engine_mut().state.int_vars.push(Self {
			domain,
			order_encoding,
			direct_encoding,
		});

		// Setup the boolean to integer mapping
		if let OrderStorage::Eager { storage, .. } = &slv.engine().state.int_vars[iv].order_encoding
		{
			let mut vars = storage.clone();
			if let DirectStorage::Eager(vars2) = &slv.engine().state.int_vars[iv].direct_encoding {
				debug_assert_eq!(Into::<i32>::into(vars.end()) + 1, vars2.start().into());
				vars = VarRange::new(vars.start(), vars2.end());
			}
			slv.engine_mut()
				.state
				.bool_to_int
				.insert_eager(vars.clone(), iv);
			for l in vars {
				<Sat as PropagatingSolver>::add_observed_var(&mut slv.oracle, l);
			}
		}

		IntView(IntViewInner::VarRef(iv))
	}

	pub(crate) fn lit_meaning(&self, lit: RawLit) -> LitMeaning {
		let var = lit.var();
		let ret = |l: LitMeaning| {
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
					return ret(LitMeaning::GreaterEq(*r.start() + offset));
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
				return ret(LitMeaning::Eq(*r.start() + offset));
			}
			offset -= r_len;
		}
		unreachable!()
	}

	#[inline]
	fn normalize_lit_meaning(
		&self,
		mut lit: LitMeaning,
		lb: IntVal,
		ub: IntVal,
	) -> (LitMeaning, bool) {
		let mut negate = false;
		match lit {
			LitMeaning::Eq(i) | LitMeaning::NotEq(i) if i == lb => {
				negate = matches!(lit, LitMeaning::Eq(_));
				lit = LitMeaning::GreaterEq(lb + 1);
			}
			LitMeaning::Eq(i) | LitMeaning::NotEq(i) if i == ub => {
				negate = matches!(lit, LitMeaning::NotEq(_));
				lit = LitMeaning::GreaterEq(ub);
			}
			LitMeaning::Less(_) | LitMeaning::NotEq(_) => {
				lit = !lit;
				negate = true;
			}
			_ => {}
		}
		(lit, negate)
	}

	/// Access the Boolean literal with the given meaning, creating it if it is not yet available.
	pub(crate) fn bool_lit(
		&mut self,
		bv: LitMeaning,
		mut new_var: impl FnMut(LazyLitDef) -> RawVar,
	) -> BoolView {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();
		let (bv, negate) = self.normalize_lit_meaning(bv, lb, ub);

		let bv = BoolView(match bv {
			LitMeaning::GreaterEq(i) if i <= lb => BoolViewInner::Const(true),
			LitMeaning::GreaterEq(i) if i > ub => BoolViewInner::Const(false),
			LitMeaning::GreaterEq(i) => BoolViewInner::Lit(
				self.order_encoding
					.entry(&self.domain, i)
					.or_insert_with(|val, prev, next| {
						new_var(LazyLitDef {
							meaning: LitMeaning::GreaterEq(val),
							prev,
							next,
						})
					})
					.1
					.into(),
			),
			LitMeaning::Eq(i) if i < lb || i > ub => BoolViewInner::Const(false),
			LitMeaning::Eq(i) => self
				.direct_encoding
				.entry(&self.domain, i)
				.or_insert_with(|| {
					let (entry, prev) = self.order_encoding.entry(&self.domain, i).or_insert_with(
						|val, prev, next| {
							new_var(LazyLitDef {
								meaning: LitMeaning::GreaterEq(val),
								prev,
								next,
							})
						},
					);
					let next = entry
						.next_value()
						.or_insert_with(|val, prev, next| {
							new_var(LazyLitDef {
								meaning: LitMeaning::GreaterEq(val),
								prev,
								next,
							})
						})
						.1;
					new_var(LazyLitDef {
						meaning: LitMeaning::Eq(i),
						prev: Some(prev),
						next: Some(next),
					})
				}),
			_ => unreachable!(),
		});

		if negate {
			!bv
		} else {
			bv
		}
	}

	/// Try and find an (already) existing Boolean literal with the given meaning
	pub(crate) fn get_bool_lit(&self, bv: LitMeaning) -> Option<BoolView> {
		let lb = *self.domain.lower_bound().unwrap();
		let ub = *self.domain.upper_bound().unwrap();
		let (bv, negate) = self.normalize_lit_meaning(bv, lb, ub);

		let bv = BoolView(match bv {
			LitMeaning::GreaterEq(i) if i <= lb => BoolViewInner::Const(true),
			LitMeaning::GreaterEq(i) if i > ub => BoolViewInner::Const(false),
			LitMeaning::GreaterEq(i) => self
				.order_encoding
				.find(&self.domain, i)
				.map(|v| BoolViewInner::Lit(v.into()))?,
			LitMeaning::Eq(i) if i < lb || i > ub => BoolViewInner::Const(false),
			LitMeaning::Eq(i) => self.direct_encoding.find(&self.domain, i)?,
			_ => unreachable!(),
		});
		if negate { !bv } else { bv }.into()
	}

	pub(crate) fn get_value<V: SatValuation + ?Sized>(&self, model: &V) -> IntVal {
		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let mut val_iter = self.domain.clone().into_iter().flatten();
				for l in storage.clone() {
					match model.value(l.into()) {
						Some(false) => return val_iter.next().unwrap(),
						Some(true) => {
							let _ = val_iter.next();
						}
						None => unreachable!(),
					}
				}
				*self.domain.upper_bound().unwrap()
			}
			OrderStorage::Lazy(storage) => {
				let mut last_val = *self.domain.lower_bound().unwrap();
				if storage.storage.is_empty() {
					return last_val;
				}
				let mut i = storage.min_index as usize;
				while model.value(storage.storage[i].var.into()).unwrap() {
					last_val = storage.storage[i].val;
					if !storage.storage[i].has_next {
						break;
					}
					i = storage.storage[i].next as usize;
				}
				last_val
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
			OrderStorage::Eager { lower_bound, .. } => {
				let lb = trail.get_trailed_int(*lower_bound);
				self.get_bool_lit(LitMeaning::GreaterEq(lb)).unwrap()
			}
			OrderStorage::Lazy(storage) => {
				let lb_index = trail.get_trailed_int(storage.lb_index);
				BoolView(if lb_index >= 0 {
					BoolViewInner::Lit(storage[lb_index as u32].var.into())
				} else {
					BoolViewInner::Const(true)
				})
			}
		}
	}

	/// Returns the upper bound of the current state of the integer variable.
	pub(crate) fn get_upper_bound(&self, trail: &impl TrailingActions) -> IntVal {
		match &self.order_encoding {
			OrderStorage::Eager { upper_bound, .. } => trail.get_trailed_int(*upper_bound),
			OrderStorage::Lazy(storage) => {
				let high = trail.get_trailed_int(storage.ub_index);
				if high >= 0 {
					storage.storage[high as usize].val - 1
				} else {
					*self.domain.upper_bound().unwrap()
				}
			}
		}
	}

	/// Returns the boolean view associated with the upper bound of the variable being this value.
	pub(crate) fn get_upper_bound_lit(&self, trail: &impl TrailingActions) -> BoolView {
		match &self.order_encoding {
			OrderStorage::Eager { upper_bound, .. } => {
				let ub = trail.get_trailed_int(*upper_bound);
				self.get_bool_lit(LitMeaning::Less(ub + 1)).unwrap()
			}
			OrderStorage::Lazy(storage) => {
				let ub_index = trail.get_trailed_int(storage.ub_index);
				BoolView(if ub_index >= 0 {
					BoolViewInner::Lit(!storage[ub_index as u32].var)
				} else {
					BoolViewInner::Const(true)
				})
			}
		}
	}

	/// Returns the lower and upper bounds of the current state of the integer variable.
	pub(crate) fn get_bounds(&self, trail: &impl TrailingActions) -> (IntVal, IntVal) {
		match &self.order_encoding {
			OrderStorage::Eager {
				upper_bound,
				lower_bound,
				..
			} => (
				trail.get_trailed_int(*lower_bound),
				trail.get_trailed_int(*upper_bound),
			),
			OrderStorage::Lazy(storage) => {
				let high = trail.get_trailed_int(storage.ub_index);
				let low = trail.get_trailed_int(storage.lb_index);
				let lb = if low >= 0 {
					storage.storage[low as usize].val
				} else {
					*self.domain.lower_bound().unwrap()
				};
				let ub = if high >= 0 {
					storage.storage[high as usize].val - 1
				} else {
					*self.domain.upper_bound().unwrap()
				};
				(lb, ub)
			}
		}
	}

	/// Notify that a new lower bound has been propagated for the variable,
	/// returning the literal previous lower bound.
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
	/// returning the literal previous upper bound.
	///
	/// # Warning
	///
	/// This method assumes the literal for the new upper bound has been created (and propagated).
	pub(crate) fn notify_upper_bound(
		&mut self,
		trail: &mut impl TrailingActions,
		val: IntVal,
	) -> IntVal {
		match &self.order_encoding {
			OrderStorage::Eager { upper_bound, .. } => trail.set_trailed_int(*upper_bound, val),
			OrderStorage::Lazy(
				storage @ LazyOrderStorage {
					max_index,
					ub_index,
					..
				},
			) => {
				let ub = *self.domain.upper_bound().unwrap();
				if val == ub {
					return ub;
				}
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
				if old_index < 0 {
					ub
				} else {
					storage[cur_index].val - 1
				}
			}
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(variant_size_differences)]
pub(crate) enum OrderStorage {
	/// Variables for all inequality conditions are eagerly created and stored in order
	Eager {
		lower_bound: TrailedInt,
		upper_bound: TrailedInt,
		storage: VarRange,
	},
	/// Variables for inequality conditions are lazily created and stored in a hashmap
	Lazy(LazyOrderStorage),
}

pub(crate) struct LazyLitDef {
	pub(crate) meaning: LitMeaning,
	pub(crate) prev: Option<RawVar>,
	pub(crate) next: Option<RawVar>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LazyOrderStorage {
	min_index: u32,
	max_index: u32,
	lb_index: TrailedInt,
	ub_index: TrailedInt,
	storage: Vec<OrderNode>,
}

type RangeIter<'a> = Peekable<
	Map<
		<&'a RangeList<IntVal> as IntoIterator>::IntoIter,
		fn(RangeInclusive<&'a IntVal>) -> RangeInclusive<IntVal>,
	>,
>;
#[derive(Debug)]
enum OrderEntry<'a> {
	Eager(&'a VarRange, usize),
	Occupied {
		storage: &'a mut LazyOrderStorage,
		index: u32,
		range_iter: RangeIter<'a>,
	},
	Vacant {
		storage: &'a mut LazyOrderStorage,
		prev_index: IntVal,
		range_iter: RangeIter<'a>,
		val: IntVal,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OrderNode {
	val: IntVal,
	var: RawVar,
	has_prev: bool,
	prev: u32,
	has_next: bool,
	next: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SearchDirection {
	Increasing,
	Decreasing,
}

impl LazyOrderStorage {
	// Find the the index of the node that contains the value or the value "before" the value
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

	fn is_empty(&self) -> bool {
		self.storage.is_empty()
	}

	fn min(&self) -> Option<&OrderNode> {
		if self.is_empty() {
			None
		} else {
			Some(&self[self.min_index])
		}
	}

	fn max(&self) -> Option<&OrderNode> {
		if self.is_empty() {
			None
		} else {
			Some(&self[self.max_index])
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

impl OrderStorage {
	// Find current domain range and calculate the offset in the VarRange
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
}

impl OrderEntry<'_> {
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DirectStorage {
	/// Variables for all equality conditions are eagerly created and stored in order
	Eager(VarRange),
	/// Variables for equality conditions are lazily created and stored in a hashmap
	Lazy(HashMap<IntVal, RawVar>),
}

enum DirectEntry<'a> {
	Occupied(BoolViewInner),
	Vacant(VacantEntry<'a, IntVal, RawVar>),
}

impl DirectStorage {
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

impl DirectEntry<'_> {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LitMeaning {
	Eq(IntVal),
	NotEq(IntVal),
	GreaterEq(IntVal),
	Less(IntVal),
}

impl LitMeaning {
	pub(crate) fn defining_clauses(
		&self,
		lit: RawLit,
		prev: Option<RawLit>,
		next: Option<RawLit>,
	) -> Vec<Clause> {
		let mut ret = Vec::<Clause>::new();
		match self {
			LitMeaning::Eq(_) => {
				let prev = prev.expect("prev should contain the GreaterEq literal for the value"); // x≥i
				let next =
					next.expect("next should contain the GreaterEq literal for the next value"); // x≥i+n

				ret.push(vec![!lit, prev]); // x=i -> x<i
				ret.push(vec![!lit, !next]); // x=i -> x≤i+n
				ret.push(vec![lit, !prev, next]); // x!=i -> x<i \/ x>i+n
			}
			LitMeaning::GreaterEq(_) => {
				if let Some(prev) = prev {
					ret.push(vec![!lit, prev]); // x>=i -> x≥(i-n)
				}
				if let Some(next) = next {
					ret.push(vec![!next, lit]); // x>=(i+n) -> x≥i
				}
			}
			_ => unreachable!(),
		}
		ret
	}
}

impl Not for LitMeaning {
	type Output = LitMeaning;

	fn not(self) -> Self::Output {
		match self {
			LitMeaning::Eq(i) => LitMeaning::NotEq(i),
			LitMeaning::NotEq(i) => LitMeaning::Eq(i),
			LitMeaning::GreaterEq(i) => LitMeaning::Less(i),
			LitMeaning::Less(i) => LitMeaning::GreaterEq(i),
		}
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		solver::{
			engine::int_var::{EncodingType, IntVar},
			view::{BoolViewInner, IntViewInner},
		},
		BoolView, IntView, LitMeaning, Solver,
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
		let mut slv: Solver<Cadical> = Cnf::default().into();
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
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(2)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(LitMeaning::Less(2)).unwrap();
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(3)).unwrap();
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(4)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(4)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::Eq(1)).unwrap();
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::Eq(2)).unwrap();
		assert_eq!(get_lit(lit), 4);
		let lit = a.get_bool_lit(LitMeaning::Eq(3)).unwrap();
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(LitMeaning::Eq(4)).unwrap();
		assert_eq!(get_lit(lit), 3);

		let mut slv: Solver<Cadical> = Cnf::default().into();
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
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(2)).unwrap();
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(3)).unwrap();
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(4)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(4)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(8)).unwrap();
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(8)).unwrap();
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(10)).unwrap();
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(LitMeaning::Less(10)).unwrap();
		assert_eq!(get_lit(lit), -5);
		let lit = a.get_bool_lit(LitMeaning::Eq(1)).unwrap();
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::Eq(2)).unwrap();
		assert_eq!(get_lit(lit), 6);
		let lit = a.get_bool_lit(LitMeaning::Eq(3)).unwrap();
		assert_eq!(get_lit(lit), 7);
		let lit = a.get_bool_lit(LitMeaning::Eq(8)).unwrap();
		assert_eq!(get_lit(lit), 8);
		let lit = a.get_bool_lit(LitMeaning::Eq(10)).unwrap();
		assert_eq!(get_lit(lit), 5);

		assert_eq!(
			a.get_bool_lit(LitMeaning::GreaterEq(1)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Less(11)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Less(1)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::GreaterEq(11)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(0)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(11)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(5)).unwrap(),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(0)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(11)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(5)).unwrap(),
			BoolView(BoolViewInner::Const(true))
		);
	}
}
