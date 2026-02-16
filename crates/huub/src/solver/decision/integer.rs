//! Integer decision variable definitions for the solver layer.

use std::{
	collections::hash_map::{self, VacantEntry},
	iter::{Map, Peekable},
	num::NonZero,
	ops::{Index, IndexMut, Neg, RangeBounds, RangeInclusive},
};

use itertools::Itertools;
use pindakaas::{
	ClauseDatabaseTools, Lit as RawLit, Var as RawVar, VarRange,
	solver::propagation::ExternalPropagation,
};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, IntDecisionActions, IntExplanationActions, IntInspectionActions,
		Trailed, TrailingActions,
	},
	solver::{
		IntLitMeaning, Solver,
		decision::{Decision, DecisionReference, private},
		engine::State,
		solving_context::SolvingContext,
		view::{View, boolean::BoolView},
	},
	views::{LinearBoolView, LinearView},
};

/// An entry in the [`DirectStorage`] that can be used to access the
/// representation of an equality condition, or insert a new literal to
/// represent the condition otherwise.
enum DirectEntry<'a> {
	/// The condition is already stored in the [`DirectStorage`].
	Occupied(View<bool>),
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
struct DomainLocation<'a, const OFFSET: usize> {
	/// Tightest value for the less-than literal
	less_val: IntVal,
	/// Tightest value for the greater-than or equal-to literal
	greater_eq_val: IntVal,
	/// Offset of the literal in the variable range.
	offset: [usize; OFFSET],
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
pub(crate) struct IntDecision {
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
	upper_bound: Trailed<IntVal>,
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
	lb_index: Trailed<isize>,
	/// The index of the node that currently represents the upper bound of the
	/// integer variable.
	ub_index: Trailed<isize>,
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
		lower_bound: Trailed<IntVal>,
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

impl Decision<IntVal> {
	/// Return the a integer identifier that can be used for this decision.
	pub(crate) fn ident(&self) -> u32 {
		self.0
	}

	/// Return the index used to access this decision in solver storage.
	pub(crate) fn idx(&self) -> usize {
		self.0 as usize
	}
}

impl<Sat: ExternalPropagation> IntDecisionActions<Solver<Sat>> for Decision<IntVal> {
	fn lit(&self, ctx: &mut Solver<Sat>, meaning: IntLitMeaning) -> View<bool> {
		let (mut actions, mut engine) = ctx.as_parts_mut();
		let mut ctx = SolvingContext::new(&mut actions, &mut engine.state);
		self.lit(&mut ctx, meaning)
	}

	fn val_lit(&self, ctx: &mut Solver<Sat>) -> Option<View<bool>> {
		let (mut actions, mut engine) = ctx.as_parts_mut();
		let mut ctx = SolvingContext::new(&mut actions, &mut engine.state);
		IntDecisionActions::val_lit(self, &mut ctx)
	}
}

impl IntExplanationActions<State> for Decision<IntVal> {
	fn lit_relaxed(&self, ctx: &State, mut meaning: IntLitMeaning) -> (View<bool>, IntLitMeaning) {
		debug_assert!(
			!matches!(meaning, IntLitMeaning::Eq(_)),
			"relaxed integer literals are not yet supported for IntLitMeaning::Eq(_)"
		);

		let var_def = &ctx.int_vars[self.idx()];
		// If we are looking for a not-equal literal, try and find it. Return it if we
		// find it, otherwise defer to an order literal.
		if let IntLitMeaning::NotEq(v) = meaning {
			if let Some((bv, _)) = var_def.try_lit(meaning) {
				return (bv, IntLitMeaning::NotEq(v));
			}

			let lb = var_def.lower_bound(&ctx.trail);
			if v < lb {
				meaning = IntLitMeaning::GreaterEq(v + 1);
			} else {
				debug_assert!(v > var_def.upper_bound(&ctx.trail));
				meaning = IntLitMeaning::Less(v);
			}
		}
		// Find the strongest order literal that fits the given meaning.
		match meaning {
			IntLitMeaning::GreaterEq(v) => {
				let (bv, v) = var_def.greater_eq_lit_or_weaker(&ctx.trail, v);
				(bv, IntLitMeaning::GreaterEq(v))
			}
			IntLitMeaning::Less(v) => {
				let (bv, v) = var_def.less_lit_or_weaker(&ctx.trail, v);
				(bv, IntLitMeaning::Less(v))
			}
			_ => unreachable!(),
		}
	}
}

impl<Sat> IntInspectionActions<Solver<Sat>> for Decision<IntVal> {
	fn bounds(&self, ctx: &Solver<Sat>) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &Solver<Sat>) -> IntSet {
		self.domain(&ctx.engine.borrow().state)
	}

	fn in_domain(&self, ctx: &Solver<Sat>, val: IntVal) -> bool {
		self.in_domain(&ctx.engine.borrow().state, val)
	}

	fn lit_meaning(&self, ctx: &Solver<Sat>, lit: View<bool>) -> Option<IntLitMeaning> {
		self.lit_meaning(&ctx.engine.borrow().state, lit)
	}

	fn max(&self, ctx: &Solver<Sat>) -> IntVal {
		self.max(&ctx.engine.borrow().state)
	}

	fn max_lit(&self, ctx: &Solver<Sat>) -> View<bool> {
		self.max_lit(&ctx.engine.borrow().state)
	}

	fn min(&self, ctx: &Solver<Sat>) -> IntVal {
		self.min(&ctx.engine.borrow().state)
	}

	fn min_lit(&self, ctx: &Solver<Sat>) -> View<bool> {
		self.min_lit(&ctx.engine.borrow().state)
	}

	fn try_lit(&self, ctx: &Solver<Sat>, meaning: IntLitMeaning) -> Option<View<bool>> {
		self.try_lit(&ctx.engine.borrow().state, meaning)
	}

	fn val(&self, ctx: &Solver<Sat>) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

impl IntInspectionActions<State> for Decision<IntVal> {
	fn bounds(&self, ctx: &State) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &State) -> IntSet {
		ctx.int_vars[self.idx()].domain(&ctx.trail)
	}

	fn in_domain(&self, ctx: &State, val: IntVal) -> bool {
		let (lb, ub) = self.bounds(ctx);
		if lb <= val && val <= ub {
			let eq_lit = self.try_lit(ctx, IntLitMeaning::Eq(val));
			if let Some(eq_lit) = eq_lit {
				eq_lit.val(ctx).unwrap_or(true)
			} else {
				true
			}
		} else {
			false
		}
	}

	fn lit_meaning(&self, ctx: &State, lit: View<bool>) -> Option<IntLitMeaning> {
		let BoolView::Lit(lit) = lit.0 else {
			return None;
		};
		let (iv, meaning) = ctx.get_int_lit_meaning(lit)?;
		if *self != iv {
			return None;
		}
		Some(meaning)
	}

	fn max(&self, ctx: &State) -> IntVal {
		ctx.int_vars[self.idx()].upper_bound(&ctx.trail)
	}

	fn max_lit(&self, ctx: &State) -> View<bool> {
		ctx.int_vars[self.idx()].upper_bound_lit(&ctx.trail)
	}

	fn min(&self, ctx: &State) -> IntVal {
		ctx.int_vars[self.idx()].lower_bound(&ctx.trail)
	}

	fn min_lit(&self, ctx: &State) -> View<bool> {
		ctx.int_vars[self.idx()].lower_bound_lit(&ctx.trail)
	}

	fn try_lit(&self, ctx: &State, meaning: IntLitMeaning) -> Option<View<bool>> {
		ctx.int_vars[self.idx()].try_lit(meaning).map(|t| t.0)
	}

	fn val(&self, ctx: &State) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

impl Neg for Decision<IntVal> {
	type Output = LinearView<NonZero<IntVal>, IntVal, Self>;

	fn neg(self) -> Self::Output {
		let lin: LinearView<NonZero<IntVal>, IntVal, Self> = self.into();
		-lin
	}
}

impl DirectEntry<'_> {
	/// Extract the [`BoolViewInner`] if the entry is occupied, or insert a new
	/// variable using the given function.
	fn or_insert_with(self, f: impl FnOnce() -> RawVar) -> View<bool> {
		match self {
			DirectEntry::Occupied(bv) => bv,
			DirectEntry::Vacant(no_entry) => {
				let v = f();
				no_entry.insert(v);
				Decision(v.into()).into()
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
					DirectEntry::Occupied(Decision(vars.index(offset as usize).into()).into())
				} else {
					DirectEntry::Occupied(false.into())
				}
			}
			DirectStorage::Lazy(map) => match map.entry(i) {
				hash_map::Entry::Occupied(entry) => {
					DirectEntry::Occupied(Decision((*entry.get()).into()).into())
				}
				hash_map::Entry::Vacant(no_entry) => {
					if domain.contains(&i) {
						DirectEntry::Vacant(no_entry)
					} else {
						DirectEntry::Occupied(false.into())
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
	fn find(&self, domain: &RangeList<IntVal>, i: IntVal) -> Option<View<bool>> {
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
					Decision(vars.index(offset as usize).into()).into()
				} else {
					false.into()
				})
			}
			DirectStorage::Lazy(map) => {
				map.get(&i)
					.map(|v| Decision((*v).into()).into())
					.or_else(|| {
						if !domain.contains(&i) {
							Some(false.into())
						} else {
							None
						}
					})
			}
		}
	}
}

impl IntDecision {
	/// Returns the lower and upper bounds of the current state of the integer
	/// variable.
	pub(crate) fn bounds(&self, trail: &impl TrailingActions) -> (IntVal, IntVal) {
		let lb = match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => trail.trailed(*lower_bound),
			OrderStorage::Lazy(storage) => {
				let low = trail.trailed(storage.lb_index);
				if low >= 0 {
					storage.storage[low as usize].val
				} else {
					*self.domain.lower_bound().unwrap()
				}
			}
		};
		(lb, trail.trailed(self.upper_bound))
	}

	/// Returns the current domain of the integer variable.
	pub(crate) fn domain<T>(&self, trail: &T) -> RangeList<IntVal>
	where
		T: TrailingActions,
		Decision<bool>: BoolInspectionActions<T>,
	{
		let (lb, ub) = self.bounds(trail);
		let domain = &self.domain;
		let orig_lb = *domain.lower_bound().unwrap();
		let lb_var = || self.order_encoding.find(domain, orig_lb + 1).map(|v| v.0);
		let orig_ub = *domain.upper_bound().unwrap();
		let ub_var = || self.order_encoding.find(domain, orig_ub).map(|v| v.0);

		match &self.direct_encoding {
			DirectStorage::Eager(direct_range) => {
				let pos = domain.position(&lb).unwrap();
				RangeList::from_sorted_elements(
					domain
						.iter()
						.skip_while(|range| *range.end() < lb)
						.flatten()
						.skip_while(|&v| v < lb)
						.enumerate()
						.map(|(i, v)| {
							(
								v,
								if v == orig_lb {
									lb_var().unwrap()
								} else if v == orig_ub {
									ub_var().unwrap()
								} else {
									direct_range.index(pos + i - 1)
								},
							)
						})
						.take_while(|(v, _)| *v <= ub)
						.filter(|&(_, lit)| Decision::<bool>(lit.into()).val(trail) != Some(false))
						.map(|(v, _)| v),
				)
			}
			DirectStorage::Lazy(hash_map) => RangeList::from_sorted_elements(
				domain
					.iter()
					.skip_while(|range| *range.end() < lb)
					.flatten()
					.skip_while(|&v| v < lb)
					.map(|v| {
						(
							v,
							if v == orig_lb {
								lb_var()
							} else if v == orig_ub {
								ub_var()
							} else {
								hash_map.get(&v).copied()
							},
						)
					})
					.take_while(|(v, _)| *v <= ub)
					.filter(|&(_, lit)| {
						lit.map(|lit| Decision::<bool>(lit.into()).val(trail) != Some(false))
							.unwrap_or(true)
					})
					.map(|(v, _)| v),
			),
		}
	}

	/// Returns the boolean view associated with `≥ v` if it exists or weaker
	/// version otherwise.
	///
	/// ## Warning
	/// This function assumes that `v <= lb`.
	pub(crate) fn greater_eq_lit_or_weaker<T>(&self, trail: &T, v: IntVal) -> (View<bool>, IntVal)
	where
		T: TrailingActions,
		Decision<bool>: BoolInspectionActions<T>,
	{
		debug_assert!(v <= self.lower_bound(trail));
		if v <= *self.domain.lower_bound().unwrap() {
			return (true.into(), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation { offset, .. } = OrderStorage::resolve_val::<1>(&self.domain, v);
				(Decision(!storage.index(offset[0])).into(), v)
			}
			OrderStorage::Lazy(storage) => {
				let mut ret = (true.into(), v);
				let lb_index = trail.trailed(storage.lb_index);
				let mut index = if lb_index < 0 {
					return ret;
				} else {
					lb_index as usize
				};
				while storage.storage[index].val >= v {
					let node = &storage.storage[index];
					let lit: View<bool> = Decision(!node.var).into();
					if let Some(v) = lit.val(trail) {
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
	pub(crate) fn less_lit_or_weaker<T>(&self, trail: &T, v: IntVal) -> (View<bool>, IntVal)
	where
		T: TrailingActions,
		Decision<bool>: BoolInspectionActions<T>,
	{
		if v < self.upper_bound(trail) {
			println!("{}", self.upper_bound(trail));
			println!("What?!");
		}
		debug_assert!(v >= self.upper_bound(trail));
		if v > *self.domain.upper_bound().unwrap() {
			return (true.into(), v);
		}

		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation { offset, .. } = OrderStorage::resolve_val::<1>(&self.domain, v);
				let bv = Decision(storage.index(offset[0]).into()).into();
				(bv, v)
			}
			OrderStorage::Lazy(storage) => {
				let mut ret = (true.into(), v);
				let ub_index = trail.trailed(storage.ub_index);
				let mut index = if ub_index < 0 {
					return ret;
				} else {
					ub_index as usize
				};
				while storage.storage[index].val <= v {
					let node = &storage.storage[index];
					let lit: View<bool> = Decision(node.var.into()).into();
					if let Some(v) = lit.val(trail) {
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

	/// Access the Boolean literal with the given meaning, creating it if it is
	/// not yet available.
	pub(crate) fn lit(
		&mut self,
		lit_req: IntLitMeaning,
		mut new_var: impl FnMut(LazyLitDef) -> RawVar,
	) -> (View<bool>, IntLitMeaning) {
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

		let bv = match lit_req {
			IntLitMeaning::Eq(i) | IntLitMeaning::NotEq(i) if i < lb || i > ub => {
				matches!(lit_req, IntLitMeaning::NotEq(_)).into()
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
				matches!(lit_req, IntLitMeaning::GreaterEq(_)).into()
			}
			IntLitMeaning::GreaterEq(i) | IntLitMeaning::Less(i) if i > ub => {
				matches!(lit_req, IntLitMeaning::Less(_)).into()
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
				Decision(if matches!(lit_req, IntLitMeaning::GreaterEq(_)) {
					lit_req = IntLitMeaning::GreaterEq(geq);
					!var
				} else {
					lit_req = IntLitMeaning::Less(lt);
					var
				})
				.into()
			}
		};

		(bv, lit_req)
	}

	/// Returns the meaning of a literal in the context of this integer
	/// variable.
	///
	/// # Warning
	///
	/// This method can only be used with literals that were eagerly created for
	/// this integer variable. Lazy literals should be mapped using
	/// [`BoolToIntMap`].
	pub(crate) fn lit_meaning(&self, lit: Decision<bool>) -> IntLitMeaning {
		let var = lit.0.var();
		let ret = |l: IntLitMeaning| {
			if lit.is_negated() { !l } else { l }
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

	/// Returns the lower bound of the current state of the integer variable.
	pub(crate) fn lower_bound<T>(&self, trail: &T) -> IntVal
	where
		T: TrailingActions,
		Decision<bool>: BoolInspectionActions<T>,
	{
		match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => trail.trailed(*lower_bound),
			OrderStorage::Lazy(storage) => {
				let low = trail.trailed(storage.lb_index);
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
	pub(crate) fn lower_bound_lit(&self, trail: &impl TrailingActions) -> View<bool> {
		match &self.order_encoding {
			OrderStorage::Eager {
				lower_bound,
				storage,
				..
			} => {
				let lb = trail.trailed(*lower_bound);
				if lb == *self.domain.lower_bound().unwrap() {
					true.into()
				} else {
					let DomainLocation { offset, .. } =
						OrderStorage::resolve_val::<1>(&self.domain, lb);
					Decision(!storage.index(offset[0])).into()
				}
			}
			OrderStorage::Lazy(storage) => {
				let lb_index = trail.trailed(storage.lb_index);
				if lb_index >= 0 {
					Decision(!storage[lb_index as u32].var).into()
				} else {
					true.into()
				}
			}
		}
	}

	/// Create a new integer variable within the given solver, which the given
	/// domain. The `order_encoding` and `direct_encoding` parameters determine
	/// whether literals to reason about the integer variables are created
	/// eagerly or lazily.
	pub(crate) fn new_in<Sat: ExternalPropagation>(
		slv: &mut Solver<Sat>,
		domain: IntSet,
		order_encoding: EncodingType,
		direct_encoding: EncodingType,
	) -> View<IntVal> {
		let orig_domain_len = domain.card();
		assert_ne!(
			orig_domain_len,
			Some(0),
			"Unable to create integer variable empty domain"
		);
		if orig_domain_len == Some(1) {
			return (*domain.lower_bound().unwrap()).into();
		}
		let lb = *domain.lower_bound().unwrap();
		let ub = *domain.upper_bound().unwrap();
		if orig_domain_len == Some(2) {
			let lit = slv.new_bool_decision();
			return LinearBoolView::new(NonZero::new(ub - lb).unwrap(), lb, lit).into();
		}
		debug_assert!(
			direct_encoding != EncodingType::Eager || order_encoding == EncodingType::Eager
		);

		let mut engine = slv.engine.borrow_mut();
		let upper_bound = engine.state.trail.track(ub);
		let order_encoding = match order_encoding {
			EncodingType::Eager => OrderStorage::Eager {
				lower_bound: engine.state.trail.track(lb),
				storage: slv.sat.new_var_range(
					orig_domain_len.expect(
						"unable to create literals eagerly for domains that exceed usize::MAX",
					) - 1,
				),
			},
			EncodingType::Lazy => OrderStorage::Lazy(LazyOrderStorage {
				min_index: 0,
				max_index: 0,
				lb_index: engine.state.trail.track(-1),
				ub_index: engine.state.trail.track(-1),
				storage: Vec::default(),
			}),
		};
		let direct_encoding =
			match direct_encoding {
				EncodingType::Eager => DirectStorage::Eager(slv.sat.new_var_range(
					orig_domain_len.expect(
						"unable to create literals eagerly for domains that exceed usize::MAX",
					) - 2,
				)),
				EncodingType::Lazy => DirectStorage::Lazy(FxHashMap::default()),
			};
		// Drop engine to allow SAT interaction
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
				slv.sat.add_clause([!ord_i, ord_j]).unwrap(); // x<i -> x<(i+n)
				if matches!(direct_encoding, DirectStorage::Eager(_)) {
					let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
					slv.sat.add_clause([!eq_i, !ord_i]).unwrap(); // x=i -> x≥i
					slv.sat.add_clause([!eq_i, ord_j]).unwrap(); // x=i -> x<(i+n)
					slv.sat.add_clause([eq_i, ord_i, !ord_j]).unwrap(); // x≠i -> (x<i \/
					// x≥(i+n))
				}
			}
			debug_assert!(direct_enc_iter.next().is_none());
		}

		// Create the resulting integer variable
		let mut engine = slv.engine.borrow_mut();
		engine.state.int_vars.push(Self {
			direct_encoding,
			domain,
			order_encoding,
			upper_bound,
		});
		let iv = Decision((engine.state.int_vars.len() - 1) as u32);
		// Create propagator activation list
		engine.state.int_activation.push(Default::default());
		debug_assert_eq!(
			engine.state.int_vars.len(),
			engine.state.int_activation.len()
		);

		// Setup the boolean to integer mapping
		if let OrderStorage::Eager { storage, .. } = engine.state.int_vars[iv.idx()].order_encoding
		{
			let mut vars = storage;
			if let DirectStorage::Eager(vars2) = &engine.state.int_vars[iv.idx()].direct_encoding {
				debug_assert_eq!(Into::<i32>::into(vars.end()) + 1, vars2.start().into());
				vars = VarRange::new(vars.start(), vars2.end());
			}
			engine.state.bool_to_int.insert_eager(vars, iv);
			engine
				.state
				.trail
				.grow_to_boolvar(vars.clone().next_back().unwrap());
			for l in vars {
				slv.sat.add_observed_var(l);
			}
		}

		iv.into()
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
		Decision<bool>: BoolInspectionActions<T>,
	{
		debug_assert!(self.domain.contains(&val));
		debug_assert!(val > self.lower_bound(trail));
		match &self.order_encoding {
			OrderStorage::Eager { lower_bound, .. } => {
				trail.set_trailed(*lower_bound, val);
			}
			OrderStorage::Lazy(
				storage @ LazyOrderStorage {
					min_index,
					lb_index,
					..
				},
			) => {
				let cur_index = trail.trailed(*lb_index);
				let cur_index = if cur_index < 0 {
					*min_index
				} else {
					cur_index as u32
				};
				debug_assert!(storage[cur_index].val <= val);
				let new_index = storage.find_index(cur_index, SearchDirection::Increasing, val);
				debug_assert_eq!(storage[new_index].val, val);
				let old_index = trail.set_trailed(*lb_index, new_index as isize);
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
		debug_assert!(val < self.upper_bound(trail));
		trail.set_trailed(self.upper_bound, val);
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
			} = OrderStorage::resolve_val::<0>(&self.domain, val + 1);
			let cur_index = trail.trailed(*ub_index);
			let cur_index = if cur_index < 0 {
				*max_index
			} else {
				cur_index as u32
			};
			let new_index = storage.find_index(cur_index, SearchDirection::Decreasing, val);
			debug_assert_eq!(storage[new_index].val, val);
			let old_index = trail.set_trailed(*ub_index, new_index as isize);
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

	/// Try and find an (already) existing Boolean literal with the given
	/// meaning
	pub(crate) fn try_lit(&self, lit_req: IntLitMeaning) -> Option<(View<bool>, IntLitMeaning)> {
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

		let bv = match lit_req {
			IntLitMeaning::Eq(i) if i < lb || i > ub => false.into(),
			IntLitMeaning::Eq(i) => self.direct_encoding.find(&self.domain, i)?,
			IntLitMeaning::GreaterEq(i) if i <= lb => true.into(),
			IntLitMeaning::GreaterEq(i) if i > ub => false.into(),
			IntLitMeaning::GreaterEq(i) => {
				let (var, _, geq) = self.order_encoding.find(&self.domain, i)?;
				lit_req = IntLitMeaning::GreaterEq(geq);
				Decision(!var).into()
			}
			IntLitMeaning::Less(i) if i <= lb => false.into(),
			IntLitMeaning::Less(i) if i > ub => true.into(),
			IntLitMeaning::Less(i) => {
				let (var, lt, _) = self.order_encoding.find(&self.domain, i)?;
				lit_req = IntLitMeaning::Less(lt);
				Decision(var.into()).into()
			}
			IntLitMeaning::NotEq(i) if i < lb || i > ub => true.into(),
			IntLitMeaning::NotEq(i) => !self.direct_encoding.find(&self.domain, i)?,
		};
		Some((bv, lit_req))
	}

	/// Returns the upper bound of the current state of the integer variable.
	pub(crate) fn upper_bound(&self, trail: &impl TrailingActions) -> IntVal {
		trail.trailed(self.upper_bound)
	}

	/// Returns the boolean view associated with the upper bound of the variable
	/// being this value.
	pub(crate) fn upper_bound_lit(&self, trail: &impl TrailingActions) -> View<bool> {
		match &self.order_encoding {
			OrderStorage::Eager { storage, .. } => {
				let ub = trail.trailed(self.upper_bound);
				if ub == *self.domain.upper_bound().unwrap() {
					true.into()
				} else {
					let DomainLocation { offset, .. } =
						OrderStorage::resolve_val::<1>(&self.domain, ub + 1);
					Decision(storage.index(offset[0]).into()).into()
				}
			}
			OrderStorage::Lazy(storage) => {
				let ub_index = trail.trailed(storage.ub_index);
				if ub_index >= 0 {
					Decision(storage[ub_index as u32].var.into()).into()
				} else {
					true.into()
				}
			}
		}
	}
}

impl DecisionReference for IntVal {
	type Ref = u32;
}
impl private::Sealed for IntVal {}

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
					range_iter.next().unwrap();
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
					range_iter.next().unwrap();
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
		match self {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation {
					less_val,
					greater_eq_val: val,
					offset,
					..
				} = Self::resolve_val::<1>(domain, val);
				let entry = OrderEntry::Eager(storage, offset[0]);
				(entry, less_val, val)
			}
			OrderStorage::Lazy(storage) => {
				let DomainLocation {
					less_val,
					greater_eq_val: val,
					range_iter,
					..
				} = Self::resolve_val::<0>(domain, val);
				let entry = if storage.is_empty() || storage.min().unwrap().val > val {
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
				};
				(entry, less_val, val)
			}
		}
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
		match self {
			OrderStorage::Eager { storage, .. } => {
				let DomainLocation {
					less_val,
					greater_eq_val: val,
					offset,
					..
				} = Self::resolve_val::<1>(domain, val);
				Some((storage.index(offset[0]), less_val, val))
			}
			OrderStorage::Lazy(storage) => {
				let DomainLocation {
					less_val,
					greater_eq_val: val,
					..
				} = Self::resolve_val::<0>(domain, val);
				if storage.is_empty()
					|| storage.min().unwrap().val > val
					|| storage.max().unwrap().val < val
				{
					return None;
				};

				let i = storage.find_index(storage.min_index, SearchDirection::Increasing, val);
				let var = (storage[i].val == val).then(|| storage[i].var)?;
				Some((var, less_val, val))
			}
		}
	}

	#[inline]
	/// Returns the lowest integer value `j`, for which `< i` is equivalent to
	/// `< j` in the given `domain. In addition it returns the index of the
	/// range in `domain` in which `j` is located, and calculate the offset of
	/// the representation `< j` in a VarRange when the order literals are
	/// eagerly created.
	fn resolve_val<const OFFSET: usize>(
		domain: &RangeList<IntVal>,
		val: IntVal,
	) -> DomainLocation<'_, OFFSET> {
		let mut offset = if OFFSET >= 1 { -1 } else { 0 }; // -1 to account for the lower bound
		let mut it = domain.iter().peekable();
		let mut last_val = IntVal::MIN;
		loop {
			let r = it.peek().unwrap();
			if val < *r.start() {
				return DomainLocation {
					less_val: last_val + 1,
					greater_eq_val: *r.start(),
					offset: [offset as usize; OFFSET],
					range_iter: it,
				};
			} else if val <= *r.end() {
				if OFFSET >= 1 {
					offset += val - r.start();
				}
				return DomainLocation {
					less_val: if val == *r.start() { last_val + 1 } else { val },
					greater_eq_val: val,
					offset: [offset as usize; OFFSET],
					range_iter: it,
				};
			} else if OFFSET >= 1 {
				offset += r.end() - r.start() + 1;
			}
			last_val = *it.next().unwrap().end();
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{iter::once, num::NonZeroI32};

	use itertools::Itertools;
	use pindakaas::Lit as RawLit;
	use rangelist::RangeList;

	use crate::{
		IntVal,
		actions::{IntDecisionActions, IntInspectionActions},
		solver::{
			IntLitMeaning, Solver,
			decision::{
				Decision,
				integer::{EncodingType, IntDecision},
			},
			view::{View, boolean::BoolView, integer::IntView},
		},
		views::LinearView,
	};

	fn assert_eager_lits_eq(
		iv: &mut IntDecision,
		input: impl IntoIterator<Item = IntLitMeaning>,
		lits: impl IntoIterator<Item = View<bool>>,
		output: impl IntoIterator<Item = IntLitMeaning>,
	) {
		for (req, expected) in input.into_iter().zip_eq(lits.into_iter().zip_eq(output)) {
			let out = iv.try_lit(req).expect("lit must be present");
			assert_eq!(out, expected, "given {req:?}");
			let out = iv.lit(req, |_| panic!("all literals should be eagerly created"));
			assert_eq!(out, expected, "given {req:?}");
			if let BoolView::Lit(l) = out.0.0 {
				assert_eq!(iv.lit_meaning(l), expected.1);
			}
		}
	}

	fn assert_lazy_lits_eq(
		slv: &mut Solver,
		iv: Decision<IntVal>,
		input: impl IntoIterator<Item = IntLitMeaning>,
		lits: impl IntoIterator<Item = View<bool>>,
		output: impl IntoIterator<Item = IntLitMeaning>,
	) {
		for (req, expected) in input.into_iter().zip_eq(lits.into_iter().zip_eq(output)) {
			let bv = iv.lit(slv, req);
			let m = iv.lit_meaning(slv, bv).unwrap_or(req);
			assert_eq!((bv, m), expected, "given {req:?}");

			let v = &mut slv.engine.borrow_mut().state.int_vars[iv.idx()];
			let out = v.try_lit(req).expect("lit must be present");
			assert_eq!(out, expected, "given {req:?}");
		}
	}

	#[test]
	fn eager_continuous_lits() {
		use IntLitMeaning::*;

		let mut slv: Solver = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from(1..=4),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView::Linear(LinearView { var: a, .. }) = a.0 else {
			unreachable!()
		};
		let a = &mut slv.engine.borrow_mut().state.int_vars[a.idx()];
		assert_eager_lits_eq(
			a,
			(0..=6).map(Less),
			vec![false.into(); 2]
				.into_iter()
				.chain(vec![1, 2, 3].into_iter().map(into_lit))
				.chain(vec![true.into(); 2]),
			(0..=6).map(Less),
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(GreaterEq),
			vec![true.into(); 2]
				.into_iter()
				.chain(vec![-1, -2, -3].into_iter().map(into_lit))
				.chain(vec![false.into(); 2]),
			(0..=6).map(GreaterEq),
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(Eq),
			once(false.into())
				.chain(vec![1, 4, 5, -3].into_iter().map(into_lit))
				.chain(vec![false.into(); 2]),
			vec![Eq(0), Less(2), Eq(2), Eq(3), GreaterEq(4), Eq(5), Eq(6)],
		);
		assert_eager_lits_eq(
			a,
			(0..=6).map(NotEq),
			once(true.into())
				.chain(vec![-1, -4, -5, 3].into_iter().map(into_lit))
				.chain(vec![true.into(); 2]),
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
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=3, 8..=10]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let IntView::Linear(LinearView { var: a, .. }) = a.0 else {
			unreachable!()
		};
		let a = &mut slv.engine.borrow_mut().state.int_vars[a.idx()];
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
				.chain(vec![false.into(); 4])
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
				.chain(vec![true.into(); 4])
				.chain(vec![-8, -9, 5].into_iter().map(into_lit)),
			once(GreaterEq(2))
				.chain((2..=9).map(NotEq))
				.chain(once(Less(10))),
		);
	}

	fn into_lit(i: i32) -> View<bool> {
		Decision(RawLit::from_raw(NonZeroI32::new(i).unwrap())).into()
	}

	#[test]
	fn lazy_gaps_lits() {
		use IntLitMeaning::*;

		let mut slv: Solver = Solver::default();
		let a = IntDecision::new_in(
			&mut slv,
			RangeList::from_iter([1..=3, 8..=10]),
			EncodingType::Lazy,
			EncodingType::Lazy,
		);
		let IntView::Linear(LinearView { var: a, .. }) = a.0 else {
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
				.chain(vec![false.into(); 4])
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
				.chain(vec![true.into(); 4])
				.chain(vec![-8, -9, 5].into_iter().map(into_lit)),
			once(GreaterEq(2))
				.chain((2..=9).map(NotEq))
				.chain(once(Less(10))),
		);
	}
}
