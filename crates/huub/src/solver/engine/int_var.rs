use std::ops::{Not, RangeBounds};

use flatzinc_serde::RangeList;
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatingSolver, VarRange},
	Lit as RawLit,
};

use super::TrailedInt;
use crate::{
	solver::{view::IntViewInner, IntView, SatSolver},
	Solver,
};

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

pub type IntVal = i64;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub(crate) struct IntVar {
	pub(crate) lower_bound: TrailedInt,
	pub(crate) upper_bound: TrailedInt,
	pub(crate) orig_domain: RangeList<IntVal>,
	pub(crate) orig_domain_len: usize,
	pub(crate) vars: VarRange,
	pub(crate) has_direct: bool,
}

impl IntVar {
	fn order_vars(&self) -> VarRange {
		VarRange::new(
			self.vars.index(0),
			self.vars.index(self.orig_domain_len - 2),
		)
	}

	fn direct_vars(&self) -> VarRange {
		if self.has_direct && self.orig_domain_len > 2 {
			VarRange::new(
				self.vars.index(self.orig_domain_len - 1),
				self.vars.index(self.vars.len() - 1),
			)
		} else {
			VarRange::empty()
		}
	}

	pub(crate) fn new_in<Sat: SatSolver>(
		slv: &mut Solver<Sat>,
		domain: RangeList<i64>,
		direct_encoding: bool,
	) -> IntView {
		let orig_domain_len = (&domain)
			.into_iter()
			.map(|x| (*x.end() - *x.start() + 1) as usize)
			.sum();
		debug_assert!(orig_domain_len >= 2, "Domain must have at least two values");

		let mut num_vars = orig_domain_len - 1;
		if direct_encoding {
			num_vars += orig_domain_len - 2;
		}
		let vars = slv
			.core
			.next_var_range(num_vars)
			.expect("Boolean variable pool exhausted");

		// Create the resulting integer variable
		let iv = Self {
			lower_bound: slv
				.engine_mut()
				.int_trail
				.track(*domain.lower_bound().unwrap()),
			upper_bound: slv
				.engine_mut()
				.int_trail
				.track(*domain.upper_bound().unwrap()),
			orig_domain: domain,
			orig_domain_len,
			vars: vars.clone(),
			has_direct: direct_encoding,
		};

		// Enforce consistency constraints
		let mut direct_enc_iter = iv.direct_vars();
		for (ord_i, ord_j) in iv.order_vars().tuple_windows() {
			let ord_i: RawLit = ord_i.into();
			let ord_j: RawLit = ord_j.into();
			slv.core.add_clause([!ord_j, ord_i]).unwrap();
			if direct_encoding {
				let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
				slv.core.add_clause([!eq_i, ord_i]).unwrap();
				slv.core.add_clause([!eq_i, !ord_j]).unwrap();
				slv.core.add_clause([!ord_i, ord_j, eq_i]).unwrap();
			}
		}
		debug_assert!(direct_enc_iter.next().is_none());

		// Setup the boolean to integer mapping
		let iv = slv.engine_mut().int_vars.push(iv);
		slv.engine_mut().bool_to_int.insert(vars.clone(), iv);
		for l in vars {
			<Sat as PropagatingSolver>::add_observed_var(&mut slv.core, l);
		}
		IntView(IntViewInner::VarRef(iv))
	}

	pub(crate) fn lit_meaning(&self, lit: RawLit) -> LitMeaning {
		let var = lit.var();
		debug_assert!(self.vars.contains(&var));
		let offset = self.vars.find(var).unwrap();
		let direct_offset = self.orig_domain_len - 1;

		let meaning = if offset < direct_offset {
			LitMeaning::GreaterEq(*self.orig_domain.lower_bound().unwrap() + 1 + offset as i64)
		} else {
			debug_assert!(self.has_direct);
			let offset = offset - direct_offset;
			LitMeaning::Eq(*self.orig_domain.lower_bound().unwrap() + 1 + offset as i64)
		};
		if lit.is_negated() {
			!meaning
		} else {
			meaning
		}
	}

	pub(crate) fn get_bool_var(&self, bv: LitMeaning) -> RawLit {
		let mut bv = bv;
		let mut negate = false;
		if matches!(bv, LitMeaning::Less(_) | LitMeaning::NotEq(_)) {
			bv = !bv;
			negate = true;
		}

		let lb = *self.orig_domain.lower_bound().unwrap();
		let lit = match bv {
			LitMeaning::GreaterEq(i) => {
				debug_assert_ne!(i, lb);
				debug_assert!(self.orig_domain.contains(&i));
				let offset = (i - lb - 1) as usize;
				debug_assert!(
					offset < self.order_vars().len(),
					"var range offset, {}, must be in [{}, {})",
					offset,
					0,
					self.order_vars().len(),
				);
				self.order_vars().index(offset).into()
			}
			LitMeaning::Eq(i) => {
				debug_assert!(self.orig_domain.contains(&i));
				let ub = *self.orig_domain.upper_bound().unwrap();
				if i == lb {
					!self.order_vars().next().unwrap()
				} else if i == ub {
					self.order_vars().next_back().unwrap().into()
				} else {
					// TODO: Fix (does not account for holes)
					let offset = (i - lb - 1) as usize;
					debug_assert!(
						offset < self.direct_vars().len(),
						"var range offset, {}, must be in [{}, {})",
						offset,
						0,
						self.direct_vars().len(),
					);
					self.direct_vars().index(offset).into()
				}
			}
			_ => unreachable!(),
		};
		if negate {
			!lit
		} else {
			lit
		}
	}

	pub(crate) fn get_value(&self, value: &dyn pindakaas::Valuation) -> i64 {
		let mut val_iter = self.orig_domain.clone().into_iter().flatten();
		for l in self.order_vars() {
			match value(l.into()) {
				Some(false) => return val_iter.next().unwrap(),
				Some(true) => {
					val_iter.next().unwrap();
				}
				None => unreachable!(),
			}
		}
		return *self.orig_domain.upper_bound().unwrap();
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LitMeaning {
	Eq(i64),
	NotEq(i64),
	GreaterEq(i64),
	Less(i64),
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
