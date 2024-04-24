use std::ops::{Not, RangeBounds};

use flatzinc_serde::RangeList;
use itertools::Itertools;
use pindakaas::{
	solver::{PropagatingSolver, VarRange},
	Lit as RawLit,
};

use super::TrailedInt;
use crate::{
	solver::{
		view::{BoolViewInner, IntViewInner},
		IntView, SatSolver,
	},
	BoolView, IntVal, Solver,
};

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

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
			slv.core.add_clause([!ord_j, ord_i]).unwrap(); // ord_j -> ord_i
			if direct_encoding {
				let eq_i: RawLit = direct_enc_iter.next().unwrap().into();
				slv.core.add_clause([!eq_i, ord_i]).unwrap(); // eq_i -> ord_i
				slv.core.add_clause([!eq_i, !ord_j]).unwrap(); // eq_i -> !ord_j
				slv.core.add_clause([eq_i, !ord_i, ord_j]).unwrap(); // !eq_i -> !ord_i \/ ord_j
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

	pub(crate) fn get_bool_lit(&self, bv: LitMeaning) -> BoolView {
		let mut bv = bv;
		let mut negate = false;
		if matches!(bv, LitMeaning::Less(_) | LitMeaning::NotEq(_)) {
			bv = !bv;
			negate = true;
		}

		let ret_const = |b: bool| BoolView(BoolViewInner::Const(if negate { !b } else { b }));

		let lb = *self.orig_domain.lower_bound().unwrap();
		let ub = *self.orig_domain.upper_bound().unwrap();
		let lit = match bv {
			LitMeaning::GreaterEq(i) => {
				if i <= lb {
					return ret_const(true);
				} else if i > ub {
					return ret_const(false);
				}
				// Calculate the offset in the VarRange
				let mut offset = -1; // -1 to account for the lower bound
				for r in &self.orig_domain {
					if i < **r.start() {
						break;
					} else if r.contains(&&i) {
						offset += i - *r.start();
						break;
					} else {
						offset += *r.end() - *r.start() + 1;
					}
				}
				// Look up the corresponding variable
				debug_assert!(
					(offset as usize) < self.order_vars().len(),
					"var range offset, {}, must be in [{}, {})",
					offset,
					0,
					self.order_vars().len(),
				);
				self.order_vars().index(offset as usize).into()
			}
			LitMeaning::Eq(i) => {
				if i == lb {
					!self.order_vars().next().unwrap()
				} else if i == ub {
					self.order_vars().next_back().unwrap().into()
				} else if i > ub {
					return ret_const(false);
				} else {
					// Calculate the offset in the VarRange
					let mut offset = -1; // -1 to account for the lower bound
					for r in &self.orig_domain {
						if i < **r.start() {
							return ret_const(false);
						} else if r.contains(&&i) {
							offset += i - *r.start();
							break;
						} else {
							offset += *r.end() - *r.start() + 1;
						}
					}
					debug_assert!(
						(offset as usize) < self.direct_vars().len(),
						"var range offset, {}, must be in [{}, {})",
						offset,
						0,
						self.direct_vars().len(),
					);
					self.direct_vars().index(offset as usize).into()
				}
			}
			_ => unreachable!(),
		};
		BoolView(BoolViewInner::Lit(if negate { !lit } else { lit }))
	}

	pub(crate) fn get_value(&self, value: &dyn pindakaas::Valuation) -> i64 {
		let mut val_iter = self.orig_domain.clone().into_iter().flatten();
		for l in self.order_vars() {
			match value(l.into()) {
				Some(false) => return val_iter.next().unwrap(),
				Some(true) => {
					let _ = val_iter.next();
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

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		solver::{
			engine::int_var::IntVar,
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
		let a = IntVar::new_in(&mut slv, RangeList::from(1..=4), true);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &slv.engine_mut().int_vars[a];
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(2));
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(LitMeaning::Less(2));
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(3));
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(4));
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(4));
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::Eq(1));
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::Eq(2));
		assert_eq!(get_lit(lit), 4);
		let lit = a.get_bool_lit(LitMeaning::Eq(3));
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(LitMeaning::Eq(4));
		assert_eq!(get_lit(lit), 3);

		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=3, 8..=10]), true);
		let IntView(IntViewInner::VarRef(a)) = a else {
			unreachable!()
		};
		let a = &slv.engine_mut().int_vars[a];
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(2));
		assert_eq!(get_lit(lit), 1);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(3));
		assert_eq!(get_lit(lit), 2);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(4));
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(4));
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(8));
		assert_eq!(get_lit(lit), 3);
		let lit = a.get_bool_lit(LitMeaning::Less(8));
		assert_eq!(get_lit(lit), -3);
		let lit = a.get_bool_lit(LitMeaning::GreaterEq(10));
		assert_eq!(get_lit(lit), 5);
		let lit = a.get_bool_lit(LitMeaning::Less(10));
		assert_eq!(get_lit(lit), -5);
		let lit = a.get_bool_lit(LitMeaning::Eq(1)).into();
		assert_eq!(get_lit(lit), -1);
		let lit = a.get_bool_lit(LitMeaning::Eq(2)).into();
		assert_eq!(get_lit(lit), 6);
		let lit = a.get_bool_lit(LitMeaning::Eq(3)).into();
		assert_eq!(get_lit(lit), 7);
		let lit = a.get_bool_lit(LitMeaning::Eq(8)).into();
		assert_eq!(get_lit(lit), 8);
		let lit = a.get_bool_lit(LitMeaning::Eq(10)).into();
		assert_eq!(get_lit(lit), 5);

		assert_eq!(
			a.get_bool_lit(LitMeaning::GreaterEq(1)),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Less(11)),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Less(1)),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::GreaterEq(11)),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(0)),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(11)),
			BoolView(BoolViewInner::Const(false))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::Eq(5)),
			BoolView(BoolViewInner::Const(false))
		);

		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(0)),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(11)),
			BoolView(BoolViewInner::Const(true))
		);
		assert_eq!(
			a.get_bool_lit(LitMeaning::NotEq(5)),
			BoolView(BoolViewInner::Const(true))
		);
	}
}
