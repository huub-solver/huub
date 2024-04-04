use std::ops::RangeBounds;

use flatzinc_serde::RangeList;
use pindakaas::{
	solver::{PropagatingSolver, VarRange},
	BitwiseEncoder, CardinalityOne, Encoder, Lit as RawLit, Var as RawVar,
};

use crate::{
	solver::{view::IntViewInner, IntView, SatSolver},
	Solver,
};

index_vec::define_index_type! {
	/// Identifies an integer variable in a [`Solver`]
	pub struct IntVarRef = u32;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub(crate) struct IntVar {
	pub(crate) domain: RangeList<i64>,
	pub(crate) orig_domain: RangeList<i64>,
	pub(crate) one_hot: VarRange,
}

impl IntVar {
	pub(crate) fn new_in<Sat: SatSolver>(slv: &mut Solver<Sat>, domain: RangeList<i64>) -> IntView {
		let dom_size = (&domain)
			.into_iter()
			.map(|x| (*x.end() - *x.start() + 1) as usize)
			.sum();
		let vars = slv
			.core
			.next_var_range(dom_size)
			.expect("Boolean variable pool exhausted");
		BitwiseEncoder::default()
			.encode(
				&mut slv.core,
				&CardinalityOne {
					lits: vars.clone().map(Into::into).collect(),
					cmp: pindakaas::LimitComp::Equal,
				},
			)
			.unwrap();
		let iv = slv.engine_mut().int_vars.push(Self {
			orig_domain: domain.clone(),
			domain,
			one_hot: vars.clone(),
		});
		for l in vars {
			<Sat as PropagatingSolver>::add_observed_var(&mut slv.core, l);
			slv.engine_mut().bool_to_int.insert(l, iv);
		}
		IntView(IntViewInner::VarRef(iv))
	}

	pub(crate) fn map_bool_var(&self, x: RawVar) -> BoolVarMap {
		debug_assert!(self.one_hot.contains(&x));
		let v = self.one_hot.find(x);
		// TODO: Fix (does not account for holes)
		BoolVarMap::Eq(*self.orig_domain.lower_bound().unwrap() + v.unwrap() as i64)
	}

	pub(crate) fn get_bool_var(&self, bv: BoolVarMap) -> RawLit {
		match bv {
			BoolVarMap::Eq(i) => {
				debug_assert!(self.orig_domain.contains(&i));
				// TODO: Fix (does not account for holes)
				let lb = *self.orig_domain.lower_bound().unwrap();
				let offset = (i - lb) as usize;
				debug_assert!(
					offset < self.one_hot.len(),
					"var range offset, {}, must be in [0, {})",
					i - lb,
					self.one_hot.len()
				);
				self.one_hot.index(offset).into()
			}
		}
	}
}

pub(crate) enum BoolVarMap {
	Eq(i64),
}
