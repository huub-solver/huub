use pindakaas::{
	solver::{cadical::Cadical, Solver},
	ClauseDatabase, Valuation, Var,
};

#[derive(Default)]
pub struct Huub {
	sat: Cadical,
}

pub struct BoolVar(Var);

impl Huub {
	pub fn new_bool_var(&mut self) -> BoolVar {
		BoolVar(self.sat.new_var())
	}

	pub fn solve(&mut self, on_sol: impl FnMut(&dyn Valuation)) {
		self.sat.solve(on_sol);
	}
}

impl ClauseDatabase for Huub {
	fn new_var(&mut self) -> Var {
		self.sat.new_var()
	}

	fn add_clause<I: IntoIterator<Item = pindakaas::Lit>>(&mut self, cl: I) -> pindakaas::Result {
		self.sat.add_clause(cl)
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::Lit;

	use super::*;

	#[test]
	fn it_works() {
		let mut slv = Huub::default();
		let a: Lit = slv.new_var().into();
		let b: Lit = slv.new_var().into();

		slv.add_clause([!a, !b]).unwrap();
		slv.add_clause([a, b]).unwrap();

		slv.solve(|value| {
			assert_ne!(value(a), value(b));
		})
	}
}
