use super::{reason::ReasonBuilder, InitializationActions, PropagationActions};
use crate::{
	propagator::{conflict::Conflict, int_event::IntEvent, Propagator},
	solver::{
		engine::{int_var::LitMeaning, queue::PriorityLevel},
		view::{IntView, IntViewInner},
	},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct AllDifferentIntValue {
	vars: Vec<IntView>,
	action_list: Vec<u32>,
}

impl AllDifferentIntValue {
	pub(crate) fn new<V: Into<IntView>, I: IntoIterator<Item = V>>(vars: I) -> Self {
		let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
		let action_list = vars
			.iter()
			.enumerate()
			.filter_map(|(i, v)| {
				if matches!(v.0, IntViewInner::Const(_)) {
					Some(i as u32)
				} else {
					None
				}
			})
			.collect();
		Self { vars, action_list }
	}
}

impl Propagator for AllDifferentIntValue {
	fn initialize(&mut self, actions: &mut dyn InitializationActions) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Fixed, i as u32)
		}
		!self.action_list.is_empty()
	}

	fn notify_event(&mut self, data: u32, _: &IntEvent) -> bool {
		self.action_list.push(data);
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Low
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear()
	}

	#[tracing::instrument(name = "all_different", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut dyn PropagationActions) -> Result<(), Conflict> {
		while let Some(i) = self.action_list.pop() {
			let var = self.vars[i as usize];
			let val = actions.get_int_val(var).unwrap();
			let reason = ReasonBuilder::Simple(actions.get_int_lit(var, LitMeaning::Eq(val)));
			for (j, &v) in self.vars.iter().enumerate() {
				let j_val = actions.get_int_val(v);
				if (j as u32) != i && (j_val.is_none() || j_val.unwrap() == val) {
					actions.set_int_not_eq(v, val, &reason)?
				}
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use itertools::Itertools;
	use pindakaas::{solver::cadical::Cadical, Cnf};

	use crate::{
		propagator::all_different_int::AllDifferentIntValue, solver::engine::int_var::IntVar,
		IntVal, IntView, SolveResult, Solver,
	};

	#[test]
	fn test_all_different_value_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(AllDifferentIntValue::new(vec![a, b, c]));
		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique())
	}

	#[test]
	fn test_all_different_value_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(AllDifferentIntValue::new(vec![a, b, c]));
		slv.assert_unsatisfiable()
	}

	fn test_sudoku(grid: &[&str], expected: SolveResult) {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let mut all_vars = vec![];
		// create variables and add all different propagator for each row
		grid.iter().for_each(|row| {
			let mut vars = Vec::with_capacity(row.len());
			for c in row.chars() {
				if c.is_ascii_digit() {
					let num = IntVal::from(c.to_digit(10).unwrap());
					vars.push(num.into());
				} else {
					vars.push(IntVar::new_in(
						&mut slv,
						RangeList::from_iter([1..=9]),
						true,
					));
				}
			}
			slv.add_propagator(AllDifferentIntValue::new(vars.clone()));
			all_vars.push(vars);
		});
		// add all different propagator for each column
		for i in 0..9 {
			let col_vars: Vec<IntView> = (0..9).map(|j| all_vars[j][i]).collect();
			slv.add_propagator(AllDifferentIntValue::new(col_vars));
		}
		// add all different propagator for each 3 by 3 grid
		for i in 0..3 {
			for j in 0..3 {
				let mut block_vars: Vec<IntView> = Vec::with_capacity(9);
				for x in 0..3 {
					for y in 0..3 {
						block_vars.push(all_vars[3 * i + x][3 * j + y]);
					}
				}
				slv.add_propagator(AllDifferentIntValue::new(block_vars));
			}
		}
		assert_eq!(
			slv.solve(|val| {
				(0..9).for_each(|r| {
					let row = all_vars[r]
						.iter()
						.map(|v| val(v.into()).unwrap())
						.collect_vec();
					assert!(
						row.iter().all_unique(),
						"Values in row {} are not all different: {:?}",
						r,
						row
					);
				});
				(0..9).for_each(|c| {
					let col = all_vars
						.iter()
						.map(|row| val(row[c].into()).unwrap())
						.collect_vec();
					assert!(
						col.iter().all_unique(),
						"Values in column {} are not all different: {:?}",
						c,
						col
					);
				});
				(0..3).for_each(|i| {
					(0..3).for_each(|j| {
						let block = (0..3)
							.flat_map(|x| (0..3).map(move |y| (x, y)))
							.map(|(x, y)| val(all_vars[3 * i + x][3 * j + y].into()).unwrap())
							.collect_vec();
						assert!(
							block.iter().all_unique(),
							"Values in block ({}, {}) are not all different: {:?}",
							i,
							j,
							block
						);
					});
				});
			}),
			expected
		);
	}

	#[test]
	fn test_sudoku_1() {
		test_sudoku(
			&[
				"2581.4.37",
				"936827514",
				"47153.28.",
				"7152.3.4.",
				"849675321",
				"36241..75",
				"1249..753",
				"593742168",
				"687351492",
			],
			SolveResult::Satisfied,
		);
	}

	#[test]
	fn test_sudoku_2() {
		test_sudoku(
			&[
				"...2.5...",
				".9....73.",
				"..2..9.6.",
				"2.....4.9",
				"....7....",
				"6.9.....1",
				".8.4..1..",
				".63....8.",
				"...6.8...",
			],
			SolveResult::Satisfied,
		);
	}

	#[test]
	fn test_sudoku_3() {
		test_sudoku(
			&[
				"3..9.4..1",
				"..2...4..",
				".61...79.",
				"6..247..5",
				".........",
				"2..836..4",
				".46...23.",
				"..9...6..",
				"5..3.9..8",
			],
			SolveResult::Satisfied,
		);
	}

	#[test]
	fn test_sudoku_4() {
		test_sudoku(
			&[
				"....1....",
				"3.14..86.",
				"9..5..2..",
				"7..16....",
				".2.8.5.1.",
				"....97..4",
				"..3..4..6",
				".48..69.7",
				"....8....",
			],
			SolveResult::Satisfied,
		);
	}

	#[test]
	fn test_sudoku_5() {
		test_sudoku(
			&[
				"..4..3.7.",
				".8..7....",
				".7...82.5",
				"4.....31.",
				"9.......8",
				".15.....4",
				"1.69...3.",
				"....2..6.",
				".2.4..5..",
			],
			SolveResult::Satisfied,
		);
	}

	#[test]
	fn test_sudoku_6() {
		test_sudoku(
			&[
				".43.8.25.",
				"6........",
				".....1.94",
				"9....4.7.",
				"...6.8...",
				".1.2....3",
				"82.5.....",
				"........5",
				".34.9.71.",
			],
			SolveResult::Satisfied,
		);
	}
}
