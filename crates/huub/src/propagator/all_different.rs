use tracing::trace;

use super::reason::ReasonBuilder;
use crate::{
	propagator::{
		conflict::Conflict, init_action::InitializationActions, int_event::IntEvent,
		propagation_action::PropagationActions, Initialize, Propagator,
	},
	solver::{
		engine::{int_var::LitMeaning, queue::PriorityLevel},
		view::IntViewInner,
		IntView, SatSolver,
	},
};

#[derive(Debug)]
pub(crate) struct AllDifferentValue {
	vars: Vec<IntView>,
	action_list: Vec<u32>,
}

impl AllDifferentValue {
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

impl Propagator for AllDifferentValue {
	fn notify_event(&mut self, data: u32) -> bool {
		self.action_list.push(data);
		true
	}

	fn queue_priority_level(&self) -> PriorityLevel {
		PriorityLevel::Low
	}

	fn notify_backtrack(&mut self, _new_level: usize) {
		self.action_list.clear()
	}

	fn propagate(&mut self, actions: &mut PropagationActions<'_>) -> Result<(), Conflict> {
		while let Some(i) = self.action_list.pop() {
			trace!("Propagating all different value for variable {}", i);
			trace!(
				"Variable {} domain upper bound {} and lower bound {}",
				i,
				actions.get_int_upper_bound(self.vars[i as usize]),
				actions.get_int_lower_bound(self.vars[i as usize])
			);
			let var = self.vars[i as usize];
			let val = actions.get_int_val(var).unwrap();
			let reason = ReasonBuilder::Simple(actions.get_int_lit(var, LitMeaning::Eq(val)));
			for (j, &v) in self.vars.iter().enumerate() {
				let j_val = actions.get_int_val(v);
				if (j as u32) != i && (j_val.is_none() || j_val.unwrap() == val) {
					actions.set_int_not_eq(v, val, reason.clone())?
				}
			}
		}
		Ok(())
	}
}

impl Initialize for AllDifferentValue {
	fn initialize<Sat: SatSolver>(&mut self, actions: &mut InitializationActions<'_, Sat>) -> bool {
		for (i, v) in self.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Fixed, i as u32)
		}
		!self.action_list.is_empty()
	}
}

#[cfg(test)]
mod tests {
	use flatzinc_serde::RangeList;
	use itertools::Itertools;
	use pindakaas::{
		solver::{cadical::Cadical, SolveResult},
		Cnf,
	};

	use crate::{
		propagator::all_different::AllDifferentValue,
		solver::engine::int_var::{IntVal, IntVar},
		IntView, Solver,
	};

	#[test]
	fn test_all_different_value_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=4]), true);

		slv.add_propagator(AllDifferentValue::new(vec![a, b, c]));
		assert_eq!(
			slv.solve(|val| {
				assert_ne!(val(a.into()), val(b.into()));
				assert_ne!(val(b.into()), val(c.into()));
				assert_ne!(val(a.into()), val(c.into()));
			}),
			SolveResult::Sat
		)
	}

	#[test]
	fn test_all_different_value_unsat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let b = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);
		let c = IntVar::new_in(&mut slv, RangeList::from_iter([1..=2]), true);

		slv.add_propagator(AllDifferentValue::new(vec![a, b, c]));
		assert_eq!(slv.solve(|_| { unreachable!() }), SolveResult::Unsat)
	}

	fn test_sudoku(grid: Vec<String>, expected: SolveResult) {
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
			slv.add_propagator(AllDifferentValue::new(vars.clone()));
			all_vars.push(vars);
		});
		// add all different propagator for each column
		for i in 0..9 {
			let col_vars: Vec<IntView> = (0..9).map(|j| all_vars[j][i]).collect();
			slv.add_propagator(AllDifferentValue::new(col_vars));
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
				slv.add_propagator(AllDifferentValue::new(block_vars));
			}
		}
		assert_eq!(
			slv.solve(|val| {
				for i in &all_vars {
					for j in i {
						eprint!("{:?}", val(j.into()).unwrap())
					}
					eprintln!()
				}
				(0..9).for_each(|r| {
					assert!(
						all_vars[r]
							.iter()
							.map(|v| val(v.into()).unwrap())
							.all_unique(),
						"Values in row {} are not all different",
						r
					);
				});
				(0..9).for_each(|c| {
					assert!(
						all_vars
							.iter()
							.map(|row| val(row[c].into()).unwrap())
							.all_unique(),
						"Values in column {} are not all different",
						c
					);
				});
				(0..3).for_each(|i| {
					(0..3).for_each(|j| {
						assert!(
							(0..3)
								.flat_map(|x| (0..3).map(move |y| (x, y)))
								.map(|(x, y)| val(all_vars[3 * i + x][3 * j + y].into()).unwrap())
								.all_unique(),
							"Values in block ({}, {}) are not all different",
							i,
							j
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
			vec![
				"2581.4.37".to_string(),
				"936827514".to_string(),
				"47153.28.".to_string(),
				"7152.3.4.".to_string(),
				"849675321".to_string(),
				"36241..75".to_string(),
				"1249..753".to_string(),
				"593742168".to_string(),
				"687351492".to_string(),
			],
			SolveResult::Sat,
		);
	}

	#[test]
	fn test_sudoku_2() {
		test_sudoku(
			vec![
				"...2.5...".to_string(),
				".9....73.".to_string(),
				"..2..9.6.".to_string(),
				"2.....4.9".to_string(),
				"....7....".to_string(),
				"6.9.....1".to_string(),
				".8.4..1..".to_string(),
				".63....8.".to_string(),
				"...6.8...".to_string(),
			],
			SolveResult::Sat,
		);
	}

	#[test]
	fn test_sudoku_3() {
		test_sudoku(
			vec![
				"3..9.4..1".to_string(),
				"..2...4..".to_string(),
				".61...79.".to_string(),
				"6..247..5".to_string(),
				".........".to_string(),
				"2..836..4".to_string(),
				".46...23.".to_string(),
				"..9...6..".to_string(),
				"5..3.9..8".to_string(),
			],
			SolveResult::Sat,
		);
	}

	#[test]
	fn test_sudoku_4() {
		test_sudoku(
			vec![
				"....1....".to_string(),
				"3.14..86.".to_string(),
				"9..5..2..".to_string(),
				"7..16....".to_string(),
				".2.8.5.1.".to_string(),
				"....97..4".to_string(),
				"..3..4..6".to_string(),
				".48..69.7".to_string(),
				"....8....".to_string(),
			],
			SolveResult::Sat,
		);
	}

	#[test]
	fn test_sudoku_5() {
		test_sudoku(
			vec![
				"..4..3.7.".to_string(),
				".8..7....".to_string(),
				".7...82.5".to_string(),
				"4.....31.".to_string(),
				"9.......8".to_string(),
				".15.....4".to_string(),
				"1.69...3.".to_string(),
				"....2..6.".to_string(),
				".2.4..5..".to_string(),
			],
			SolveResult::Sat,
		);
	}

	#[test]
	fn test_sudoku_6() {
		test_sudoku(
			vec![
				".43.8.25.".to_string(),
				"6........".to_string(),
				".....1.94".to_string(),
				"9....4.7.".to_string(),
				"...6.8...".to_string(),
				".1.2....3".to_string(),
				"82.5.....".to_string(),
				"........5".to_string(),
				".34.9.71.".to_string(),
			],
			SolveResult::Sat,
		);
	}
}
