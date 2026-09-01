//! Value-consistent propagator for the integer `unique` constraint.
//!
//! Watches each variable for a `Fixed` event and, when one fires, removes the
//! newly fixed value from every other variable's domain. This is the cheapest
//! consistency level and exists mainly as a tie-breaker / lazy fallback that
//! the [`IntUnique`](super::IntUnique) constraint can defer to.

use itertools::Itertools;

use crate::{
	DeepClone,
	actions::{InitActions, IntEvent, IntPropCond, PostingActions, ReasonActions, ReasoningEngine},
	constraints::{IntSolverActions, Propagator},
	solver::engine::Engine,
};

/// Value consistent propagator for the integer `unique` constraint.
#[derive(Clone, Debug, DeepClone, Eq, Hash, PartialEq)]
pub struct IntUniqueValue<I> {
	/// List of integer variables that must take different values.
	vars: Vec<I>,
	/// List of (indexes of) variable signaled to be fixed.
	action_list: Vec<usize>,
}

impl<I> IntUniqueValue<I> {
	/// Whether the propagator has any pending fixed-variable actions to
	/// process — used by [`IntUnique`](super::IntUnique) to skip a redundant
	/// `propagate` call (the `propagate` body asserts the action list is
	/// non-empty).
	pub(super) fn has_pending_actions(&self) -> bool {
		!self.action_list.is_empty()
	}

	/// Create a new [`IntUniqueValue`] propagator.
	pub(crate) fn new(vars: Vec<I>) -> Self {
		Self {
			vars,
			action_list: Vec::new(),
		}
	}

	/// Create a new [`IntUniqueValue`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, vars: Vec<I>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		solver.add_propagator(Box::new(Self::new(vars)));
	}
}

impl<E, I> Propagator<E> for IntUniqueValue<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_backtrack(&mut self, _: &mut E::NotificationContext<'_>) {
		// We forget any previously remembered fixed decisions.
		self.action_list.clear();
	}

	fn advise_of_int_change(
		&mut self,
		_: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
	) -> bool {
		// We remember that the decision at index `data` has been fixed to a
		// value.
		debug_assert_eq!(event, IntEvent::Fixed);
		self.action_list.push(data as usize);
		true
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		// Let the propagator be advised when each specific decision is fixed to
		// a value, with the index of the decision.
		for (i, v) in self.vars.iter().enumerate() {
			if self.vars[i].val(ctx).is_some() {
				// If the variable is already fixed, then add it to the action
				// list immediately.
				self.action_list.push(i);
				ctx.enqueue_now(true);
			} else {
				v.advise_when(ctx, IntPropCond::Fixed, i as u64);
			}
		}
		// Advise the propagator of backtracking to clear the list of fixed
		// decision (indices).
		ctx.advise_on_backtrack();
	}

	#[tracing::instrument(
		name = "int_unique_value",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		debug_assert!(!self.action_list.is_empty() && self.action_list.iter().all_unique());
		// We walk through all fixed decisions (indices).
		for &i in &self.action_list {
			// Retrieve the value and value literal for the fixed decision.
			let val = self.vars[i].val(ctx).unwrap();
			let val_lit = self.vars[i].val_lit(ctx).unwrap();

			// We now enforce that all other decisions (at different indices)
			// are not equal to the fixed value.
			for (j, v) in self.vars.iter().enumerate() {
				if j != i {
					v.remove_val(ctx, val, |_, reason| reason.push(val_lit.clone()))?;
				}
			}
		}
		// We clear the list of indices of fixed decisions.
		self.action_list.clear();
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		constraints::int_unique::IntUniqueValue,
		solver::{LiteralStrategy, Solver, Status, Valuation},
	};

	#[test]
	#[traced_test]
	fn test_all_different_value_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=4)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueValue::post(&mut slv, vec![a, b, c]);

		slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_all_different_value_unsat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntUniqueValue::post(&mut slv, vec![a, b, c]);

		slv.assert_unsatisfiable();
	}

	fn test_sudoku(grid: &[&str], expected: Status) {
		debug_assert_eq!(grid.len(), 9);
		debug_assert!(grid.iter().all(|row| row.len() == 9));

		let mut slv: Solver = Solver::default();
		// create variables and add int_unique propagator for each row
		let all_vars: Vec<_> = grid
			.iter()
			.map(|row| {
				let vars: Vec<_> = row
					.chars()
					.map(|c| {
						if c.is_ascii_digit() {
							let num = IntVal::from(c.to_digit(10).unwrap());
							num.into()
						} else {
							slv.new_int_decision(1..=9)
								.order_literals(LiteralStrategy::Eager)
								.direct_literals(LiteralStrategy::Eager)
								.view()
						}
					})
					.collect();

				IntUniqueValue::post(&mut slv, vars.clone());
				vars
			})
			.collect();

		// add int_unique propagator for each column
		for (i, _) in grid.iter().enumerate() {
			let col_vars: Vec<_> = grid
				.iter()
				.enumerate()
				.map(|(j, _)| all_vars[j][i])
				.collect();

			IntUniqueValue::post(&mut slv, col_vars);
		}
		// add int_unique propagator for each 3 by 3 grid
		for i in 0..3 {
			for j in 0..3 {
				let mut block_vars: Vec<_> = Vec::with_capacity(grid.len());
				for x in 0..3 {
					for y in 0..3 {
						block_vars.push(all_vars[3 * i + x][3 * j + y]);
					}
				}

				IntUniqueValue::post(&mut slv, block_vars);
			}
		}
		assert_eq!(
			slv.solve()
				.on_solution(|sol| {
					(0..9).for_each(|r| {
						let row = all_vars[r].iter().map(|&v| v.val(sol)).collect_vec();
						assert!(
							row.iter().all_unique(),
							"Values in row {r} are not all different: {row:?}",
						);
					});
					(0..9).for_each(|c| {
						let col = all_vars.iter().map(|row| row[c].val(sol)).collect_vec();
						assert!(
							col.iter().all_unique(),
							"Values in column {c} are not all different: {col:?}",
						);
					});
					(0..3).for_each(|i| {
						(0..3).for_each(|j| {
							let block = (0..3)
								.flat_map(|x| (0..3).map(move |y| (x, y)))
								.map(|(x, y)| all_vars[3 * i + x][3 * j + y].val(sol))
								.collect_vec();
							assert!(
								block.iter().all_unique(),
								"Values in block ({i}, {j}) are not all different: {block:?}",
							);
						});
					});
				})
				.satisfy(),
			expected
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}

	#[test]
	#[traced_test]
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
			Status::Satisfied,
		);
	}
}
