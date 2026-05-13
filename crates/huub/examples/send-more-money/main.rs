//! # Send More Money Example
//!
//! This example solves the classic cryptarithmetic puzzle "Send More Money".
//! Each letter represents a unique digit (0-9), and the arithmetic relationship
//! must hold:
//!
//! ```text
//!   SEND
//! + MORE
//! ------
//!  MONEY
//! ```
//!
//! Leading digits S and M cannot be zero.

#[cfg(test)]
/// A macro override for `println!` that writes to the `OUTPUT` buffer instead
/// of stdout.
macro_rules! println {
    ($($tt:tt)*) => {
        let _ = writeln!(&mut OUTPUT.lock().unwrap(), $($tt)*);
    }
}

#[cfg(test)]
use std::{fmt::Write, sync::Mutex};

use huub::{
	lower::LoweringError,
	model::Model,
	solver::{Solver, Valuation},
};

#[cfg(test)]
/// A mutex-protected string buffer for storing the output (just when testing)
static OUTPUT: Mutex<String> = Mutex::new(String::new());

/// Runs the Send More Money solver and prints the solution.
pub fn main() -> Result<(), LoweringError> {
	// ANCHOR: create_model
	let mut model = Model::default();

	// Create decision variables for each letter (0-9)
	// S and M are the leading digits, so they cannot be 0
	let s = model.new_int_decision(1..=9);
	let e = model.new_int_decision(0..=9);
	let n = model.new_int_decision(0..=9);
	let d = model.new_int_decision(0..=9);

	let m = model.new_int_decision(1..=9);
	let o = model.new_int_decision(0..=9);
	let r = model.new_int_decision(0..=9);

	let y = model.new_int_decision(0..=9);
	// ANCHOR_END: create_model

	// ANCHOR: unique_constraint
	// All variables must be different
	model.unique(vec![s, e, n, d, m, o, r, y]).post()?;
	// ANCHOR_END: unique_constraint

	// ANCHOR: arithmetic_constraint
	// The arithmetic constraint: SEND + MORE = MONEY
	let send = s * 1000 + e * 100 + n * 10 + d;
	let more = m * 1000 + o * 100 + r * 10 + e;
	let money = m * 10000 + o * 1000 + n * 100 + e * 10 + y;
	model.linear(send + more).eq(money).post()?;
	// ANCHOR_END: arithmetic_constraint

	// ANCHOR: convert_to_solver
	// Convert the model to a solver
	let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	// ANCHOR_END: convert_to_solver

	// ANCHOR: map_variables
	// Map each variable so we can query its value in the solution
	let [s, e, n, d, m, o, r, y] = [s, e, n, d, m, o, r, y].map(|var| map.get(&mut solver, var));
	// ANCHOR_END: map_variables

	// ANCHOR: solve_and_print
	// Solve and print the first solution
	let _status = solver
		.solve()
		.on_solution(|sol| {
			let [s, e, n, d, m, o, r, y] = [s, e, n, d, m, o, r, y].map(|v| v.val(sol));

			let send = 1000 * s + 100 * e + 10 * n + d;
			let more = 1000 * m + 100 * o + 10 * r + e;
			let money = 10000 * m + 1000 * o + 100 * n + 10 * e + y;

			println!(
				"Solution found!

     S={s}, E={e}, N={n}, D={d}
 +   M={m}, O={o}, R={r}, E={e}
-----------------------
M={m}, O={o}, N={n}, E={e}, Y={y}

{send} + {more} = {money}"
			);
		})
		.satisfy();
	// ANCHOR_END: solve_and_print
	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn send_more_money() {
		// Run the solver, collecting its output in `OUTPUT`
		main().unwrap();

		// Parse the output to extract variable values
		let output = OUTPUT.lock().unwrap();
		let lines: Vec<&str> = output.lines().collect();

		assert_eq!(lines[0], "Solution found!");

		// Parse "     S={s}, E={e}, N={n}, D={d}"
		let s: i64 = lines[2]
			.split("S=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();
		let e: i64 = lines[2]
			.split("E=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();
		let n: i64 = lines[2]
			.split("N=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();
		let d: i64 = lines[2].split("D=").nth(1).unwrap().trim().parse().unwrap();

		// Parse " +   M={m}, O={o}, R={r}, E={}"
		let m: i64 = lines[3]
			.split("M=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();
		let o: i64 = lines[3]
			.split("O=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();
		let r: i64 = lines[3]
			.split("R=")
			.nth(1)
			.unwrap()
			.split(',')
			.next()
			.unwrap()
			.trim()
			.parse()
			.unwrap();

		// Parse "M={}, O={}, N={}, E={}, Y={y}"
		let y: i64 = lines[5].split("Y=").nth(1).unwrap().trim().parse().unwrap();

		// Parse "{send} + {more} = {money}"
		let parts: Vec<&str> = lines[7].split_whitespace().collect();
		let send: i64 = parts[0].parse().unwrap();
		let more: i64 = parts[2].parse().unwrap();
		let money: i64 = parts[4].parse().unwrap();

		// Verify all arithmetic constraints
		assert_eq!(send + more, money, "SEND + MORE should equal MONEY");
		assert_eq!(
			1000 * s + 100 * e + 10 * n + d + 1000 * m + 100 * o + 10 * r + e,
			10000 * m + 1000 * o + 100 * n + 10 * e + y,
			"SEND + MORE should equal MONEY (element-wise)"
		);
		assert_ne!(s, 0);
		assert_ne!(m, 0);

		// Verify uniqueness
		let values = vec![s, e, n, d, m, o, r, y];
		for (i, &val1) in values.iter().enumerate() {
			for &val2 in &values[i + 1..] {
				assert_ne!(val1, val2, "All values should be unique");
			}
		}

		// Verify leading digits are not zero
		assert_ne!(s, 0, "S should not be 0");
		assert_ne!(m, 0, "M should not be 0");

		// Verify the known solution
		assert_eq!(send, 9567, "SEND should be 9567");
		assert_eq!(more, 1085, "MORE should be 1085");
		assert_eq!(money, 10652, "MONEY should be 10652");
	}
}
