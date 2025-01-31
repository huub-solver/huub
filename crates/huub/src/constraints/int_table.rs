//! Structures and algorithms for the integer table constraint, which
//! constraints a sequence of integer decision variable to be assigned to a set
//! of possible sequences of integer values.

use itertools::Itertools;
use pindakaas::ClauseDatabaseTools;

use crate::{
	actions::{ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	reformulate::ReformulationError,
	solver::{BoolView, IntLitMeaning},
	IntDecision, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `table_int` constraint within a model.
///
/// This constraint enforces that the given list of integer views take their
/// values according to one of the given lists of integer values.
pub struct IntTable {
	/// List of variables that must take the values of a row in the table.
	pub(crate) vars: Vec<IntDecision>,
	/// The table of possible values for the variables.
	pub(crate) table: Vec<Vec<IntVal>>,
}

impl<S: SimplificationActions> Constraint<S> for IntTable {
	fn simplify(&mut self, actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		match self.vars.len() {
			0 => return Ok(SimplificationStatus::Subsumed),
			1 => {
				let dom = self.table.iter().map(|v| v[0]..=v[0]).collect();
				actions.set_int_in_set(self.vars[0], &dom)?;
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Remove any tuples that contain values outside of the domain of the
		// variables.
		let table = self
			.table
			.iter()
			.filter(|tup| {
				tup.iter()
					.enumerate()
					.all(|(j, val)| actions.check_int_in_domain(self.vars[j], *val))
			})
			.collect_vec();

		// If no tuples remain, then the problem is trivially unsatisfiable.
		if table.is_empty() {
			return Err(ReformulationError::TrivialUnsatisfiable);
		}

		// Restrict the domain of the variables to the values it can take in the
		// tuple.
		if table.len() == 1 {
			for (j, &var) in self.vars.iter().enumerate() {
				actions.set_int_val(var, table[0][j])?;
			}
			return Ok(SimplificationStatus::Subsumed);
		}

		for (j, &var) in self.vars.iter().enumerate() {
			let dom = (0..table.len())
				.map(|i| table[i][j]..=table[i][j])
				.collect();
			actions.set_int_in_set(var, &dom)?;
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		assert!(self.vars.len() >= 2);

		let selector = if self.vars.len() != 2 {
			(0..self.table.len()).map(|_| slv.new_bool_var()).collect()
		} else {
			Vec::new()
		};
		let vars = self
			.vars
			.iter()
			.map(|&iv| slv.get_solver_int(iv))
			.collect_vec();

		// Create clauses that say foreach tuple i, if `selector[i]` is true, then the
		// variable `j` equals `vals[i][j]`.
		if vars.len() != 2 {
			for (i, tup) in self.table.iter().enumerate() {
				assert!(tup.len() == vars.len());
				for (j, var) in vars.iter().enumerate() {
					let clause = [
						!selector[i],
						slv.get_int_lit(*var, IntLitMeaning::Eq(tup[j])),
					];
					slv.add_clause(clause)?;
				}
			}
		}

		// Create clauses that map from the value taken by the variables back to the
		// possible selectors that can be active.
		for (j, var) in vars.iter().enumerate() {
			let (lb, ub) = slv.get_int_bounds(*var);
			let mut support_clauses: Vec<Vec<BoolView>> = vec![Vec::new(); (ub - lb + 1) as usize];
			for (i, tup) in self.table.iter().enumerate() {
				let k = tup[j] - lb;
				if !(0..support_clauses.len() as IntVal).contains(&k) {
					// Value is not in the domain of the variable, so this tuple should not
					// be considered.
					continue;
				}
				// Add tuple i to be in support of value `k`.
				if vars.len() == 2 {
					// Special case where we can use the values of the other variables as
					// the selection variables directly.
					support_clauses[k as usize]
						.push(slv.get_int_lit(vars[1 - j], IntLitMeaning::Eq(tup[1 - j])));
				} else {
					support_clauses[k as usize].push(selector[i]);
				}
			}
			for (i, mut clause) in support_clauses.into_iter().enumerate() {
				if slv.check_int_in_domain(*var, lb + i as IntVal) {
					clause.push(slv.get_int_lit(vars[j], IntLitMeaning::NotEq(lb + i as IntVal)));
					slv.add_clause(clause)?;
				}
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;

	use crate::{reformulate::InitConfig, table_int, Decision, Model};

	#[test]
	fn test_binary_table_sat() {
		let mut prb = Model::default();
		let vars = prb.new_int_vars(3, (1..=5).into());
		let table = vec![
			vec![1, 3],
			vec![1, 4],
			vec![2, 4],
			vec![2, 5],
			vec![3, 1],
			vec![3, 5],
			vec![4, 1],
			vec![4, 2],
			vec![5, 2],
			vec![5, 3],
		];
		prb += table_int(vec![vars[0], vars[1]], table.clone());
		prb += table_int(vec![vars[1], vars[2]], table.clone());

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::Int(x)))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    1, 3, 1
    1, 3, 5
    1, 4, 1
    1, 4, 2
    2, 4, 1
    2, 4, 2
    2, 5, 2
    2, 5, 3
    3, 1, 3
    3, 1, 4
    3, 5, 2
    3, 5, 3
    4, 1, 3
    4, 1, 4
    4, 2, 4
    4, 2, 5
    5, 2, 4
    5, 2, 5
    5, 3, 1
    5, 3, 5"#]],
		);
	}

	#[test]
	fn test_tertiary_table_sat() {
		let mut prb = Model::default();
		let vars = prb.new_int_vars(5, (1..=5).into());
		let table = vec![
			vec![1, 3, 1],
			vec![1, 3, 5],
			vec![2, 4, 2],
			vec![3, 1, 3],
			vec![3, 5, 3],
			vec![4, 2, 4],
			vec![5, 3, 1],
			vec![5, 3, 5],
		];
		prb += table_int(
			vars[0..3].iter().cloned().map_into().collect(),
			table.clone(),
		);
		prb += table_int(
			vars[2..5].iter().cloned().map_into().collect(),
			table.clone(),
		);

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::Int(x)))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    1, 3, 1, 3, 1
    1, 3, 1, 3, 5
    1, 3, 5, 3, 1
    1, 3, 5, 3, 5
    2, 4, 2, 4, 2
    3, 1, 3, 1, 3
    3, 1, 3, 5, 3
    3, 5, 3, 1, 3
    3, 5, 3, 5, 3
    4, 2, 4, 2, 4
    5, 3, 1, 3, 1
    5, 3, 1, 3, 5
    5, 3, 5, 3, 1
    5, 3, 5, 3, 5"#]],
		);
	}
}
