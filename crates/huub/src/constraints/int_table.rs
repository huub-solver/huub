//! Structures and algorithms for the integer table constraint, which
//! constraints a sequence of integer decision variable to be assigned to a set
//! of possible sequences of integer values.

use std::mem;

use itertools::Itertools;

use crate::{
	IntVal,
	actions::{
		InitActions, IntDecisionActions, IntInitActions, IntInspectionActions,
		IntPropagationActions, IntSimplificationActions, PropagationActions, ReasoningEngine,
	},
	constraints::{
		Constraint, IntModelActions, IntSolverActions, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
	model::View,
	solver::{IntLitMeaning, activation_list::IntPropCond, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `table_int` constraint within a model.
///
/// This constraint enforces that the given list of integer views take their
/// values according to one of the given lists of integer values.
pub struct IntTable {
	/// List of variables that must take the values of a row in the table.
	pub(crate) vars: Vec<View<IntVal>>,
	/// The table of possible values for the variables.
	pub(crate) table: Vec<Vec<IntVal>>,
}

impl<E> Constraint<E> for IntTable
where
	E: ReasoningEngine,
	View<IntVal>: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		match self.vars.len() {
			0 => return Ok(SimplificationStatus::Subsumed),
			1 => {
				let dom = self.table.iter().map(|v| v[0]..=v[0]).collect();
				self.vars[0].restrict_domain(ctx, &dom, [])?;
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Remove any tuples that contain values outside of the domain of the
		// variables.
		self.table = mem::take(&mut self.table)
			.into_iter()
			.filter(|tup| {
				tup.iter()
					.enumerate()
					.all(|(j, val)| self.vars[j].in_domain(ctx, *val))
			})
			.collect_vec();

		// If no tuples remain, then the problem is trivially unsatisfiable.
		if self.table.is_empty() {
			return Err(ctx.declare_conflict([]));
		}

		// Restrict the domain of the variables to the values it can take in the
		// tuple.
		if self.table.len() == 1 {
			for (j, &var) in self.vars.iter().enumerate() {
				var.fix(ctx, self.table[0][j], [])?;
			}
			return Ok(SimplificationStatus::Subsumed);
		}

		for (j, &var) in self.vars.iter().enumerate() {
			let dom = (0..self.table.len())
				.map(|i| self.table[i][j]..=self.table[i][j])
				.collect();
			var.restrict_domain(ctx, &dom, [])?;
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		assert!(self.vars.len() >= 2);

		let selector = if self.vars.len() != 2 {
			(0..self.table.len())
				.map(|_| slv.new_bool_decision())
				.collect()
		} else {
			Vec::new()
		};
		let vars = self
			.vars
			.iter()
			.map(|&iv| slv.solver_view(iv))
			.collect_vec();

		// Create clauses that say foreach tuple i, if `selector[i]` is true, then the
		// variable `j` equals `vals[i][j]`.
		if vars.len() != 2 {
			for (i, tup) in self.table.iter().enumerate() {
				assert!(tup.len() == vars.len());
				for (j, var) in vars.iter().enumerate() {
					let clause = [!selector[i], var.lit(slv, IntLitMeaning::Eq(tup[j]))];
					slv.add_clause(clause)?;
				}
			}
		}

		// Create clauses that map from the value taken by the variables back to the
		// possible selectors that can be active.
		for (j, var) in vars.iter().enumerate() {
			let (lb, ub) = var.bounds(slv);
			let mut support_clauses: Vec<Vec<_>> = vec![Vec::new(); (ub - lb + 1) as usize];
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
						.push(vars[1 - j].lit(slv, IntLitMeaning::Eq(tup[1 - j])));
				} else {
					support_clauses[k as usize].push(selector[i]);
				}
			}
			for (i, mut clause) in support_clauses.into_iter().enumerate() {
				if var.in_domain(slv, lb + i as IntVal) {
					clause.push(vars[j].lit(slv, IntLitMeaning::NotEq(lb + i as IntVal)));
					slv.add_clause(clause)?;
				}
			}
		}

		Ok(())
	}
}

impl<E> Propagator<E> for IntTable
where
	E: ReasoningEngine,
	View<IntVal>: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for var in &self.vars {
			var.enqueue_when(ctx, IntPropCond::Domain);
		}
	}

	fn propagate(&mut self, _: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		unreachable!()
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;

	use crate::{Model, lower::InitConfig};

	#[test]
	fn test_binary_table_sat() {
		let mut prb = Model::default();
		let vars = prb.new_int_decisions(3, 1..=5);
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
		prb.table(vec![vars[0], vars[1]])
			.values(table.clone())
			.post();
		prb.table(vec![vars[1], vars[2]])
			.values(table.clone())
			.post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars.into_iter().map(|x| map.get(&mut slv, x)).collect_vec();
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
		let vars = prb.new_int_decisions(5, 1..=5);
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
		prb.table(vars[0..3].iter().cloned())
			.values(table.clone())
			.post();
		prb.table(vars[2..5].iter().cloned())
			.values(table.clone())
			.post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars.into_iter().map(|x| map.get(&mut slv, x)).collect_vec();
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
