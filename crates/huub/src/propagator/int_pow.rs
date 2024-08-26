use crate::{
	actions::{
		explanation::ExplanationActions, initialization::InitializationActions,
		trailing::TrailingActions,
	},
	propagator::{
		conflict::Conflict, int_event::IntEvent, reason::CachedReason, PropagationActions,
		Propagator,
	},
	solver::{
		engine::queue::PriorityLevel,
		poster::{BoxedPropagator, Poster, QueuePreferences},
	},
	IntVal, IntView, LitMeaning,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the constraint `result = base^exponent`.
pub(crate) struct IntPowBounds {
	/// The base in the exponentiation
	base: IntView,
	/// The exponent in the exponentiation
	exponent: IntView,
	/// The result of exponentiation
	result: IntView,
}

impl IntPowBounds {
	pub(crate) fn prepare(base: IntView, exponent: IntView, result: IntView) -> impl Poster {
		IntPowBoundsPoster {
			base,
			exponent,
			result,
		}
	}

	fn propagate_result<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
		let exp_largest_even = if exp_ub % 2 == 0 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_smallest_even = if exp_lb % 2 == 0 || exp_lb == exp_ub {
			exp_lb
		} else {
			exp_lb + 1
		};
		let exp_largest_uneven = if exp_ub % 2 == 1 || exp_lb == exp_ub {
			exp_ub
		} else {
			exp_ub - 1
		};
		let exp_smallest_uneven = if exp_lb % 2 == 1 || exp_lb == exp_ub {
			exp_lb
		} else {
			exp_lb + 1
		};

		let mut reason = CachedReason::new(|actions: &mut P| {
			let base_lb_lit = actions.get_int_lower_bound_lit(self.base);
			let base_ub_lit = actions.get_int_upper_bound_lit(self.base);
			let exp_lb_lit = actions.get_int_lower_bound_lit(self.exponent);
			let exp_ub_lit = actions.get_int_upper_bound_lit(self.exponent);
			vec![base_lb_lit, base_ub_lit, exp_lb_lit, exp_ub_lit]
		});

		if exp_lb == exp_ub && exp_lb == 0 {
			let exp_val_lit = actions.get_int_val_lit(self.exponent).unwrap();
			return actions.set_int_val(self.result, 1, exp_val_lit);
		}

		let base_bnd = base_lb..=base_ub;
		let min: IntVal = [
			pow(base_lb, exp_lb),             // base and exp always both positive
			pow(base_lb, exp_largest_uneven), // base maybe negative
			pow(base_ub, exp_smallest_even),  // negative base, but forced even exponent
			if base_bnd.contains(&-1) && exp_lb != exp_ub {
				Some(-1)
			} else if base_bnd.contains(&0)
				|| (base_bnd != (1..=1) && base_bnd != (-1..=-1) && exp_lb < 0)
			{
				Some(0)
			} else {
				None
			},
		]
		.into_iter()
		.flatten()
		.min()
		.unwrap();

		actions.set_int_lower_bound(self.result, min, &mut reason)?;

		let max: IntVal = vec![
			pow(base_ub, exp_ub),              // base and exp have positive upper bounds
			pow(base_lb, exp_largest_even),    // base maybe negative
			pow(base_ub, exp_smallest_uneven), // negative base, but forced uneven exponent
			if base_bnd.contains(&-1) && exp_lb != exp_ub {
				Some(1)
			} else if base_bnd.contains(&0)
				|| (base_bnd != (1..=1) && base_bnd != (-1..=-1) && exp_lb < 0)
			{
				Some(0)
			} else {
				None
			},
		]
		.into_iter()
		.flatten()
		.max()
		.unwrap();

		actions.set_int_upper_bound(self.result, max, &mut reason)?;

		Ok(())
	}

	fn propagate_base<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (res_lb, res_ub) = actions.get_int_bounds(self.result);
		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
		let exp_pos_even = match exp_lb {
			_ if exp_lb % 2 == 1 && exp_lb > 0 => exp_lb + 1,
			_ if exp_lb < 0 && exp_ub >= 2 => 2,
			_ => exp_lb,
		};
		let exp_pos_uneven = match exp_lb {
			_ if exp_lb % 2 == 0 && exp_lb > 0 => exp_lb + 1,
			_ if exp_lb < 0 && exp_ub >= 1 => 1,
			_ => exp_lb,
		};

		let mut reason = CachedReason::new(|actions: &mut P| {
			let res_lb_lit = actions.get_int_lower_bound_lit(self.result);
			let res_ub_lit = actions.get_int_upper_bound_lit(self.result);
			let exp_lb_lit = actions.get_int_lower_bound_lit(self.exponent);
			let exp_ub_lit = actions.get_int_upper_bound_lit(self.exponent);
			vec![res_lb_lit, res_ub_lit, exp_lb_lit, exp_ub_lit]
		});

		if (exp_lb..=exp_ub).contains(&0) && (res_lb..=res_ub).contains(&1) {
			return Ok(());
		}
		if exp_ub < 0 {
			let exp_neg_lit = actions.get_int_lit(self.exponent, LitMeaning::Less(0));
			return actions.set_int_not_eq(self.base, 0, exp_neg_lit);
		}
		// The following logic does not work for for negative values
		if exp_lb <= 0 || res_lb <= 0 || base_lb <= 0 {
			return Ok(());
		}

		// Propagate lower bound
		let mut min = vec![
			(res_lb as f64).powf(1_f64 / (exp_ub as f64)),
			(res_ub as f64).powf(1_f64 / (exp_pos_uneven as f64)),
			(res_lb as f64).powf(1_f64 / (exp_pos_uneven as f64)),
		]
		.into_iter()
		.reduce(|a, b| a.min(b))
		.unwrap()
		.ceil() as IntVal;

		if min > base_lb {
			// Correct possible numerical error
			if (min - 1 != 0 || exp_lb > 0)
				&& res_lb <= pow(min - 1, if min < 0 { exp_pos_uneven } else { exp_ub }).unwrap()
			{
				min -= 1;
			}
			actions.set_int_lower_bound(self.base, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = [
			(res_ub as f64).powf(1_f64 / (exp_lb as f64)),
			(res_ub as f64).powf(1_f64 / (exp_pos_uneven as f64)),
			(res_lb as f64).powf(1_f64 / (exp_pos_even as f64)),
			-((res_lb as f64).powf(1_f64 / (exp_pos_even as f64))),
		]
		.into_iter()
		.reduce(|a, b| a.max(b))
		.unwrap()
		.floor() as IntVal;

		if max < base_ub {
			// Correct possible numerical error
			if res_ub >= pow(max + 1, if min < 0 { exp_pos_even } else { exp_lb }).unwrap() {
				max += 1;
			}
			actions.set_int_upper_bound(self.base, max, &mut reason)?;
		}
		Ok(())
	}

	fn propagate_exponent<P: PropagationActions>(
		&mut self,
		actions: &mut P,
	) -> Result<(), Conflict> {
		let (base_lb, base_ub) = actions.get_int_bounds(self.base);
		let (res_lb, res_ub) = actions.get_int_bounds(self.result);

		if base_ub == base_lb && base_lb == 0 {
			let base_val_lit = actions.get_int_val_lit(self.base).unwrap();
			return actions.set_int_lower_bound(self.exponent, 0, base_val_lit);
		}
		if base_lb <= 1 || res_lb <= 1 {
			// TODO: It seems there should be propagation possible, but log2() certainly won't work.
			return Ok(());
		}

		let (exp_lb, exp_ub) = actions.get_int_bounds(self.exponent);
		let mut reason = CachedReason::new(|actions: &mut P| {
			let res_lb_lit = actions.get_int_lit(self.base, LitMeaning::GreaterEq(1));
			let res_ub_lit = actions.get_int_upper_bound_lit(self.result);
			let base_lb_lit = actions.get_int_lit(self.base, LitMeaning::GreaterEq(1));
			let base_ub_lit = actions.get_int_upper_bound_lit(self.base);
			vec![res_lb_lit, res_ub_lit, base_lb_lit, base_ub_lit]
		});

		// Propagate lower bound
		let mut min = ((res_lb as f64).log2() / (base_ub as f64).log2()).ceil() as IntVal;
		if min > exp_lb {
			// Correct possible numerical error
			if res_lb <= pow(base_lb, min - 1).unwrap() {
				min -= 1;
			}
			actions.set_int_lower_bound(self.base, min, &mut reason)?;
		}

		// Propagate upper bound
		let mut max = ((res_ub as f64).log2() / (base_lb as f64).log2()).floor() as IntVal;
		if max < exp_ub {
			// Correct possible numerical error
			if res_ub <= pow(base_ub, max + 1).unwrap() {
				max += 1;
			}
			actions.set_int_upper_bound(self.base, max, &mut reason)?;
		}

		Ok(())
	}
}

impl<P, E, T> Propagator<P, E, T> for IntPowBounds
where
	P: PropagationActions,
	E: ExplanationActions,
	T: TrailingActions,
{
	fn notify_event(&mut self, _: u32, _: &IntEvent, _: &mut T) -> bool {
		true
	}

	#[tracing::instrument(name = "int_pow", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		self.propagate_result(actions)?;
		self.propagate_base(actions)?;
		self.propagate_exponent(actions)?;

		Ok(())
	}
}

struct IntPowBoundsPoster {
	base: IntView,
	exponent: IntView,
	result: IntView,
}
impl Poster for IntPowBoundsPoster {
	fn post<I: InitializationActions + ?Sized>(
		self,
		actions: &mut I,
	) -> (BoxedPropagator, QueuePreferences) {
		actions.subscribe_int(self.base, IntEvent::Bounds, 1);
		actions.subscribe_int(self.exponent, IntEvent::Bounds, 2);
		actions.subscribe_int(self.result, IntEvent::Bounds, 3);
		(
			Box::new(IntPowBounds {
				base: self.base,
				exponent: self.exponent,
				result: self.result,
			}),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Highest,
			},
		)
	}
}

fn pow(base: IntVal, exponent: IntVal) -> Option<IntVal> {
	Some(match exponent {
		0 => 1,
		1 => base,
		exp if exp < 0 => match base {
			0 => return None,
			1 => 1,
			-1 if exp % 2 == 0 => 1,
			-1 => -1,
			_ => 0,
		},
		_ => {
			let mut result = 1;
			for _ in 0..exponent {
				result *= base;
			}
			result
		}
	})
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use tracing_test::traced_test;

	use crate::{
		propagator::int_pow::IntPowBounds,
		solver::engine::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_int_pow_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(
			&mut slv,
			(-2..=3).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			(-2..=2).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			(-2..=9).into(),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		slv.add_propagator(IntPowBounds::prepare(a, b, c));
		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			-2, -2, 0
			-2, -1, 0
			-2, 0, 1
			-2, 1, -2
			-2, 2, 4
			-1, -2, 1
			-1, -1, -1
			-1, 0, 1
			-1, 1, -1
			-1, 2, 1
			0, 0, 1
			0, 1, 0
			0, 2, 0
			1, -2, 1
			1, -1, 1
			1, 0, 1
			1, 1, 1
			1, 2, 1
			2, -2, 0
			2, -1, 0
			2, 0, 1
			2, 1, 2
			2, 2, 4
			3, -2, 0
			3, -1, 0
			3, 0, 1
			3, 1, 3
			3, 2, 9"#]],
		);
	}
}
