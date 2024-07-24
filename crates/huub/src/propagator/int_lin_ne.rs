use pindakaas::Lit as RawLit;

use crate::{
	actions::{initialization::InitializationActions, trailing::TrailingActions},
	helpers::opt_field::OptField,
	propagator::{
		conflict::Conflict, int_event::IntEvent, reason::ReasonBuilder, ExplanationActions,
		PropagationActions, Propagator,
	},
	solver::{
		engine::{queue::PriorityLevel, trail::TrailedInt},
		poster::{BoxedPropagator, Poster, QueuePreferences},
		value::IntVal,
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, Conjunction,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct IntLinearNotEqValueImpl<const R: usize> {
	/// Variables in the sumation
	vars: Vec<IntView>,
	/// Violation value
	violation: IntVal,
	/// Reified variable
	reification: OptField<R, RawLit>,
	/// Number of variables currently fixed
	num_fixed: TrailedInt,
}

pub(crate) type IntLinearNotEqValue = IntLinearNotEqValueImpl<0>;
pub(crate) type IntLinearNotEqImpValue = IntLinearNotEqValueImpl<1>;

impl IntLinearNotEqValue {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut val: IntVal,
	) -> impl Poster {
		IntLinearNotEqValuePoster::<0> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						val -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			val,
			reification: Default::default(),
		}
	}
}

impl IntLinearNotEqImpValue {
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut val: IntVal,
		r: RawLit,
	) -> impl Poster {
		IntLinearNotEqValuePoster::<1> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						val -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			val,
			reification: OptField::new(r),
		}
	}
}

impl<const R: usize, P, E, T> Propagator<P, E, T> for IntLinearNotEqValueImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
	T: TrailingActions,
{
	fn notify_event(&mut self, _: u32, _: &IntEvent, actions: &mut T) -> bool {
		let num_fixed = actions.get_trailed_int(self.num_fixed) + 1;
		let _ = actions.set_trailed_int(self.num_fixed, num_fixed);
		let size = self.vars.len() + R;
		size as i64 - num_fixed <= 1
	}

	fn notify_backtrack(&mut self, _new_level: usize) {}

	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		if let Some(r) = self.reification.get() {
			if actions.get_bool_val(BoolView(BoolViewInner::Lit(*r))) == Some(false) {
				return Ok(());
			}
		}
		let mut sum = 0;
		let mut unfixed = None;
		for (i, v) in self.vars.iter().enumerate() {
			if let Some(val) = actions.get_int_val(*v) {
				sum += val;
			} else {
				debug_assert_eq!(unfixed, None);
				unfixed = Some((i, v));
			}
		}
		if let Some((i, v)) = unfixed {
			debug_assert!(
				self.reification.get().is_none()
					|| actions.get_bool_val(BoolView(BoolViewInner::Lit(
						*self.reification.get().unwrap()
					))) == Some(true)
			);
			let val = self.violation - sum;
			actions.set_int_not_eq(*v, val, &ReasonBuilder::Lazy(i as u64))
		} else if sum == self.violation {
			let bv = if let Some(r) = self.reification.get() {
				BoolView(BoolViewInner::Lit(*r))
			} else {
				true.into()
			};
			actions.set_bool_val(bv, false, &ReasonBuilder::Lazy(self.vars.len() as u64))
		} else {
			Ok(())
		}
	}

	fn explain(&mut self, actions: &mut E, data: u64) -> Conjunction {
		let i = data as usize;
		let mut conj: Vec<_> = self
			.vars
			.iter()
			.enumerate()
			.filter_map(|(j, v)| {
				if i != j {
					match actions.get_int_val_lit(*v).unwrap().0 {
						BoolViewInner::Lit(l) => Some(l),
						BoolViewInner::Const(b) => {
							debug_assert!(b);
							None
						}
					}
				} else {
					None
				}
			})
			.collect();
		if let Some(r) = self.reification.get() {
			if i != self.vars.len() {
				conj.push(*r)
			}
		}
		conj
	}
}

struct IntLinearNotEqValuePoster<const R: usize> {
	vars: Vec<IntView>,
	val: IntVal,
	reification: OptField<R, RawLit>,
}
impl<const R: usize> Poster for IntLinearNotEqValuePoster<R> {
	fn post<I: InitializationActions>(
		self,
		actions: &mut I,
	) -> (BoxedPropagator, QueuePreferences) {
		let prop = IntLinearNotEqValueImpl {
			vars: self.vars,
			violation: self.val,
			reification: self.reification,
			num_fixed: actions.new_trailed_int(0),
		};
		for (i, v) in prop.vars.iter().enumerate() {
			actions.subscribe_int(*v, IntEvent::Fixed, i as u32)
		}
		if let Some(r) = prop.reification.get() {
			actions.subscribe_bool(BoolView(BoolViewInner::Lit(*r)), prop.vars.len() as u32)
		}
		(
			Box::new(prop),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Low,
			},
		)
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::Cadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		propagator::int_lin_ne::IntLinearNotEqValue,
		solver::engine::int_var::{EncodingType, IntVar},
		Constraint, InitConfig, Model, NonZeroIntVal, Solver,
	};

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv: Solver<Cadical> = Cnf::default().into();
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		slv.add_propagator(IntLinearNotEqValue::prepare(
			vec![a * NonZeroIntVal::new(2).unwrap(), b, c],
			6,
		));

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
    1, 1, 1
    1, 1, 2
    1, 2, 1
    2, 1, 2
    2, 2, 1
    2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ne_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::IntLinNotEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(2).unwrap(),
				b.clone(),
				c.clone(),
			],
			6,
			r.clone().into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
    false, 1, 1, 1
    false, 1, 1, 2
    false, 1, 2, 1
    false, 1, 2, 2
    false, 2, 1, 1
    false, 2, 1, 2
    false, 2, 2, 1
    false, 2, 2, 2
    true, 1, 1, 1
    true, 1, 1, 2
    true, 1, 2, 1
    true, 2, 1, 2
    true, 2, 2, 1
    true, 2, 2, 2"#]],
		);
	}
}
