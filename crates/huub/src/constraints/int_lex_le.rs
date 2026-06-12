//! Structure and algorithms for the `lex_le` constraint, which enforces that
//! one tuple of integer decisions is lexicographically smaller than or equal to
//! another tuple of equal length.
//!
//! The propagator compares the two tuples position by position. As long as the
//! most significant positions are fixed and equal, the order is decided by the
//! first position at which the tuples differ. The propagator therefore tracks
//! the length of the fixed-equal prefix (the `start` pointer) and, at the first
//! undecided position, enforces `left_i <= right_i`. When a later position is
//! already forced to make `left` larger than `right`, the order has to be
//! decided strictly at the current position, so `left_i < right_i` is enforced
//! instead.
//!
//! Tuples of unequal length, and the strict variants, are handled by the model
//! layer (see [`Model::lex`](crate::model::Model::lex)), which reduces every
//! lexicographic order to an equal-length non-strict core constraint, turning a
//! required strict order into a non-strict one by adding one to the last
//! compared element of `left`. The model layer additionally simplifies the
//! constraint after propagation (dropping the fixed-equal prefix, and the first
//! position that already guarantees `left < right` together with everything
//! after it). Finally, when one tuple has lowered to a constant,
//! [`Constraint::to_solver`] replaces the propagator by a half-reified clausal
//! chain (one auxiliary Boolean per position) rather than running the
//! propagator.

use bon::Builder;

use crate::{
	Conjunction, IntVal,
	actions::{
		ConstructionActions, InitActions, IntDecisionActions, IntEvent, IntInspectionActions,
		IntPropCond, PostingActions, PropagationActions, ReasoningEngine, SimplificationActions,
		Trailed, TrailingActions,
	},
	constraints::{
		BoolModelActions, Constraint, DeferredReason, IntModelActions, IntSolverActions,
		Propagator, SimplificationStatus,
		int_lex_le::lex_reason_builder::IsComplete,
		int_linear::{IntLinear, LinComparator},
	},
	helpers::overflow::OverflowImpossible,
	lower::{LoweringContext, LoweringError},
	model,
	solver::{IntLitMeaning, Polarity, View, engine::Engine, queue::PriorityLevel},
};

/// Bounds propagator for the `lex_le` constraint between two equal-length
/// tuples of integer decisions.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntLexLeBounds<I> {
	/// Pairs `(left_i, right_i)` of corresponding decisions in the two tuples,
	/// ordered from the most to the least significant position. The constraint
	/// requires the tuple of all `left_i` to be lexicographically smaller than
	/// or equal to the tuple of all `right_i`.
	position: Vec<(I, I)>,
	/// Length of the prefix that is currently known to be fixed and pairwise
	/// equal (i.e. `left_j == right_j` for all `j < start_at`). The
	/// lexicographic order is decided at the first position at or after this
	/// pointer.
	start_at: Trailed<usize>,
}

/// The premises, beyond the equal prefix, that a bound derived at a given
/// position depends on.
///
/// A bound is propagated with a [deferred
/// reason](PropagationActions::deferred_reason), whose `u64` payload is the
/// [encoding](u64::from) of this object. When the reason is needed,
/// [`Propagator::explain`] [decodes](Self::from) it and reconstructs the
/// explanation: the equal prefix up to `position`, plus whichever of the
/// flagged premises were used to derive the bound.
#[derive(Builder, Clone, Copy, Debug)]
#[builder(start_fn = at, finish_fn = build_internal)]
#[allow(
	clippy::missing_docs_in_private_items,
	reason = "bon copies the start_fn member into the builder struct as an undocumented private field"
)]
struct LexReason {
	/// Position at which the bound was derived.
	#[builder(start_fn)]
	position: usize,
	/// The explanation includes the upper bound of `right` (`right <=
	/// max(right)`).
	#[builder(default)]
	right_max: bool,
	/// The explanation includes the lower bound of `left` (`left >=
	/// min(left)`).
	#[builder(default)]
	left_min: bool,
	/// The explanation includes the witness that the next position already
	/// forces `left > right`, so the order must be decided strictly at
	/// `position`.
	#[builder(default)]
	strict_witness: bool,
}

/// Encode `lex_le` against a fully-fixed constant tuple as a half-reified chain
/// of clauses, introducing one auxiliary Boolean per position.
///
/// `prefix_eq` is a literal that holds while every earlier position equals the
/// constant, so the order is still undecided. At each position it forces the
/// variable to respect the bound implied by the constant and, if the values are
/// still equal, propagates "prefix equal" to the next position. Only the
/// implication direction (`prefix_eq -> …`) is needed, which keeps the encoding
/// to O(n) clauses and avoids reifying the conjunctions. When `constant_left`,
/// the constant tuple is the left operand (`c <=lex right`); otherwise it is
/// the right operand (`left <=lex c`).
fn decompose(
	slv: &mut LoweringContext<'_>,
	position: &[(View<IntVal>, View<IntVal>)],
	constant_left: bool,
) -> Result<(), LoweringError> {
	// `prefix_eq` for the first position is the constant `true`.
	let mut prefix_eq: View<bool> = true.into();
	for (i, &(left, right)) in position.iter().enumerate() {
		// `within`: the variable respects the bound implied by the constant.
		// `strict`: the variable is strictly past it, deciding the order here.
		let (within, strict) = if constant_left {
			// `left` is the constant `c`; enforce `c <= right`, i.e. `right >= c`.
			let c = left.bounds(slv).0;
			let strict = if c == IntVal::MAX {
				false.into()
			} else {
				right.lit(slv, IntLitMeaning::GreaterEq(c + 1))
			};
			(right.lit(slv, IntLitMeaning::GreaterEq(c)), strict)
		} else {
			// `right` is the constant `c`; enforce `left <= c`, i.e. `left < c + 1`.
			let c = right.bounds(slv).0;
			let within = if c == IntVal::MAX {
				true.into()
			} else {
				left.lit(slv, IntLitMeaning::Less(c + 1))
			};
			(within, left.lit(slv, IntLitMeaning::Less(c)))
		};
		// `prefix_eq -> within`.
		slv.add_clause([!prefix_eq, within])?;
		if i + 1 < position.len() {
			let next = slv.new_bool_decision();
			// `prefix_eq -> (strict ∨ next)`.
			slv.add_clause([!prefix_eq, strict, next])?;
			prefix_eq = next;
		}
	}
	Ok(())
}

impl<I> IntLexLeBounds<I> {
	/// Create a new [`IntLexLeBounds`] propagator, to be used within the given
	/// engine.
	pub(crate) fn new<E>(engine: &mut E, position: Vec<(I, I)>) -> Self
	where
		E: ConstructionActions + ?Sized,
	{
		Self {
			position,
			start_at: engine.new_trailed(0_usize),
		}
	}

	/// Create a new [`IntLexLeBounds`] propagator and post it in the
	/// [`Solver`](crate::solver::Solver).
	pub fn post<E>(solver: &mut E, position: Vec<(I, I)>)
	where
		E: PostingActions + ?Sized,
		I: IntSolverActions<Engine>,
	{
		let con = IntLexLeBounds::new(solver, position);
		solver.add_propagator(Box::new(con));
	}
}

impl<E, I> Constraint<E> for IntLexLeBounds<I>
where
	E: ReasoningEngine,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	I: IntModelActions<E>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		for (left, right) in &self.position {
			left.polarity(ctx, Polarity::Negative);
			right.polarity(ctx, Polarity::Positive);
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		// Structurally shrink the tuple, compacting the survivors in place. After
		// propagation `start_at` marks the fixed-equal prefix, so the scan starts
		// there.
		let start = ctx.trailed(self.start_at);
		let mut i = 0;
		for old in start..self.position.len() {
			let (left, right) = &self.position[old];
			if left.max(ctx) < right.min(ctx) {
				// This position guarantees `left_i < right_i`, so this position and everything
				// after it is dropped.
				break;
			}
			let violated_pos = left.min(ctx) > right.max(ctx);
			let left_val = left.val(ctx);
			let keep = left_val.is_none() || left_val != right.val(ctx);
			if keep {
				self.position.swap(i, old);
				i += 1;
			}
			if violated_pos {
				// This position violates `left_i <= right_i`; So one of the previous
				// positions must be strict, and all further positions can be dropped.
				break;
			}
		}
		self.position.truncate(i);
		let _ = ctx.set_trailed(self.start_at, 0);

		// An empty tuple means the two tuples are equal, or the order was already
		// decided; either way the non-strict order is satisfied. A fully-fixed
		// constraint always reduces to this case. Otherwise the decomposition into
		// clauses, when one side is fixed, is deferred to `to_solver` (where
		// auxiliary Boolean decisions can be created).
		let post_as_linear = |ctx: &mut E::PropagationContext<'_>, left_offset: IntVal| {
			ctx.post_constraint(IntLinear::<OverflowImpossible> {
				terms: vec![
					self.position[0].0.clone().into(),
					-(self.position[0].1.clone().into()),
				],
				comparator: LinComparator::LessEq,
				rhs: -left_offset,
				reif: None,
			});
		};
		match self.position.len() {
			0 => Ok(SimplificationStatus::Subsumed),
			1 => {
				post_as_linear(ctx, 0);
				Ok(SimplificationStatus::Subsumed)
			}
			// The second position is forced to be violated (`left_1 > right_1`
			// always), so the order must be decided strictly at the first.
			2 if self.position[1].0.min(ctx) > self.position[1].1.max(ctx) => {
				post_as_linear(ctx, 1);
				Ok(SimplificationStatus::Subsumed)
			}
			_ => Ok(SimplificationStatus::NoFixpoint),
		}
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let mut position: Vec<_> = self
			.position
			.iter()
			.map(|(left, right)| {
				(
					slv.solver_view(left.clone().into()),
					slv.solver_view(right.clone().into()),
				)
			})
			.collect();
		debug_assert!(position.len() > 1, "constraint should have been simplified");

		// Small optimization: when the last position is forced to be violated, the
		// order must be strictly enforced before it.
		if let Some((left, right)) = position.last()
			&& left.min(slv) > right.max(slv)
		{
			position.pop();
			if position.last().unwrap().0.max(slv) != IntVal::MAX {
				let (l, _) = position.last_mut().unwrap();
				*l = *l + 1;
			} else {
				position.push((1.into(), 0.into()));
			}
		}

		// If one tuple lowered entirely to fixed values, replace the propagator by
		// a clausal decomposition against that constant tuple.
		let mut left_const = true;
		let mut right_const = true;
		for (left, right) in &position {
			left_const &= left.val(slv).is_some();
			right_const &= right.val(slv).is_some();
		}
		if right_const {
			return decompose(slv, &position, false);
		}
		if left_const {
			return decompose(slv, &position, true);
		}
		IntLexLeBounds::post(slv, position);
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntLexLeBounds<I>
where
	E: ReasoningEngine,
	I: IntSolverActions<E>,
{
	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		_: IntEvent,
	) -> bool {
		let start = ctx.trailed(self.start_at);
		data as usize <= start + 1
	}

	fn explain(
		&mut self,
		ctx: &mut E::ExplanationContext<'_>,
		_lit: E::Atom,
		data: u64,
	) -> Conjunction<E::Atom> {
		// The data identifies the position at which the bound was derived and which
		// premises beyond the equal prefix are required.
		let LexReason {
			position,
			right_max,
			left_min,
			strict_witness,
		} = data.into();
		let mut reason = Vec::new();
		for j in 0..position {
			let (left, right) = &self.position[j];
			if let Some(lit) = left.try_val_lit(ctx) {
				reason.push(lit);
			} else {
				reason.push(left.min_lit(ctx));
				reason.push(left.max_lit(ctx));
			}
			if let Some(lit) = right.try_val_lit(ctx) {
				reason.push(lit);
			} else {
				reason.push(right.min_lit(ctx));
				reason.push(right.max_lit(ctx));
			}
		}
		let (left, right) = &self.position[position];
		if right_max {
			reason.push(right.max_lit(ctx));
		}
		if left_min {
			reason.push(left.min_lit(ctx));
		}
		if strict_witness && position + 1 < self.position.len() {
			let (next_left, next_right) = &self.position[position + 1];
			reason.push(next_left.min_lit(ctx));
			reason.push(next_right.max_lit(ctx));
		}
		reason
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::High);

		for (i, (left, right)) in self.position.iter().enumerate() {
			if i <= 1 {
				left.enqueue_when(ctx, IntPropCond::LowerBound);
				right.enqueue_when(ctx, IntPropCond::UpperBound);
			} else {
				left.advise_when(ctx, IntPropCond::LowerBound, i as u64);
				right.advise_when(ctx, IntPropCond::UpperBound, i as u64);
			}
		}
	}

	#[tracing::instrument(
		name = "int_lex_le_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let n = self.position.len();
		let start = ctx.trailed(self.start_at);
		for i in start..n {
			// Every bound derived at position `i` shares the same equal-prefix
			// premise, which is expensive to build, so all explanations are deferred
			// and reconstructed in `explain` only if a conflict needs them. The
			// `LexReason` records which extra premises each derivation used.
			let (left, right) = &self.position[i];
			let (left_min, left_max) = left.bounds(ctx);
			let (right_min, right_max) = right.bounds(ctx);

			// (1) If `left_i < right_i` is already guaranteed, the order holds regardless
			// of the remaining positions and nothing more needs to be enforced.
			if left_max < right_min {
				return Ok(());
			}

			// (2) All earlier positions are fixed and equal, so the order requires
			// `left_i <= right_i`. The bound on `left_i` is explained by the upper bound of
			// `right_i` (and vice versa), together with the equal prefix.
			let reason = LexReason::at(i).right_max(true).build(ctx);
			left.tighten_max(ctx, right_max, reason)?;
			let reason = LexReason::at(i).left_min(true).build(ctx);
			right.tighten_min(ctx, left_min, reason)?;

			// (3) When the next position already forces `left_{i+1} > right_{i+1}`, the
			// order cannot be decided there, so it must be decided strictly here:
			// `left_i < right_i`.
			if let Some((next_left, next_right)) = self.position.get(i + 1)
				&& next_left.min(ctx) > next_right.max(ctx)
			{
				// `left_i < right_i` is unsatisfiable when no integer can sit strictly
				// between the bounds: either `right_i` is pinned to the smallest
				// representable value, or `left_i` to the largest. Detecting this also
				// keeps the `- 1`/`+ 1` below from overflowing.
				if right_max == IntVal::MIN || left_min == IntVal::MAX {
					let reason = LexReason::at(i)
						.right_max(true)
						.left_min(true)
						.strict_witness(true)
						.build(ctx);
					return Err(ctx.declare_conflict(reason));
				}
				let reason = LexReason::at(i)
					.right_max(true)
					.strict_witness(true)
					.build(ctx);
				left.tighten_max(ctx, right_max - 1, reason)?;
				let reason = LexReason::at(i)
					.left_min(true)
					.strict_witness(true)
					.build(ctx);
				right.tighten_min(ctx, left_min + 1, reason)?;
				// The order is now decided at position `i`; the suffix is free.
				return Ok(());
			}

			// (4) Advance the equal-prefix frontier only when position `i` has
			// become fixed and equal; otherwise the order is still undecided here
			// and no later position may be constrained yet.
			match (left.val(ctx), right.val(ctx)) {
				(Some(a), Some(b)) => {
					debug_assert_eq!(a, b);
					let _ = ctx.set_trailed(self.start_at, i + 1);
				}
				_ => return Ok(()),
			}
		}

		// The whole prefix is fixed and equal, i.e. the two tuples are identical,
		// which satisfies the non-strict order.
		Ok(())
	}
}

impl LexReason {
	/// Number of low bits of the `u64` encoding reserved for the flags; the
	/// remaining high bits hold the position index.
	const INDEX_SHIFT: u64 = 3;
	/// Bit marking that the explanation includes the lower bound of `left`
	/// (`left >= min(left)`).
	const LEFT_MIN: u64 = 0b010;
	/// Bit marking that the explanation includes the upper bound of `right`
	/// (`right <= max(right)`).
	const RIGHT_MAX: u64 = 0b001;
	/// Bit marking that the explanation includes the strict witness, that the
	/// next position already forces `left > right`.
	const STRICT_WITNESS: u64 = 0b100;
}

impl From<u64> for LexReason {
	fn from(data: u64) -> Self {
		Self {
			position: (data >> LexReason::INDEX_SHIFT) as usize,
			right_max: data & LexReason::RIGHT_MAX != 0,
			left_min: data & LexReason::LEFT_MIN != 0,
			strict_witness: data & LexReason::STRICT_WITNESS != 0,
		}
	}
}

impl<S: lex_reason_builder::State> LexReasonBuilder<S> {
	/// Finish building the reason and register it as a [deferred
	/// reason](PropagationActions::deferred_reason) in the given context,
	/// encoding the [`LexReason`] into the reason's `u64` payload.
	fn build<Ctx>(self, ctx: &mut Ctx) -> DeferredReason
	where
		Ctx: PropagationActions,
		S: IsComplete,
	{
		ctx.deferred_reason(self.build_internal().into())
	}
}

impl From<LexReason> for u64 {
	fn from(reason: LexReason) -> u64 {
		let mut data = (reason.position as u64) << LexReason::INDEX_SHIFT;
		if reason.right_max {
			data |= LexReason::RIGHT_MAX;
		}
		if reason.left_min {
			data |= LexReason::LEFT_MIN;
		}
		if reason.strict_witness {
			data |= LexReason::STRICT_WITNESS;
		}
		data
	}
}

#[cfg(test)]
mod tests {
	use std::ops::RangeInclusive;

	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		actions::{IntDecisionActions, IntInspectionActions},
		constraints::int_lex_le::IntLexLeBounds,
		model::Model,
		solver::{IntLitMeaning, LiteralStrategy, Solver, View},
	};

	/// Create an integer decision with the given domain and eager literals, so
	/// that the propagator's reasoning is fully observable.
	fn dcn(slv: &mut Solver, domain: RangeInclusive<IntVal>) -> View<IntVal> {
		slv.new_int_decision(domain)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view()
	}

	#[test]
	#[traced_test]
	fn test_lex_propagation() {
		// Each block posts the propagator once and checks the single propagation
		// step it performs: the input domains, and the domains it produces.

		// `left_0 <= right_0` tightens both bounds towards each other (and nothing
		// else).
		{
			let mut slv = Solver::default();
			let left = dcn(&mut slv, 2..=5);
			let right = dcn(&mut slv, 0..=3);
			IntLexLeBounds::post(&mut slv, vec![(left, right)]);
			let propagated = slv.propagate_next().unwrap();
			assert_eq!(left.bounds(&slv), (2, 3));
			assert_eq!(right.bounds(&slv), (2, 3));
			assert_eq!(
				propagated,
				vec![
					left.lit(&mut slv, IntLitMeaning::Less(4)),
					right.lit(&mut slv, IntLitMeaning::GreaterEq(2)),
				]
			);
		}

		// `left_0 < right_0` is already guaranteed, so nothing is propagated.
		{
			let mut slv = Solver::default();
			let left = dcn(&mut slv, 0..=1);
			let right = dcn(&mut slv, 3..=4);
			IntLexLeBounds::post(&mut slv, vec![(left, right)]);
			assert!(slv.propagate_next().unwrap().is_empty());
			assert_eq!(left.bounds(&slv), (0, 1));
			assert_eq!(right.bounds(&slv), (3, 4));
		}

		// A fixed-equal first position advances the frontier, after which the
		// second position is bounded by `left_1 <= right_1`.
		{
			let mut slv = Solver::default();
			let left = [dcn(&mut slv, 2..=2), dcn(&mut slv, 0..=5)];
			let right = [dcn(&mut slv, 2..=2), dcn(&mut slv, 0..=3)];
			IntLexLeBounds::post(&mut slv, vec![(left[0], right[0]), (left[1], right[1])]);
			let _ = slv.propagate_next().unwrap();
			assert_eq!(left[1].bounds(&slv), (0, 3));
			assert_eq!(right[1].bounds(&slv), (0, 3));
		}

		// The second position forces `left_1 > right_1`, so the first must be strict:
		// `left_0 < right_0`, tightening both bounds by one.
		{
			let mut slv = Solver::default();
			let left = [dcn(&mut slv, 0..=5), dcn(&mut slv, 3..=3)];
			let right = [dcn(&mut slv, 0..=5), dcn(&mut slv, 0..=0)];
			IntLexLeBounds::post(&mut slv, vec![(left[0], right[0]), (left[1], right[1])]);
			let _ = slv.propagate_next().unwrap();
			assert_eq!(left[0].bounds(&slv), (0, 4));
			assert_eq!(right[0].bounds(&slv), (1, 5));
		}
	}

	#[test]
	#[traced_test]
	fn test_lex_solutions() {
		// `lex_le` between two tuples of decisions (the bounds propagator).
		let mut prb = Model::default();
		let left = prb.new_int_decisions(2, 0..=1);
		let right = prb.new_int_decisions(2, 0..=1);
		prb.lex(left.clone()).le(right.clone()).post().unwrap();
		prb.expect_solutions(
			&[left[0], left[1], right[0], right[1]],
			expect![[r#"
    0, 0, 0, 0
    0, 0, 0, 1
    0, 0, 1, 0
    0, 0, 1, 1
    0, 1, 0, 1
    0, 1, 1, 0
    0, 1, 1, 1
    1, 0, 1, 0
    1, 0, 1, 1
    1, 1, 1, 1"#]],
		);

		// `lex_lt`: the strict order reduces to a non-strict core via `left + 1`.
		let mut prb = Model::default();
		let left = prb.new_int_decisions(2, 0..=1);
		let right = prb.new_int_decisions(2, 0..=1);
		prb.lex(left.clone()).lt(right.clone()).post().unwrap();
		prb.expect_solutions(
			&[left[0], left[1], right[0], right[1]],
			expect![[r#"
    0, 0, 0, 1
    0, 0, 1, 0
    0, 0, 1, 1
    0, 1, 1, 0
    0, 1, 1, 1
    1, 0, 1, 1"#]],
		);

		// `lex_ge`: the reversed order swaps the operands.
		let mut prb = Model::default();
		let left = prb.new_int_decisions(2, 0..=1);
		let right = prb.new_int_decisions(2, 0..=1);
		prb.lex(left.clone()).ge(right.clone()).post().unwrap();
		prb.expect_solutions(
			&[left[0], left[1], right[0], right[1]],
			expect![[r#"
    0, 0, 0, 0
    0, 1, 0, 0
    0, 1, 0, 1
    1, 0, 0, 0
    1, 0, 0, 1
    1, 0, 1, 0
    1, 1, 0, 0
    1, 1, 0, 1
    1, 1, 1, 0
    1, 1, 1, 1"#]],
		);

		// One tuple fully fixed: the clausal decomposition against `(1, 1)`.
		let mut prb = Model::default();
		let left = prb.new_int_decisions(2, 0..=2);
		let c = prb.new_int_decisions(2, 1..=1);
		prb.lex(left.clone()).le(c).post().unwrap();
		prb.expect_solutions(
			&[left[0], left[1]],
			expect![[r#"
    0, 0
    0, 1
    0, 2
    1, 0
    1, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_lex_unsatisfiable() {
		// A fixed-equal prefix followed by a position forcing `left_1 > right_1`
		// violates the lexicographic order.
		let mut slv = Solver::default();
		let left = [dcn(&mut slv, 2..=2), dcn(&mut slv, 3..=3)];
		let right = [dcn(&mut slv, 2..=2), dcn(&mut slv, 0..=0)];
		IntLexLeBounds::post(&mut slv, vec![(left[0], right[0]), (left[1], right[1])]);
		slv.assert_unsatisfiable();
	}
}
