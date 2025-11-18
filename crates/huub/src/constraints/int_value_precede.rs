//! Structure and algorithms for the value_precede_chain constraint, which
//! enforces that a fixed order of the first occurrences of a given list of
//! integers in a list of integer variables.

use std::{
	cmp::{max, min},
	ops::AddAssign,
};

use pindakaas::Lit as RawLit;

use crate::{
	actions::{
		BoolInspectionActions, ConstructionActions, InitActions, IntDecisionActions,
		IntInspectionActions, ReasoningContext, ReasoningEngine, ReformulationActions,
		TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	helpers::static_dispatch::static_dispatch,
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, int_var::IntVarRef, queue::PriorityLevel, trail::TrailedInt,
		IntLitMeaning, IntView,
	},
	Conjunction, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for the `seq_precede_chain_int` constraint.
pub struct IntSeqPrecedeChainBounds<I> {
	/// List of integer variables where first occurrences of all i>0 must be
	/// ordered.
	vars: Vec<I>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of i.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of i.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies
	/// `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i that has to occur.
	max_last: TrailedInt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `value_precede_chain` constraint.
pub struct IntValuePrecedeChainValue<I> {
	/// List of integers that need to occur in order
	values: Vec<IntVal>,
	/// List of integer variables where first occurrences of specified values
	/// must be ordered.
	vars: Vec<I>,
	/// True if initial pass is completed.
	initialized: bool,
	/// First possible occurrence of `values[i]`.
	first: Vec<TrailedInt>,
	/// Last possible occurrence of `values[i]`.
	last: Vec<TrailedInt>,
	/// Used for incremental updates of upper bounds, `first[i] = k` implies
	/// `first_val[k] = i`.
	first_val: Vec<TrailedInt>,
	/// Greatest i such that `values[i]` has to occur.
	max_last: TrailedInt,
	/// Minimum value in values.
	min_val: IntVal,
	/// Maximum value in values.
	max_val: IntVal,
	/// Minimum value with `min_val<min_hole<max_val` such that min_hole is not
	/// an element of values.
	min_hole: IntVal,
	/// Used to iterate through the holes in values.
	next_hole: Vec<IntVal>,
	/// List of holes in values.
	holes: Vec<IntVal>,
	/// Reverse mapping of actual values to their indices in the `values` array
	mapping: Vec<Option<usize>>,
}

impl<I> IntSeqPrecedeChainBounds<I> {
	/// Lower bound explanation: Could not have this value earlier (=upper bound
	/// explanation) and some later value requires the lower bound (recursive
	/// lower bound).
	fn explain_lower<Ctx>(
		&self,
		i: usize,
		k: IntVal,
	) -> impl FnOnce(&mut Ctx) -> Conjunction<Ctx::Atom> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let mut reason = Vec::new();
			// Explain a lower bound via 3 cases:
			// - Lower bound of var i is above k - This is the value that required the
			//   earlier lower bound that is currently explained (end of recursion).
			// - k is in the domain of var i - Go one step up and to the next variable.
			// - k is not in the domain of var i - i can be anything else, go to next
			//   variable.
			{
				let mut i = i + 1;
				let mut k = k;
				loop {
					if self.vars[i].lower_bound(ctx) > k {
						reason.push(self.vars[i].lit(ctx, IntLitMeaning::GreaterEq(k + 1)));
						break;
					}
					if self.vars[i].in_domain(ctx, k) {
						i += 1;
						k += 1;
					} else {
						reason.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(k)));
						i += 1;
					}
				}
			}

			reason.extend(self.explain_upper(i, k)(ctx));
			reason
		}
	}

	/// Upper bound explanation: All previous elements are smaller.
	fn explain_upper<Ctx>(
		&self,
		i: usize,
		k: IntVal,
	) -> impl FnOnce(&mut Ctx) -> Conjunction<Ctx::Atom> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			self.vars
				.iter()
				.take(i)
				.map(|v| v.lit(ctx, IntLitMeaning::Less(k)))
				.collect()
		}
	}

	/// Do a full propagation run, requires checking all variables in both
	/// directions.
	fn initial_propagation<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		// Current upper bound
		let mut up = 0;
		// Current lower bound
		let mut low = 0;

		// Forward pass to set upper bounds and capture the highest lower bound.
		for (i, v) in self.vars.iter().enumerate() {
			let mut ub_v = v.upper_bound(ctx);
			// Upper bound can only increase by 1, set new bound if larger values are in the
			// domain.
			if ub_v > up + 1 {
				if v.in_domain(ctx, up + 1) {
					ub_v = up + 1;
				}
				v.set_upper_bound(ctx, up + 1, self.explain_upper(i, up + 1))?;
			}
			// The current var is the first possibility to reach value up + 1.
			if ub_v == up + 1 {
				up += 1;
				ctx.set_trailed_int(self.first[up as usize], i as IntVal);
				ctx.set_trailed_int(self.first_val[i], up);
			}
			let lb_v = v.lower_bound(ctx);
			// The lower bound will be needed for the backward pass.
			if low < lb_v {
				ctx.set_trailed_int(self.last[lb_v as usize], i as IntVal);
				low = lb_v;
			}
		}
		// The highest lower bound is stored.
		ctx.set_trailed_int(self.max_last, low);

		// Backward pass to set lower bounds.
		for (i, v) in self.vars.iter().enumerate().rev() {
			// Lower bound is enforced if upper and lower bound coincide.
			if ctx.trailed_int(self.first[low as usize]) == i as IntVal {
				v.set_lower_bound(ctx, low, self.explain_lower(i, low))?;
			}
			// Found possibility to use a lower value - reduce lower bound.
			if i as IntVal <= ctx.trailed_int(self.last[low as usize]) && v.in_domain(ctx, low) {
				ctx.set_trailed_int(self.last[low as usize], i as IntVal);
				low -= 1;
			}
			// Stop early if no more lower bounds can be propagated.
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Create a new [`IntSeqPrecedeChainBounds`] propagator and post it in the
	/// solver.
	pub fn new<E>(engine: &mut E, vars: Vec<I>) -> Self
	where
		E: ConstructionActions + ReasoningContext + ?Sized,
		I: IntInspectionActions<E>,
	{
		let n = vars.len();
		let ub = vars.iter().fold(0, |u, item| {
			if item.upper_bound(engine) > u {
				u + 1
			} else {
				u
			}
		});

		let first = (0..=ub).map(|_| engine.new_trailed_int(0)).collect();
		let last = (0..=ub)
			.map(|i| {
				if i == 0 {
					engine.new_trailed_int(IntVal::MIN)
				} else {
					engine.new_trailed_int(IntVal::MAX)
				}
			})
			.collect();
		let first_val = (0..n).map(|_| engine.new_trailed_int(0)).collect();
		let max_last = engine.new_trailed_int(0);

		Self {
			vars: vars.clone(),
			initialized: false,
			first,
			last,
			first_val,
			max_last,
		}
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as
	/// far as necessary.
	fn repair_lower<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		mut k: IntVal,
	) -> Result<(IntVal, IntVal), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		// Start at the last possible occurrence of k, then iterate backwards.
		let mut i = ctx.trailed_int(self.last[k as usize]);
		// If k == 0, no more lower bounds can be propagated.
		while k > 0 {
			if self.vars[i as usize].in_domain(ctx, k) {
				ctx.set_trailed_int(self.last[k as usize], i);
				// Enforce lower bound if lower and upper bound coincide.
				if ctx.trailed_int(self.first[k as usize]) == i {
					self.vars[i as usize].set_lower_bound(
						ctx,
						k,
						self.explain_lower(i as usize, k),
					)?;
				}
				k -= 1;
				// Abort early if the previous state is rejoined.
				if ctx.trailed_int(self.last[k as usize]) < i {
					return Ok((i, k + 1));
				}
			}

			i -= 1;
			// Hit boundary case, this will cause a conflict.
			if i < 0 {
				self.vars[0].set_lower_bound(ctx, k, self.explain_lower(0, k))?;
			}
		}

		Ok((i, 0))
	}

	/// Iteratively repair the upper bounds starting with k, only iterates as
	/// far as necessary.
	fn repair_upper<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		mut k: IntVal,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let mut i = ctx.trailed_int(self.first[k as usize]);
		let mut lim = self.upper_limit(ctx, k as usize);

		while i <= lim {
			// Set new upper bound if necessary.
			if self.vars[i as usize].upper_bound(ctx) > k {
				self.vars[i as usize].set_upper_bound(ctx, k, self.explain_upper(i as usize, k))?;
			}
			// If var i is the first possibility to reach value k
			if self.vars[i as usize].in_domain(ctx, k) {
				ctx.set_trailed_int(self.first[k as usize], i);
				ctx.set_trailed_int(self.first_val[i as usize], k);
				// Enforce lower bound if lower and upper bound coincide.
				if ctx.trailed_int(self.last[k as usize]) == i {
					self.vars[i as usize].set_lower_bound(
						ctx,
						k,
						self.explain_lower(i as usize, k),
					)?;
				}
				k += 1;
				// Abort early if the previous state is rejoined.
				if (k as usize) == self.first.len() || i < ctx.trailed_int(self.first[k as usize]) {
					return Ok(());
				}
				lim = self.upper_limit(ctx, k as usize);
			}
			i += 1;
		}

		// Hit boundary case, this will cause a conflict.
		if (i as usize) < self.vars.len() {
			self.vars[i as usize - 1].set_lower_bound(
				ctx,
				k,
				self.explain_lower(i as usize - 1, k),
			)?;
		}

		ctx.set_trailed_int(self.first[k as usize], 0);
		Ok(())
	}

	/// Get the latest occurrence of k, or the maximum variable index if there
	/// is no latest.
	fn upper_limit<Ctx: TrailingActions>(&self, ctx: &mut Ctx, k: usize) -> IntVal {
		min(ctx.trailed_int(self.last[k]), self.vars.len() as IntVal - 1)
	}
}

impl IntSeqPrecedeChainBounds<IntView> {
	/// Create a new [`IntSeqPrecedeChainBounds`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, mut vars: Vec<IntView>)
	where
		E: AddAssign<BoxedPropagator> + ConstructionActions + ReasoningContext + ?Sized,
		E::Atom: From<bool> + From<RawLit>,
		IntView: IntInspectionActions<E>,
		IntVarRef: IntInspectionActions<E>,
		RawLit: BoolInspectionActions<E>,
	{
		// Variables that do not allow positive values are irrelevant.
		vars.retain(|&v| v.upper_bound(solver) > 0);
		if vars.is_empty() {
			return;
		}
		vars.shrink_to_fit();

		static_dispatch!([VecIntView |> vars], |vars| {
			let con = IntSeqPrecedeChainBounds::new(solver, vars);
			*solver += Box::new(con);
		})
	}
}

impl<E, I> Constraint<E> for IntSeqPrecedeChainBounds<I>
where
	E: ReasoningEngine,
	I: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		// TODO: Can we remove negative values here?

		if self.vars.iter().all(|v| v.val(ctx).is_some()) {
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self
			.vars
			.iter()
			.map(|v| slv.solver_int(v.clone().into()))
			.collect();

		IntSeqPrecedeChainBounds::post(slv, vars);
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntSeqPrecedeChainBounds<I>
where
	E: ReasoningEngine,
	I: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		for v in &self.vars {
			v.enqueue_when(ctx, IntPropCond::Domain);
		}
	}

	#[tracing::instrument(name = "seq_precede_chain", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		if !self.initialized {
			return self.initial_propagation(ctx);
		}

		// Check upper bound updates, only necessary for all elements in first,
		// not all variables.
		for (k, &t) in self.first.iter().enumerate() {
			let i = ctx.trailed_int(t);
			if ctx.trailed_int(self.first_val[i as usize]) == k as IntVal
				&& self.vars[i as usize].upper_bound(ctx) < k as IntVal
			{
				self.repair_upper(ctx, k as IntVal)?;
			}
		}
		// Lower bound requires full pass to catch all potential propagations.
		let mut i = self.vars.len() as IntVal;
		let mut k = ctx.trailed_int(self.max_last);
		while i > 0 {
			i -= 1;
			if k > 0 && ctx.trailed_int(self.last[k as usize - 1]) == i {
				k -= 1;
			}
			let lb = self.vars[i as usize].lower_bound(ctx);
			// Deal with increase of lower bound.
			if lb > k {
				ctx.set_trailed_int(self.last[lb as usize], i);
				// Update highest lower bound if necessary.
				if lb > ctx.trailed_int(self.max_last) {
					ctx.set_trailed_int(self.max_last, lb);
				}
				// If a repair is necessary, continue check where the repair ended.
				(i, k) = self.repair_lower(ctx, lb)?;
				continue;
			}
			// Deal with moving the last possibility to have value k for the first.
			if ctx.trailed_int(self.last[k as usize]) == i
				&& !self.vars[i as usize].in_domain(ctx, k)
			{
				(i, k) = self.repair_lower(ctx, k)?;
			}
		}
		Ok(())
	}
}

impl<I> IntValuePrecedeChainValue<I> {
	/// Lower bound explanation: Could not have this index earlier (=upper bound
	/// explanation) and some later index requires the lower bound (recursive
	/// lower bound).
	fn explain_lower<Ctx>(
		&self,
		i: usize,
		j: usize,
	) -> impl FnOnce(&mut Ctx) -> Conjunction<Ctx::Atom> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			let mut reason = Vec::new();

			// Explain a lower bound via 3 cases:
			// - Current lower bound index is above k - This is the value that required the
			//   earlier lower bound that is currently explained (end of recursion).
			// - Index k is in the domain of var i - Go one step up and to the next
			//   variable.
			// - Index k is not in the domain of var i - i can be anything else, go to next
			//   variable.
			{
				let mut i = i + 1;
				let mut j = j;

				loop {
					// A lower bound is explained by stating that all untracked values are excluded
					// (< min value, > max value, all holes), as well as all values with smaller
					// indices.
					if let Some(lb) = self.lowest_index(ctx, i) {
						if lb > j {
							reason.push(
								self.vars[i].lit(ctx, IntLitMeaning::GreaterEq(self.min_val)),
							);
							reason
								.push(self.vars[i].lit(ctx, IntLitMeaning::Less(self.max_val + 1)));
							reason.extend(
								self.holes
									.iter()
									.map(|&h| self.vars[i].lit(ctx, IntLitMeaning::NotEq(h))),
							);
							reason.extend((0..j).map(|k| {
								self.vars[i].lit(ctx, IntLitMeaning::NotEq(self.values[k]))
							}));
							break;
						}
					}
					if self.vars[i].in_domain(ctx, self.values[j - 1]) {
						i += 1;
						j += 1;
					} else {
						reason
							.push(self.vars[i].lit(ctx, IntLitMeaning::NotEq(self.values[j - 1])));
						i += 1;
					}
				}
			}

			if j > 0 {
				reason.extend(self.explain_upper(i, j)(ctx));
			}
			reason
		}
	}

	/// Upper bound explanation: All previous indices are smaller (exclude
	/// values with larger index).
	fn explain_upper<Ctx>(
		&self,
		i: usize,
		j: usize,
	) -> impl FnOnce(&mut Ctx) -> Conjunction<Ctx::Atom> + '_
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		move |ctx: &mut Ctx| {
			self.vars
				.iter()
				.take(i)
				.map(|v| v.lit(ctx, IntLitMeaning::NotEq(self.values[j - 1])))
				.collect()
		}
	}

	/// Do a full propagation run, requires checking all variables in both
	/// directions.
	fn initial_propagation<E>(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		// Current upper bound
		let mut up = 0;
		// Current lower bound
		let mut low = 0;

		// Forward pass to set upper bounds and capture the highest lower bound.
		for (i, v) in self.vars.iter().enumerate() {
			// Upper bound can only increase by 1, set new bound if larger values are in the
			// domain.
			self.propagate_upper_bound(ctx, i, up + 1)?;
			// The current var is the first possibility to reach index up + 1.
			if up < self.values.len() && v.in_domain(ctx, self.values[up]) {
				up += 1;
				ctx.set_trailed_int(self.first[up], i as IntVal);
				ctx.set_trailed_int(self.first_val[i], up as IntVal);
			}
			// The lower bound will be needed for the backward pass.
			if let Some(lb) = self.lowest_index(ctx, i) {
				if low < lb {
					ctx.set_trailed_int(self.last[lb], i as IntVal);
					low = lb;
				}
			}
		}

		// Backward pass to set lower bounds.
		for (i, v) in self.vars.iter().enumerate().rev() {
			// Lower bound is enforced if upper and lower bound coincide.
			if ctx.trailed_int(self.first[low]) == i as IntVal {
				self.propagate_lower_bound(ctx, i, low)?;
			}
			// Found possibility to use a lower value - reduce lower bound.
			if i as IntVal <= ctx.trailed_int(self.last[low])
				&& v.in_domain(ctx, self.values[low - 1])
			{
				ctx.set_trailed_int(self.last[low], i as IntVal);
				low -= 1;
			}
			// Stop early if no more lower bounds can be propagated.
			if low == 0 {
				break;
			}
		}

		self.initialized = true;
		Ok(())
	}

	/// Get the lower bound for the index in values, None if any options outside
	/// values are still in the domain. Has to exclude values below and above
	/// the range of values, then all holes, finally values with lower index.
	fn lowest_index<Ctx>(&self, ctx: &mut Ctx, i: usize) -> Option<usize>
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntInspectionActions<Ctx>,
	{
		let (lb, ub) = self.vars[i].bounds(ctx);
		// Easy case with no lower index bound.
		if lb < self.min_val || ub > self.max_val {
			return None;
		}
		// Shortcut for fixed variables.
		if lb == ub {
			return self.mapping[(lb - self.min_val) as usize];
		}
		// Iteration over holes (via nex_hole for efficiency).
		let mut h = max(lb, self.min_hole);
		while ((h - self.min_hole) as usize) < self.next_hole.len() {
			h = self.next_hole[(h - self.min_hole) as usize];
			if h > ub {
				break;
			}
			if self.vars[i].in_domain(ctx, h) {
				return None;
			}
			h += 1;
		}
		// Find the first possible index in values.
		for (j, &val) in self.values.iter().enumerate() {
			if self.vars[i].in_domain(ctx, val) {
				return Some(j + 1);
			}
		}
		Some(self.values.len() + 1)
	}

	/// Create a new [`ValuePrecedeChainValue`] propagator
	pub fn new<E>(engine: &mut E, values: Vec<IntVal>, vars: Vec<I>) -> Self
	where
		E: ConstructionActions + ?Sized,
	{
		let first = (0..=values.len())
			.map(|i| {
				if i == 0 {
					engine.new_trailed_int(0)
				} else {
					engine.new_trailed_int(vars.len() as IntVal - 1)
				}
			})
			.collect();
		let last = (0..=values.len())
			.map(|i| {
				if i == 0 {
					engine.new_trailed_int(IntVal::MIN)
				} else {
					engine.new_trailed_int(IntVal::MAX)
				}
			})
			.collect();
		let first_val = (0..vars.len()).map(|_| engine.new_trailed_int(0)).collect();
		let max_last = engine.new_trailed_int(0);
		// Set up some data structures to deal with holes in values more efficiently.
		let min_val = *values.iter().min().unwrap_or(&IntVal::MAX);
		let max_val = *values.iter().max().unwrap_or(&IntVal::MIN);
		let holes = (min_val..=max_val)
			.filter(|&i| values.iter().all(|&v| v != i))
			.collect::<Vec<_>>();
		let min_hole = *holes.iter().min().unwrap_or(&0);
		let mut next_hole = vec![0; (*holes.iter().max().unwrap_or(&-1) - min_hole + 1) as usize];
		let mut cur_hole = 0;
		for (i, h) in next_hole.iter_mut().enumerate() {
			if i as IntVal + min_hole > holes[cur_hole] {
				cur_hole += 1;
			}
			*h = holes[cur_hole];
		}
		let mut mapping = vec![None; (max_val - min_val + 1) as usize];
		for (i, &val) in values.iter().enumerate() {
			mapping[(val - min_val) as usize] = Some(i + 1);
		}

		Self {
			values,
			vars,
			initialized: false,
			first,
			last,
			first_val,
			max_last,
			min_val,
			max_val,
			holes,
			min_hole,
			next_hole,
			mapping,
		}
	}

	/// Propagate a lower bound by excluding all elements outside values, and
	/// values with lower index.
	fn propagate_lower_bound<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		i: usize,
		j: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let (lb, ub) = self.vars[i].bounds(ctx);
		// Exclude values below the minimum tracked value.
		if lb < self.min_val {
			self.vars[i].set_lower_bound(ctx, self.min_val, self.explain_lower(i, j))?;
		}
		// Exclude values above the maximum tracked value.
		if ub > self.max_val {
			self.vars[i].set_upper_bound(ctx, self.max_val, self.explain_lower(i, j))?;
		}
		// Exclude holes in the tracked values.
		let mut h = max(lb, self.min_hole);
		while ((h - self.min_hole) as usize) < self.next_hole.len() {
			h = self.next_hole[(h - self.min_hole) as usize];
			if h > ub {
				break;
			}
			if self.vars[i].in_domain(ctx, h) {
				self.vars[i].set_not_eq(ctx, h, self.explain_lower(i, j))?;
			}
			h += 1;
		}
		// Exclude values with lower index.
		for k in 0..j - 1 {
			if self.vars[i].in_domain(ctx, self.values[k]) {
				self.vars[i].set_not_eq(ctx, self.values[k], self.explain_lower(i, j))?;
			}
		}
		Ok(())
	}

	/// Propagate an upper bound by removing all values with higher index.
	fn propagate_upper_bound<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		i: usize,
		j: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		for k in j..self.values.len() {
			if self.vars[i].in_domain(ctx, self.values[k]) {
				self.vars[i].set_not_eq(ctx, self.values[k], self.explain_upper(i, k))?;
			}
		}
		Ok(())
	}

	/// Iteratively repairs the lower bounds starting with k, only iterates as
	/// far as necessary.
	fn repair_lower<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		mut k: usize,
	) -> Result<(usize, usize), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		// Start at the last possible occurrence of k, then iterate backwards.
		let mut i = ctx.trailed_int(self.last[k]);
		// If k == 0, no more lower bounds can be propagated.
		while k > 0 {
			if self.vars[i as usize].in_domain(ctx, self.values[k - 1]) {
				ctx.set_trailed_int(self.last[k], i);
				// Enforce lower bound if lower and upper bound coincide.
				if ctx.trailed_int(self.first[k]) == i {
					self.propagate_lower_bound(ctx, i as usize, k)?;
				}
				k -= 1;
				// Abort early if the previous state is rejoined.
				if ctx.trailed_int(self.last[k]) < i {
					return Ok((i as usize, k + 1));
				}
			}

			i -= 1;
			// Hit boundary case, this will cause a conflict.
			if i < 0 {
				self.propagate_lower_bound(ctx, 0, k)?;
				// Return Ok since the conflict is only detected during propagation
				// (several domain elements are removed separately).
				return Ok((0, k));
			}
		}

		if i < 0 {
			return Ok((0, 0));
		}
		Ok((i as usize, 0))
	}

	/// Iteratively repair the upper bounds starting with k, only iterates as
	/// far as necessary.
	fn repair_upper<E>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		mut k: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let mut i = ctx.trailed_int(self.first[k]);
		let mut lim = self.upper_limit(ctx, k);

		while i <= lim {
			// Set new upper bound if necessary.
			self.propagate_upper_bound(ctx, i as usize, k)?;
			// If var i is the first possibility to reach value k
			if self.vars[i as usize].in_domain(ctx, self.values[k - 1]) {
				ctx.set_trailed_int(self.first[k], i);
				ctx.set_trailed_int(self.first_val[i as usize], k as IntVal);
				// Enforce lower bound if lower and upper bound coincide.
				if ctx.trailed_int(self.last[k]) == i {
					self.propagate_lower_bound(ctx, i as usize, k)?;
				}
				k += 1;
				// Abort early if the previous state is rejoined.
				if k == self.first.len() || i < ctx.trailed_int(self.first[k]) {
					return Ok(());
				}
				lim = self.upper_limit(ctx, k);
			}
			i += 1;
		}

		// Hit boundary case, this will cause a conflict.
		if (i as usize) < self.vars.len() {
			self.propagate_lower_bound(ctx, i as usize - 1, k)?;
			// Return Ok since the conflict is only detected during propagation
			// (several domain elements are removed separately).
			return Ok(());
		}

		ctx.set_trailed_int(self.first[k], 0);
		Ok(())
	}

	/// Get the latest occurrence of value index k, or the maximum variable
	/// index if there is no latest.
	fn upper_limit<Ctx>(&self, ctx: &mut Ctx, k: usize) -> IntVal
	where
		Ctx: TrailingActions,
	{
		min(ctx.trailed_int(self.last[k]), self.vars.len() as IntVal - 1)
	}
}

impl IntValuePrecedeChainValue<IntView> {
	/// Create a new [`ValuePrecedeChainValue`] propagator and post it in the
	/// solver.
	pub fn post<E>(solver: &mut E, values: Vec<IntVal>, mut vars: Vec<IntView>)
	where
		E: AddAssign<BoxedPropagator> + ConstructionActions + ReasoningContext + ?Sized,
		IntView: IntInspectionActions<E>,
	{
		// Variables that do not any tracked values are irrelevant.
		vars.retain(|&var| values.iter().any(|&val| var.in_domain(solver, val)));
		if vars.is_empty() {
			return;
		}
		vars.shrink_to_fit();
		let n = vars.len();

		let first = (0..=values.len())
			.map(|i| {
				if i == 0 {
					solver.new_trailed_int(0)
				} else {
					solver.new_trailed_int(vars.len() as IntVal - 1)
				}
			})
			.collect();
		let last = (0..=values.len())
			.map(|i| {
				if i == 0 {
					solver.new_trailed_int(IntVal::MIN)
				} else {
					solver.new_trailed_int(IntVal::MAX)
				}
			})
			.collect();
		let first_val = (0..n).map(|_| solver.new_trailed_int(0)).collect();
		let max_last = solver.new_trailed_int(0);
		// Set up some data structures to deal with holes in values more efficiently.
		let min_val = *values.iter().min().unwrap_or(&IntVal::MAX);
		let max_val = *values.iter().max().unwrap_or(&IntVal::MIN);
		let holes = (min_val..=max_val)
			.filter(|&i| values.iter().all(|&v| v != i))
			.collect::<Vec<_>>();
		let min_hole = *holes.iter().min().unwrap_or(&0);
		let mut next_hole = vec![0; (*holes.iter().max().unwrap_or(&-1) - min_hole + 1) as usize];
		let mut cur_hole = 0;
		for (i, h) in next_hole.iter_mut().enumerate() {
			if i as IntVal + min_hole > holes[cur_hole] {
				cur_hole += 1;
			}
			*h = holes[cur_hole];
		}
		let mut mapping = vec![None; (max_val - min_val + 1) as usize];
		for (i, &val) in values.iter().enumerate() {
			mapping[(val - min_val) as usize] = Some(i + 1);
		}

		static_dispatch!([VecIntView |> vars], |vars| {
			*solver += Box::new(IntValuePrecedeChainValue {
				values,
				vars,
				initialized: false,
				first,
				last,
				first_val,
				max_last,
				min_val,
				max_val,
				holes,
				min_hole,
				next_hole,
				mapping,
			});
		})
	}
}

impl<E, I> Constraint<E> for IntValuePrecedeChainValue<I>
where
	E: ReasoningEngine,
	I: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		// TODO: Can we eliminate variables without tracked values here?

		if self.vars.iter().all(|v| v.val(ctx).is_some()) {
			return Ok(SimplificationStatus::Subsumed);
		}

		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let vars: Vec<_> = self
			.vars
			.iter()
			.map(|v| slv.solver_int(v.clone().into()))
			.collect();
		IntValuePrecedeChainValue::post(slv, self.values.clone(), vars);
		Ok(())
	}
}

impl<E, I> Propagator<E> for IntValuePrecedeChainValue<I>
where
	E: ReasoningEngine,
	I: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Low);

		for v in &self.vars {
			v.enqueue_when(ctx, IntPropCond::Domain);
		}
	}

	#[tracing::instrument(name = "value_precede_chain", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		if !self.initialized {
			return self.initial_propagation(ctx);
		}

		// Check upper bound updates, only necessary for all elements in first,
		// not all variables.
		for (k, &t) in self.first.iter().enumerate().skip(1) {
			let i = ctx.trailed_int(t);
			if ctx.trailed_int(self.first_val[i as usize]) == k as IntVal
				&& !self.vars[i as usize].in_domain(ctx, self.values[k - 1])
			{
				self.repair_upper(ctx, k)?;
			}
		}
		// Lower bound requires full pass to catch all potential propagation.
		let mut i = self.vars.len();
		let mut k = ctx.trailed_int(self.max_last) as usize;
		while i > 0 {
			i -= 1;
			if k > 0 && ctx.trailed_int(self.last[k - 1]) == i as IntVal {
				k -= 1;
			};
			if let Some(lb) = self.lowest_index(ctx, i) {
				// Deal with increase of lower bound.
				if lb > k {
					ctx.set_trailed_int(self.last[lb], i as IntVal);
					// Update highest lower bound if necessary.
					if lb as IntVal > ctx.trailed_int(self.max_last) {
						ctx.set_trailed_int(self.max_last, lb as IntVal);
					}
					// If a repair is necessary, continue check where the repair ended.
					(i, k) = self.repair_lower(ctx, lb)?;
					continue;
				}
			}
			// Deal with moving the last possibility to have value k for the first.
			if ctx.trailed_int(self.last[k]) == i as IntVal
				&& !self.vars[i].in_domain(ctx, self.values[k - 1])
			{
				(i, k) = self.repair_lower(ctx, k)?;
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use std::cmp::max;

	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_value_precede::{IntSeqPrecedeChainBounds, IntValuePrecedeChainValue},
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
			Value::{self, Int},
		},
		IntVal,
	};

	#[test]
	#[traced_test]
	fn test_seq_precede_chain_paper() {
		let mut slv = Solver::default();
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1, 5..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2, 4..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x5 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x6 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x7 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x8 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([4..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x9 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntSeqPrecedeChainBounds::post(&mut slv, vec![x1, x2, x3, x4, x5, x6, x7, x8, x9]);
		slv.assert_all_solutions(
			&[x1, x2, x3, x4, x5, x6, x7, x8, x9],
			valid_sequence_precede,
		);
	}

	#[test]
	#[traced_test]
	fn test_seq_precede_chain_unrestricted() {
		let mut slv = Solver::default();
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntSeqPrecedeChainBounds::post(&mut slv, vec![x1, x2, x3, x4]);
		slv.assert_all_solutions(&[x1, x2, x3, x4], valid_sequence_precede);
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_complex() {
		let mut slv = Solver::default();
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=0, 2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=-3, 1..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=0, 2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x5 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x6 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=-1, 1..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x7 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-1..=-1, 3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x8 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::post(
			&mut slv,
			vec![2, -2, 1, -1],
			vec![x0, x1, x2, x3, x4, x5, x6, x7, x8],
		);
		slv.assert_all_solutions(
			&[x0, x1, x2, x3, x4, x5, x6, x7, x8],
			valid_value_precede(vec![2, -2, 1, -1]),
		);
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_out_of_bounds() {
		let mut slv = Solver::default();
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=1]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::post(&mut slv, vec![1, 3], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 3]));
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_simple() {
		let mut slv = Solver::default();
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::post(&mut slv, vec![1, 2], vec![x0, x1, x2]);
		slv.assert_all_solutions(&[x0, x1, x2], valid_value_precede(vec![1, 2]));
	}

	#[test]
	#[traced_test]
	fn test_value_precede_chain_unrestricted() {
		let mut slv = Solver::default();
		let x0 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-2..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let x3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntValuePrecedeChainValue::post(&mut slv, vec![2, -2, 1, -1], vec![x0, x1, x2, x3]);
		slv.assert_all_solutions(&[x0, x1, x2, x3], valid_value_precede(vec![2, -2, 1, -1]));
	}

	fn valid_sequence_precede(sol: &[Value]) -> bool {
		sol.iter()
			.map(|v| {
				let Int(val) = *v else { return None };
				Some(val)
			})
			.try_fold(0, |u, val| match (u, val) {
				(uv, Some(val)) => {
					if val <= uv + 1 {
						Some(max(uv, val))
					} else {
						None
					}
				}
				_ => None,
			})
			.is_some()
	}

	fn valid_value_precede(values: Vec<IntVal>) -> impl Fn(&[Value]) -> bool {
		move |sol| {
			let mut cur_index = 0;
			for v in sol.iter() {
				if let Int(val) = *v {
					for &forbidden in values.iter().skip(cur_index + 1) {
						if forbidden == val {
							return false;
						}
					}
					if cur_index < values.len() && val == values[cur_index] {
						cur_index += 1;
					}
				} else {
					return false;
				}
			}
			true
		}
	}
}
