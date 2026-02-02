//! Structure and algorithms for the integer no overlap constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.

use std::{
	any::TypeId,
	cmp::{self, Ordering},
	iter::{repeat_with, zip},
};

use itertools::izip;

use crate::{
	IntVal,
	actions::{
		ConstructionActions, InitActions, IntDecisionActions, IntInspectionActions, PostingActions,
		ReasoningContext, ReasoningEngine, Trailed, TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, IntModelActions, IntSolverActions, Propagator,
		SimplificationStatus,
	},
	helpers::matrix::Matrix,
	lower::{LoweringContext, LoweringError},
	solver::{IntLitMeaning, activation_list::IntPropCond, engine::Engine, queue::PriorityLevel},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// The [`IntNoOverlapSweep`] propagator ensures that a set of k-dimensional
/// hyperrectangles do not overlap. It is a sweep-based propagator that reasons
/// about forbidden regions for each rectangle.
///
/// This propagator was originally proposed in "Sweep as a Generic Pruning
/// Technique Applied to the Non-overlapping Rectangles Constraint" by Beldinau,
/// Nicolas and Carlsson, Mats. Then it was implemented within Gecode in
/// <https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-325845> and then extended
/// to lazy clause generation within this solver in
/// <https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-562628>.
///
/// The core idea is that we reason about forbidden regions of each rectangle,
/// that is, regions we are not allowed to place the lower-left corner of a
/// rectangle due to the domains of the other rectangles. These regions are
/// forbidden in the sense that if we would put our rectangle at that place, it
/// would guarantee that at least two rectangles are overlapping, which violates
/// the constraint.
// All Matrix attributes are 2-dimensional, with the first index
// representing the object and the second representing the dimension.
pub struct IntNoOverlapSweep<const STRICT: bool, I1, I2> {
	/// The origin position of each object in each dimension.
	origin: Matrix<2, I1>,
	/// The size of each object in each dimension.
	size: Matrix<2, I2>,

	/// Trail which tracks the target property, target[i] = 1 if is has been
	/// lost, and will let us skip some iterations since it at that point has
	/// been checked to be at a feasible position and fixed.
	target: Box<[Trailed<bool>]>,
	/// Trail which tracks the source property, target[i] = 1 if is has been
	/// lost, and will allow it to be disregarded through the entire algorithm
	/// since it will not affect any other rectangle.
	source: Box<[Trailed<bool>]>,

	/// A cache for the upper bounds of the origin variables.
	origin_ub: Matrix<2, IntVal>,
	/// A cache for the lower bounds of the origin variables.
	origin_lb: Matrix<2, IntVal>,
	/// A cache for the lower bounds of the size variables.
	size_lb: Matrix<2, IntVal>,

	/// Used to see if any rectangle has lost its source property, that is; it
	/// is completely disjoint from all the others and therefore can be removed
	/// completely when reasoning in the rest of the algorithm since it will not
	/// effect any other triangle.
	bounding_box: Region,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A region, or bounding box, in a multi-dimensional space.
///
/// It is represented by a vector of tuples, where each tuple contains the lower
/// and upper bounds for a single dimension.
struct Region(Vec<(IntVal, IntVal)>);

impl<const STRICT: bool, I1, I2> IntNoOverlapSweep<STRICT, I1, I2> {
	/// Adjusts the sweep point to find the next potential feasible location
	/// when pruning upper bounds.
	///
	/// This is the analog of [`Self::adjust_sweep_min`], but for
	/// [`Self::prune_max`], sweeping downwards.
	fn adjust_sweep_max(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		curr_dimension: usize,
	) -> bool {
		let dimensions = sweep.len();
		debug_assert_eq!(jump.len(), dimensions);
		debug_assert_eq!(curr_obj_lb.len(), dimensions);
		debug_assert_eq!(curr_obj_ub.len(), dimensions);

		for i in (0..dimensions).rev() {
			// Ensures that we check the dimension we are pruning last
			let rotation = (i + curr_dimension) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = curr_obj_lb[rotation] - 1;
			// If the new sweep point is still within the object's domain,
			// we have a new candidate.
			if sweep[rotation] >= curr_obj_lb[rotation] {
				return true;
			} else {
				// Otherwise, this dimension is exhausted. Reset and continue.
				sweep[rotation] = curr_obj_ub[rotation];
			}
		}
		// No feasible origin exists. Set sweep to cause a conflict.
		sweep[curr_dimension] = curr_obj_lb[curr_dimension] - 1;
		false
	}

	/// Adjusts the sweep point to find the next potential feasible location
	/// when pruning lower bounds.
	///
	/// This function implements the "sweep" logic. It iterates through the
	/// dimensions and moves the `sweep` point to the `jump` location in one
	/// dimension at a time. If the new `sweep` coordinate is still within the
	/// object's domain, a potential new location is found, and the function
	/// returns `true`. If the sweep goes out of bounds in all dimensions, it
	/// means no feasible point was found, and the function returns `false`,
	/// setting the sweep point to a value that will cause a conflict.
	fn adjust_sweep_min(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		obj_lb: &[IntVal],
		obj_ub: &[IntVal],
		dim: usize,
	) -> bool {
		let dimensions = sweep.len();
		debug_assert_eq!(jump.len(), dimensions);
		debug_assert_eq!(obj_lb.len(), dimensions);
		debug_assert_eq!(obj_ub.len(), dimensions);

		for i in (0..dimensions).rev() {
			// Ensures that we check the dimension we are pruning last
			let rotation = (i + dim) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = obj_ub[rotation] + 1;
			// If the new sweep point is still within the object's domain,
			// we have found a new candidate point to check.
			if sweep[rotation] <= obj_ub[rotation] {
				return true;
			} else {
				// Otherwise, this dimension is exhausted. Reset sweep point to the
				// lower bound and try the next dimension.
				sweep[rotation] = obj_lb[rotation];
			}
		}
		// If all dimensions are exhausted, no feasible origin exists.
		// Set the sweep point to a value that guarantees a conflict.
		sweep[dim] = obj_ub[dim] + 1;
		false
	}

	/// Checks if a given object is completely outside the given `Region`
	/// (bounding box) in at least one dimension.
	fn disjoint(&self, region: &Region, obj: usize) -> bool {
		let origin_lb = self.origin_lb.row(obj);
		let origin_ub = self.origin_ub.row(obj);
		let size_lb = self.size_lb.row(obj);

		izip!(&region.0, origin_lb, origin_ub, size_lb)
			.any(|(&(lb, ub), &o_lb, &o_ub, &size)| o_ub + size - 1 < lb || o_lb > ub)
	}

	/// Generates a set of literals that explain the existence of the given
	/// forbidden regions.
	///
	/// For each forbidden region, this method identifies the literals (i.e.,
	/// the bounds of the variables) that define it. This is essential for
	/// generating conflict clauses when a domain becomes empty. It also "lifts"
	/// the bounds if a forbidden region extends beyond the domain of the object
	/// being pruned, which can lead to more general explanations.
	fn explain_forbidden_regions<Ctx>(
		&mut self,
		ctx: &mut Ctx,
		forbidden_regions: &[(Region, usize)],
		obj: usize,
	) -> Vec<Ctx::Atom>
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntInspectionActions<Ctx>,
	{
		let mut reason = Vec::new();
		for (region, support) in forbidden_regions.iter() {
			for d in 0..self.num_dimensions() {
				// If sizes are not [`IntVal`], their lower bounds contribute to the
				// forbidden region and must be part of the explanation.
				if TypeId::of::<I2>() != TypeId::of::<IntVal>() {
					reason.push(self.size[[*support, d]].min_lit(ctx));
				}
				let mut possible_ub = self.origin_ub[[*support, d]];
				let origin_ub = self.origin_ub[[obj, d]];

				let mut possible_lb = self.origin_lb[[*support, d]];
				let origin_lb = self.origin_lb[[obj, d]];

				// "Lifting": If a forbidden region overhangs the domain of the object
				// being pruned, we can use the object's bounds to create a tighter,
				// more general explanation.
				if region.max(d) > origin_ub {
					possible_lb = origin_ub - self.size_lb[[*support, d]] + 1;
				}

				if region.min(d) < origin_lb {
					possible_ub = origin_lb + self.size_lb[[obj, d]] - 1;
				}

				reason.push(
					self.origin[[*support, d]].lit(ctx, IntLitMeaning::Less(possible_ub + 1)),
				);
				reason.push(
					self.origin[[*support, d]].lit(ctx, IntLitMeaning::GreaterEq(possible_lb)),
				);
			}
		}
		reason
	}

	/// Generates a complete explanation (a "reason") for a pruning operation.
	///
	/// The reason consists of two parts:
	/// 1. The literals that define the other dimensions of the dimension being
	///    pruned (`dim`) of the object being pruned (`obj`).
	/// 2. The literals that explain the existence of the forbidden regions that
	///    forced the pruning.
	fn explain_propagation<Ctx>(
		&mut self,
		ctx: &mut Ctx,
		forbidden_regions: &[(Region, usize)],
		obj: usize,
		dim: usize,
		prune_upper: bool,
	) -> Vec<Ctx::Atom>
	where
		Ctx: ReasoningContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntInspectionActions<Ctx>,
	{
		let mut reason: Vec<_> = Vec::new();
		for d in 0..self.num_dimensions() {
			// If sizes are not [`IntVal`], their lower bounds contribute to the
			// forbidden region and must be part of the explanation.
			if TypeId::of::<I2>() != TypeId::of::<IntVal>() {
				reason.push(self.size[[obj, d]].min_lit(ctx));
			}

			// The literal for the bound we are about to prune is implicitly part of the
			// conclusion, so we only need to explain the *other* bounds of the object.
			if d == dim {
				if prune_upper {
					reason.push(
						self.origin[[obj, d]]
							.lit(ctx, IntLitMeaning::Less(self.origin_ub[[obj, d]] + 1)),
					);
				} else {
					reason.push(
						self.origin[[obj, d]]
							.lit(ctx, IntLitMeaning::GreaterEq(self.origin_lb[[obj, d]])),
					);
				}
			} else {
				reason.push(
					self.origin[[obj, d]]
						.lit(ctx, IntLitMeaning::Less(self.origin_ub[[obj, d]] + 1)),
				);
				reason.push(
					self.origin[[obj, d]]
						.lit(ctx, IntLitMeaning::GreaterEq(self.origin_lb[[obj, d]])),
				);
			}
		}
		reason.extend(self.explain_forbidden_regions(ctx, forbidden_regions, obj));
		reason
	}

	/// Checks if the origin of a given object is fixed in all dimensions.
	fn fixed_object(&self, obj: usize) -> bool {
		self.origin_lb.row(obj) == self.origin_ub.row(obj)
	}

	/// Generates the set of "forbidden regions" for a given object `obj`.
	///
	/// A forbidden region is an area where the origin of `obj` cannot be placed
	/// because it would guarantee an overlap with another object `i`. Such a
	/// region is calculated based on the current domain of `i`'s origin and
	/// the sizes of both `obj` and `i`.
	///
	/// This method performs two key optimizations:
	/// 1. It filters out any generated forbidden region that does not overlap
	///    with the current domain of `obj`.
	/// 2. It merges regions where one is a subset of another to keep the set of
	///    forbidden regions minimal.
	///
	/// # Returns
	///
	/// A vector of tuples, where each tuple contains a `Region` and the index
	/// of the object that induced it.
	fn forbidden_regions<Ctx>(&mut self, ctx: &mut Ctx, obj: usize) -> Vec<(Region, usize)>
	where
		Ctx: ReasoningContext + TrailingActions,
	{
		let mut forbidden_regions: Vec<Option<(Region, usize)>> = Vec::new();

		'obj_iter: for i in 0..self.num_objects() {
			// Ignore objects that have lost their "source" property.
			if ctx.trailed(self.source[i]) {
				continue;
			}

			if i == obj {
				continue;
			};

			let mut forbidden = Region::with_dimensions(self.num_dimensions());

			for d in 0..self.num_dimensions() {
				let fr_lb = self.origin_ub[[i, d]] - self.size_lb[[obj, d]] + 1;
				let fr_ub = self.origin_lb[[i, d]] + self.size_lb[[i, d]] - 1;
				if fr_lb <= fr_ub {
					forbidden.0[d] = (fr_lb, fr_ub);
				} else {
					// If the interval is empty in any dimension, no forbidden region exists.
					continue 'obj_iter;
				}
			}

			let lb = self.origin_lb.row(obj);
			let ub = self.origin_ub.row(obj);

			// Check if the new forbidden region can be coalesced with an existing one.
			if forbidden.overlaps(lb, ub) {
				for tup in &mut forbidden_regions {
					if let Some((f, _)) = tup {
						match f.coalesce(&forbidden) {
							// `forbidden` is a subset of an existing region `f`, so we can ignore
							// it.
							Some(Ordering::Equal) | Some(Ordering::Greater) => {
								continue 'obj_iter;
							}
							// An existing region `f` is a subset of `forbidden`, so we remove `f`.
							Some(Ordering::Less) => {
								*tup = None;
							}
							// No subset relationship, so we keep both.
							None => continue,
						}
					}
				}
				forbidden_regions.push(Some((forbidden, i)));
			}
		}

		forbidden_regions.into_iter().flatten().collect()
	}

	/// Create a new [`IntNoOverlapSweep`] propagator, to be used within the
	/// given engine.
	///
	/// # Parameters
	///
	/// - `engine`: The construction and reasoning context.
	/// - `origin`: A matrix-like `Vec<Vec<I>>` where `origin[i][d]` is the
	///   origin of object `i` in dimension `d`.
	/// - `size`: A matrix-like `Vec<Vec<I>>` where `size[i][d]` is the size of
	///   object `i` in dimension `d`.
	///
	/// # Panics
	///
	/// Panics if the dimensions of `origin` and `size` are inconsistent.
	/// Specifically, the number of objects (outer `Vec` length) must be the
	/// same, and the number of dimensions (inner `Vec` length) must be the
	/// same for all objects.
	pub(crate) fn new<E>(engine: &mut E, origin: Vec<Vec<I1>>, size: Vec<Vec<I2>>) -> Self
	where
		E: ConstructionActions + ReasoningContext + ?Sized,
	{
		assert_eq!(origin.len(), size.len());
		let num_objects = origin.len();

		let num_dimensions = if num_objects > 0 { origin[0].len() } else { 0 };
		assert!(origin.is_empty() || origin.iter().all(|v| v.len() == num_dimensions));
		assert!(size.is_empty() || size.iter().all(|v| v.len() == num_dimensions));

		let origin = Matrix::new(
			[num_objects, num_dimensions],
			origin.into_iter().flatten().collect(),
		);
		let size = Matrix::new(
			[num_objects, num_dimensions],
			size.into_iter().flatten().collect(),
		);

		let target = repeat_with(|| engine.new_trailed(false))
			.take(num_objects)
			.collect();
		let source = repeat_with(|| engine.new_trailed(false))
			.take(num_objects)
			.collect();

		let origin_ub = Matrix::with_dimensions([num_objects, num_dimensions]);
		let origin_lb = Matrix::with_dimensions([num_objects, num_dimensions]);
		let size_lb = Matrix::with_dimensions([num_objects, num_dimensions]);

		let bounding_box = Region::with_dimensions(num_dimensions);

		Self {
			origin,
			size,
			target,
			source,
			origin_ub,
			origin_lb,
			size_lb,
			bounding_box,
		}
	}

	/// Returns the number of dimensions of the objects.
	fn num_dimensions(&self) -> usize {
		self.origin.len(1)
	}

	/// Returns the number of objects (hyperrectangles) being managed by this
	/// propagator.
	fn num_objects(&self) -> usize {
		self.origin.len(0)
	}

	/// Posts the [`IntNoOverlapSweep`] propagator to the solver.
	///
	/// This is the public entry point for creating the constraint for a
	/// [`Solver`](crate::solver::Solver) instance.
	///
	/// # Parameters
	///
	/// - `solver`: The solver instance.
	/// - `origin`: A matrix-like `Vec<Vec<I>>` where `origin[i][d]` is the
	///   origin of object `i` in dimension `d`.
	/// - `size`: A matrix-like `Vec<Vec<I>>` where `size[i][d]` is the size of
	///   object `i` in dimension `d`.
	///
	/// # Panics
	///
	/// Panics if the dimensions of `origin` and `size` are inconsistent.
	/// Specifically, the number of objects (outer `Vec` length) must be the
	/// same, and the number of dimensions (inner `Vec` length) must be the
	/// same for all objects.
	pub fn post<E>(solver: &mut E, origin: Vec<Vec<I1>>, size: Vec<Vec<I2>>)
	where
		E: PostingActions + ?Sized,
		I1: IntSolverActions<Engine>,
		I2: IntSolverActions<Engine> + IntInspectionActions<E>,
	{
		// Use specialized version if all sizes are constant
		if size.iter().flatten().all(|v| v.val(solver).is_some()) {
			let size: Vec<Vec<_>> = size
				.iter()
				.map(|v| v.iter().map(|v| v.val(solver).unwrap()).collect())
				.collect();

			let con: BoxedPropagator =
				Box::new(IntNoOverlapSweep::<STRICT, _, _>::new(solver, origin, size));
			solver.add_propagator(con);
			return;
		}

		let con: BoxedPropagator = Box::new(Self::new(solver, origin, size));
		solver.add_propagator(con);
	}

	/// Prunes the upper bound of an object's origin in a specific dimension.
	///
	/// This method is analogous to [`Self::prune_min`], but it sweeps backward
	/// from the object's upper bound to find the latest possible feasible
	/// position.
	fn prune_max<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		forbidden_regions: &[(Region, usize)],
		obj: usize,
		dim: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
	{
		// `sweep` is the current point being checked for feasibility.
		let mut sweep = self.origin_ub.row(obj).to_vec();
		// `jump` stores the latest possible escape point (lower bound - 1).
		let mut jump: Vec<_> = self.origin_lb.row(obj).iter().map(|v| v - 1).collect();
		let mut b = true;

		// Find the first forbidden region that the sweep point is inside.
		let mut fr = Region::find_collision(forbidden_regions.iter().map(|(r, _)| r), &sweep);
		while b && fr.is_some() {
			// To escape `fr`, we must jump to at least its lower bound - 1.
			// We take the maximum of all possible jump points.
			for (i, j) in jump.iter_mut().enumerate() {
				*j = cmp::max(*j, fr.unwrap().min(i) - 1);
			}

			let lb = self.origin_lb.row(obj);
			let ub = self.origin_ub.row(obj);

			// Adjust the sweep point to the new jump location.
			b = Self::adjust_sweep_max(&mut sweep, &mut jump, lb, ub, dim);

			// Check if the new sweep point is in another forbidden region.
			fr = Region::find_collision(forbidden_regions.iter().map(|(r, _)| r), &sweep);
		}

		// If the sweep found a new, lower feasible upper bound, propagate it.
		if sweep[dim] != self.origin_ub[[obj, dim]] {
			let reason = self.explain_propagation(ctx, forbidden_regions, obj, dim, true);
			self.origin[[obj, dim]].tighten_max(ctx, sweep[dim], reason)?;

			self.origin_ub[[obj, dim]] = sweep[dim];
		}
		Ok(())
	}

	/// Prunes the lower bound of an object's origin in a specific dimension.
	///
	/// This method implements the core sweep-line algorithm to find the
	/// earliest possible feasible position for the object's origin. It starts
	/// a "sweep point" at the object's lower bound and moves it through the
	/// multi-dimensional space, "jumping" over forbidden regions until a
	/// feasible position is found.
	///
	/// If the first feasible position found is greater than the current lower
	/// bound, the variable's domain is pruned. If no feasible position is
	/// found within the object's domain, a conflict is triggered.
	fn prune_min<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		forbidden_regions: &[(Region, usize)],
		obj: usize,
		dim: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
	{
		// `sweep` is the current point being checked for feasibility.
		let mut sweep = self.origin_lb.row(obj).to_vec();
		// `jump` stores the earliest possible escape point from a forbidden region.
		let mut jump: Vec<_> = self.origin_ub.row(obj).iter().map(|v| v + 1).collect();
		let mut b = true;

		// Find the first forbidden region that the sweep point is inside.
		let mut fr = Region::find_collision(forbidden_regions.iter().map(|(r, _)| r), &sweep);
		while b && fr.is_some() {
			// Update the jump point: to escape the current forbidden region `fr`,
			// we must jump to at least its upper bound + 1 in some dimension.
			// We take the minimum of all possible jump points.
			for (i, j) in jump.iter_mut().enumerate() {
				*j = cmp::min(*j, fr.unwrap().max(i) + 1);
			}

			let lb = self.origin_lb.row(obj);
			let ub = self.origin_ub.row(obj);

			// Adjust the sweep point to the new jump location.
			b = Self::adjust_sweep_min(&mut sweep, &mut jump, lb, ub, dim);

			// Check if the new sweep point is in another forbidden region.
			fr = Region::find_collision(forbidden_regions.iter().map(|(r, _)| r), &sweep);
		}
		// If the sweep found a new, higher feasible lower bound, propagate it.
		if sweep[dim] != self.origin_lb[[obj, dim]] {
			let reason = self.explain_propagation(ctx, forbidden_regions, obj, dim, false);
			self.origin[[obj, dim]].tighten_min(ctx, sweep[dim], reason)?;

			self.origin_lb[[obj, dim]] = sweep[dim];
		}
		Ok(())
	}
}

impl<const STRICT: bool, E, I1, I2> Constraint<E> for IntNoOverlapSweep<STRICT, I1, I2>
where
	E: ReasoningEngine,
	I1: IntModelActions<E>,
	I2: IntModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if self.origin.iter_elem().all(|v| v.val(ctx).is_some())
			&& self.size.iter_elem().all(|v| v.val(ctx).is_some())
		{
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let box_pos = self
			.origin
			.row_iter()
			.map(|row| {
				row.iter()
					.map(|v| slv.solver_view(v.clone().into()))
					.collect()
			})
			.collect();
		let box_size = self
			.size
			.row_iter()
			.map(|row| {
				row.iter()
					.map(|v| slv.solver_view(v.clone().into()))
					.collect()
			})
			.collect();
		IntNoOverlapSweep::<STRICT, _, _>::post(slv, box_pos, box_size);
		Ok(())
	}
}

impl<const STRICT: bool, E, I1, I2> Propagator<E> for IntNoOverlapSweep<STRICT, I1, I2>
where
	E: ReasoningEngine,
	I1: IntSolverActions<E>,
	I2: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Lowest);

		// The propagator needs to be re-run whenever the bounds of any origin or
		// size variable change.
		for v in self.origin.iter_elem() {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
		for v in self.size.iter_elem() {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	#[tracing::instrument(name = "int_no_overlap", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// Cache the current bounds of all variables.
		for o in 0..self.num_objects() {
			for d in 0..self.num_dimensions() {
				self.origin_ub[[o, d]] = self.origin[[o, d]].max(ctx);
				self.origin_lb[[o, d]] = self.origin[[o, d]].min(ctx);
				self.size_lb[[o, d]] = self.size[[o, d]].min(ctx);
			}
		}

		// Main propagation loop: iterate through each object that is still a "target".
		for obj in 0..self.num_objects() {
			// Skip objects that are already fixed and verified.
			if ctx.trailed(self.target[obj]) {
				continue;
			}

			// In non-strict mode, objects with size 0 do not need to be considered.
			if !STRICT && self.size.row(obj).iter().any(|v| v.val(ctx) == Some(0)) {
				continue;
			}

			// Generate forbidden regions for the current object.
			let forbidden_regions = self.forbidden_regions(ctx, obj);
			if !forbidden_regions.is_empty() {
				// Check for conflicts: if an object is fixed and is in a forbidden
				// region, it's a conflict.
				if self.fixed_object(obj) {
					let reason = self.explain_propagation(ctx, &forbidden_regions, obj, 0, false);
					// Trigger a conflict by increasing the lower bound.
					self.origin[[obj, 0]].tighten_min(ctx, self.origin_lb[[obj, 0]] + 1, reason)?;
				}

				// Prune the domains of the origin variables for the current object.
				let mut all_fixed = true;
				for d in 0..self.num_dimensions() {
					self.prune_min(ctx, &forbidden_regions, obj, d)?;
					self.prune_max(ctx, &forbidden_regions, obj, d)?;

					if self.origin_lb[[obj, d]] != self.origin_ub[[obj, d]] {
						all_fixed = false;
					}
				}
				// Target optimization: If pruning has fixed the object at a feasible
				// position, mark it as no longer being a target.
				if all_fixed {
					let _ = ctx.set_trailed(self.target[obj], true);
				}
			}
		}

		// Source optimization: Update the bounding box of all non-fixed objects.
		for obj in 0..self.num_objects() {
			if ctx.trailed(self.target[obj]) {
				continue;
			}
			for i in 0..self.num_dimensions() {
				*self.bounding_box.min_mut(i) =
					cmp::min(self.bounding_box.min(i), self.origin_lb[[obj, i]]);
				*self.bounding_box.max_mut(i) = cmp::max(
					self.bounding_box.max(i),
					self.origin_ub[[obj, i]] + self.size_lb[[obj, i]] - 1,
				);
			}
		}

		// Identify objects that have lost their "source" property. If a fixed
		// object is now completely disjoint from the bounding box of all other
		// non-fixed objects, it can no longer create forbidden regions for them.
		for obj in 0..self.num_objects() {
			if ctx.trailed(self.target[obj]) && self.disjoint(&self.bounding_box, obj) {
				let _ = ctx.set_trailed(self.source[obj], true);
			}
		}

		Ok(())
	}
}

impl Region {
	/// Determines if two regions can be coalesced and their relationship.
	///
	/// This method checks if `self` and `other` can be merged. A merge is
	/// only possible if, in every dimension, one region is a subset of the
	/// other.
	///
	/// # Returns
	///
	/// - `Some(Ordering::Less)`: `self` is a subset of `other`.
	/// - `Some(Ordering::Greater)`: `other` is a subset of `self`.
	/// - `Some(Ordering::Equal)`: The regions are identical.
	/// - `None`: The regions cannot be coalesced because they are disjoint,
	///   partially overlapping, or touching in a way that doesn't form a subset
	///   relationship across all dimensions.
	fn coalesce(&self, other: &Self) -> Option<Ordering> {
		debug_assert_eq!(self.0.len(), other.0.len());

		let mut trend = Ordering::Equal;
		for (&(self_lb, self_ub), &(other_lb, other_ub)) in zip(&self.0, &other.0) {
			// No overlapping possible
			if self_ub + 1 < other_lb || self_lb > other_ub + 1 {
				return None;
			// The regions are equal
			} else if (self_lb, self_ub) == (other_lb, other_ub) {
				continue;
			// `other` is a subset of `self`
			} else if self_lb <= other_lb && self_ub >= other_ub {
				match trend {
					Ordering::Equal | Ordering::Greater => trend = Ordering::Greater,
					_ => return None,
				}
			// `self` is a subset of `other`
			} else if self_lb >= other_lb && self_ub <= other_ub {
				match trend {
					Ordering::Equal | Ordering::Less => trend = Ordering::Less,
					_ => return None,
				}
			// They overlap, but not such one is a subset of another
			} else {
				return None;
			}
		}
		Some(trend)
	}

	/// Finds the first region in a collection that contains the given point.
	fn find_collision<'a>(
		regions: impl IntoIterator<Item = &'a Region>,
		point: &[IntVal],
	) -> Option<&'a Region> {
		regions.into_iter().find(|r| {
			debug_assert_eq!(r.0.len(), point.len());
			r.0.iter()
				.zip(point)
				.all(|((lb, ub), p)| p >= lb && p <= ub)
		})
	}

	/// Returns the upper bound of the region in the specified dimension.
	fn max(&self, dim: usize) -> IntVal {
		self.0[dim].1
	}

	/// Returns a mutable reference to the upper bound of the region in the
	/// specified dimension.
	fn max_mut(&mut self, dim: usize) -> &mut IntVal {
		&mut self.0[dim].1
	}

	/// Returns the lower bound of the region in the specified dimension.
	fn min(&self, dim: usize) -> IntVal {
		self.0[dim].0
	}

	/// Returns a mutable reference to the lower bound of the region in the
	/// specified dimension.
	fn min_mut(&mut self, dim: usize) -> &mut IntVal {
		&mut self.0[dim].0
	}

	/// Checks if this region overlaps with another region defined by the given
	/// lower and upper bounds.
	fn overlaps(&self, other_lb: &[IntVal], other_ub: &[IntVal]) -> bool {
		debug_assert_eq!(self.0.len(), other_lb.len());
		debug_assert_eq!(self.0.len(), other_ub.len());

		self.0
			.iter()
			.zip(other_lb.iter().zip(other_ub))
			.all(|(&(lb, ub), (&o_lb, &o_ub))| o_lb <= ub && o_ub >= lb)
	}

	/// Creates a new `Region` with the given number of dimensions, initialized
	/// to default values.
	fn with_dimensions(dimensions: usize) -> Self {
		Self(vec![(IntVal::default(), IntVal::default()); dimensions])
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{Model, lower::InitConfig};

	#[test]
	#[traced_test]
	fn no_overlap_sat_2d() {
		let mut prb = Model::default();

		let x1 = prb.new_int_decision(1..=3);
		let y1 = prb.new_int_decision(1..=3);

		let x2 = prb.new_int_decision(1..=1);
		let y2 = prb.new_int_decision(1..=1);

		let size = prb.new_int_decision(2..=2);

		prb.no_overlap()
			.origins(vec![vec![x1, y1], vec![x2, y2]])
			.sizes(vec![vec![size, size], vec![size, size]])
			.strict(true)
			.post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, x2, y2]
			.into_iter()
			.map(|x| map.get(&mut slv, x))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
			1, 3, 1, 1
			2, 3, 1, 1
			3, 1, 1, 1
			3, 2, 1, 1
			3, 3, 1, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn no_overlap_sat_2d_nonstrict() {
		let mut prb = Model::default();

		let x1 = prb.new_int_decision(1..=3);
		let y1 = prb.new_int_decision(1..=1);

		let x2 = prb.new_int_decision(2..=3);
		let y2 = prb.new_int_decision(1..=1);

		let size1 = prb.new_int_decision(2..=2);
		let size2 = prb.new_int_decision(0..=0);

		prb.no_overlap()
			.origins(vec![vec![x1, y1], vec![x2, y2]])
			.sizes(vec![vec![size1, size1], vec![size2, size2]])
			.strict(false)
			.post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, x2, y2]
			.into_iter()
			.map(|x| map.get(&mut slv, x))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
			1, 1, 2, 1
			1, 1, 3, 1
			2, 1, 2, 1
			2, 1, 3, 1
			3, 1, 2, 1
			3, 1, 3, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn no_overlap_sat_3d() {
		let mut prb = Model::default();

		let x1 = prb.new_int_decision(2..=3);
		let y1 = prb.new_int_decision(5..=5);
		let z1 = prb.new_int_decision(2..=3);

		let x2 = prb.new_int_decision(1..=3);
		let y2 = prb.new_int_decision(4..=4);
		let z2 = prb.new_int_decision(2..=7);

		let size = prb.new_int_decision(5..=5);

		prb.no_overlap()
			.origins(vec![vec![x1, y1, z1], vec![x2, y2, z2]])
			.sizes(vec![vec![size, size, size], vec![size, size, size]])
			.strict(true)
			.post();

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, z1, x2, y2, z2]
			.into_iter()
			.map(|v| map.get(&mut slv, v))
			.collect_vec();

		slv.expect_solutions(
			&vars,
			expect![[r#"
			2, 5, 2, 1, 4, 7
			2, 5, 2, 2, 4, 7
			2, 5, 2, 3, 4, 7
			3, 5, 2, 1, 4, 7
			3, 5, 2, 2, 4, 7
			3, 5, 2, 3, 4, 7"#]],
		);
	}

	#[test]
	#[traced_test]
	fn no_overlap_unsat() {
		let mut prb = Model::default();
		let x1 = prb.new_int_decision(1..=2);
		let y1 = prb.new_int_decision(1..=2);

		let x2 = prb.new_int_decision(1..=2);
		let y2 = prb.new_int_decision(1..=2);

		let size = prb.new_int_decision(4..=4);

		prb.no_overlap()
			.origins(vec![vec![x1, y1], vec![x2, y2]])
			.sizes(vec![vec![size, size], vec![size, size]])
			.strict(true)
			.post();

		prb.assert_unsatisfiable();
	}
}
