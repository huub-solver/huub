//! Structure and algorithms for the integer diffn constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
use std::{cmp, iter::repeat_with, ops::AddAssign};

use crate::{
	IntLitMeaning, IntVal,
	actions::{
		ConstructionActions, InitActions, IntDecisionActions, IntInspectionActions,
		ReasoningContext, ReasoningEngine, ReformulationActions, TrailingActions,
	},
	constraints::{
		BoxedPropagator, Constraint, ModelIntView, Propagator, SimplificationStatus, SolverIntView,
	},
	helpers::matrix::Matrix,
	reformulate::ReformulationError,
	solver::{IntView, activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `diffn_int` constraint.
///
/// This propagator was originally proposed in "Sweep as a Generic Pruning
/// Technique Applied to the Non-overlapping Rectangles Constraint" by Beldinau,
/// Nicolas and Carlsson, Mats. Then it was implemented within Gecode in
/// https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-325845 and then extended to
/// lazy clause generation within this solver in
/// https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-562628.
///
/// The core idea is that we reason about forbidden regions of each rectangle,
/// that is, regions we are not allowed to place the lower-left corner of a
/// rectangle due to the domains of the other rectangles. These regions are
/// forbidden in the sense that if we would put our rectangle at that place, it
/// would guarantee that at least two rectangles are overlapping, which violates
/// the constraint.
///
/// All [`Matrix`] attributes have two dimensions/indexes, the first is the
/// object, the second is the dimension number.
pub struct IntDiffnSweep<const STRICT: bool, I> {
	/// The origin position of each object in each dimension
	origin: Matrix<2, I>,
	/// The size of each object in each dimension
	size: Matrix<2, I>,

	/// Trail which tracks the target property, target[i] = 1 if is has been
	/// lost, and will let us skip some iterations since it at that point has
	/// been checked to be at a feasible position and fixed.
	target: Box<[TrailedInt]>,
	/// Trail which tracks the source property, target[i] = 1 if is has been
	/// lost, and will allow it to be disregarded through the entire algorithm
	/// since it will not affect any other rectangle.
	source: Box<[TrailedInt]>,

	/// Whether all size variables where fixed when the propagator was posted.
	size_fixed: bool,

	/// Tracks the upper bound of the positions
	origin_ub: Matrix<2, IntVal>,
	/// Tracks the lower bound of the positions
	origin_lb: Matrix<2, IntVal>,
	/// Tracks the lower bound of the sizes
	size_lb: Matrix<2, IntVal>,

	/// Used to see if any rectangle has lost its source property, that is; it
	/// is completely disjoint from all the others and therefore can be removed
	/// completely when reasoning in the rest of the algorithm since it will not
	/// effect any other triangle
	bounding_box: Region,
	/// Stores all forbidden regions for the current object
	forbidden_regions: Vec<Region>,
}

impl<const STRICT: bool, E, I> Constraint<E> for IntDiffnSweep<STRICT, I>
where
	E: ReasoningEngine,
	I: ModelIntView<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;

		if self.origin.iter_elem().all(|v| v.val(ctx).is_some())
			&& self.origin.iter_elem().all(|v| v.val(ctx).is_some())
		{
			return Ok(SimplificationStatus::Subsumed);
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let box_pos = self
			.origin
			.row_iter()
			.map(|row| {
				row.iter()
					.map(|v| slv.solver_int(v.clone().into()))
					.collect()
			})
			.collect();
		let box_size = self
			.size
			.row_iter()
			.map(|row| {
				row.iter()
					.map(|v| slv.solver_int(v.clone().into()))
					.collect()
			})
			.collect();
		IntDiffnSweep::<STRICT, _>::post(slv, box_pos, box_size);
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A region in a multi-dimensional space.
struct Region {
	/// Lower bound in each dimension
	lb: Vec<IntVal>,
	/// Upper bound in each dimension
	ub: Vec<IntVal>,
}

impl<const STRICT: bool, I> IntDiffnSweep<STRICT, I> {
	fn num_objects(&self) -> usize {
		self.origin.len(0)
	}

	fn num_dimensions(&self) -> usize {
		self.origin.len(1)
	}

	/// Create a new [`IntDiffnSweep`] propagator, to be used within the given
	/// engine.
	pub(crate) fn new<E>(engine: &mut E, box_posn: Vec<Vec<I>>, box_size: Vec<Vec<I>>) -> Self
	where
		E: ConstructionActions + ReasoningContext + ?Sized,
		I: IntInspectionActions<E>,
	{
		assert_eq!(box_posn.len(), box_size.len());
		assert!(
			box_posn.is_empty()
				|| box_posn
					.iter()
					.chain(&box_size)
					.all(|v| v.len() == box_posn[0].len())
		);
		// Make sure all sizes are fixed before enqueueing
		let fixed_sizes = box_size.iter().flatten().all(|v| v.val(engine).is_some());

		let num_objects = box_posn.len();
		let num_dimensions = box_posn[0].len();

		let box_posn = Matrix::new(
			[num_objects, num_dimensions],
			box_posn.into_iter().flatten().collect(),
		);
		let box_size = Matrix::new(
			[num_objects, num_dimensions],
			box_size.into_iter().flatten().collect(),
		);

		let target = repeat_with(|| engine.new_trailed_int(0))
			.take(num_objects)
			.collect();
		let source = repeat_with(|| engine.new_trailed_int(0))
			.take(num_objects)
			.collect();

		let ub_tracker = Matrix::with_dimensions([num_objects, num_dimensions]);
		let lb_tracker = Matrix::with_dimensions([num_objects, num_dimensions]);
		let lb_sizes = Matrix::with_dimensions([num_objects, num_dimensions]);

		let bounding_box = Region {
			lb: vec![i64::MAX; num_dimensions],
			ub: vec![i64::MIN; num_dimensions],
		};

		let all_fr = Vec::new();

		Self {
			origin: box_posn,
			size: box_size,
			target,
			source,
			size_fixed: fixed_sizes,
			origin_ub: ub_tracker,
			origin_lb: lb_tracker,
			size_lb: lb_sizes,
			bounding_box,
			forbidden_regions: all_fr,
		}
	}

	/// Prunes the lower bound of a given rectangle by searching for a feasible
	/// origin by using a sweep point which tracks the search and a jump point
	/// which tracks the actions to be taken by the sweep point. If a feasible
	/// origin is found, set the lower-bound of the rectangle to the position
	/// of the sweep, if no feasible origin is found, a conflict is reported.
	fn prune_min<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let mut sweep = self.origin_lb.row(curr_obj_idx).to_vec();
		let mut jump: Vec<_> = self
			.origin_ub
			.row(curr_obj_idx)
			.iter()
			.map(|v| v + 1)
			.collect();
		let mut b = true;

		// Get the forbidden region our current sweep point is overlapping with
		let mut infeasible_fr =
			Self::infeasible_sweep(&sweep, self.num_dimensions(), &self.forbidden_regions);
		while b && infeasible_fr.is_some() {
			// The jump is always pointed toward upper bounds of forbiddens as this is where
			// we will find feasible origins
			for (i, j) in jump.iter_mut().enumerate() {
				*j = cmp::min(*j, infeasible_fr.unwrap().ub[i] + 1);
			}

			let lb = self.origin_lb.row(curr_obj_idx);
			let ub = self.origin_ub.row(curr_obj_idx);

			b = Self::adjust_sweep_min(
				&mut sweep,
				&mut jump,
				&lb,
				&ub,
				curr_dimension,
				self.num_dimensions(),
			);

			infeasible_fr =
				Self::infeasible_sweep(&sweep, self.num_dimensions(), &self.forbidden_regions);
		}
		// Don't bother to do any propagation if the sweep point is at the same place it
		// started
		if sweep[curr_dimension] != self.origin_lb[[curr_obj_idx, curr_dimension]] {
			let reason =
				self.explain_propagation(ctx, fr_support, curr_obj_idx, curr_dimension, false);
			self.origin[[curr_obj_idx, curr_dimension]].set_lower_bound(
				ctx,
				sweep[curr_dimension],
				reason,
			)?;

			self.origin_lb[[curr_obj_idx, curr_dimension]] = sweep[curr_dimension];
		}
		Ok(())
	}

	/// Prunes the upper bound of a given rectangle by searching for a feasible
	/// origin by using a sweep point which tracks the search and a jump point
	/// which tracks the actions to be taken by the sweep point. If a feasible
	/// origin is found, set the upper-bound of the rectangle to the position
	/// of the sweep, if no feasible origin is found, a conflict is reported.
	fn prune_max<E>(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
	) -> Result<(), E::Conflict>
	where
		E: ReasoningEngine,
		I: SolverIntView<E>,
	{
		let mut sweep = self.origin_ub.row(curr_obj_idx).to_vec();
		let mut jump: Vec<_> = self
			.origin_lb
			.row(curr_obj_idx)
			.iter()
			.map(|v| v - 1)
			.collect();
		let mut b = true;

		// Get the forbidden region our current sweep point is overlapping with
		let mut infeasible_fr =
			Self::infeasible_sweep(&sweep, self.num_dimensions(), &self.forbidden_regions);
		while b && infeasible_fr.is_some() {
			// The jump is always pointed toward upper bounds of forbiddens as this is where
			// we will find feasible origins
			for (i, j) in jump.iter_mut().enumerate() {
				*j = cmp::max(*j, infeasible_fr.unwrap().lb[i] - 1);
			}

			let lb = self.origin_lb.row(curr_obj_idx);
			let ub = self.origin_ub.row(curr_obj_idx);

			b = Self::adjust_sweep_max(
				&mut sweep,
				&mut jump,
				&lb,
				&ub,
				curr_dimension,
				self.num_dimensions(),
			);

			infeasible_fr =
				Self::infeasible_sweep(&sweep, self.num_dimensions(), &self.forbidden_regions);
		}

		// Don't bother to do any propagation if the sweep point is at the same place it
		// started
		if sweep[curr_dimension] != self.origin_ub[[curr_obj_idx, curr_dimension]] {
			let reason =
				self.explain_propagation(ctx, fr_support, curr_obj_idx, curr_dimension, true);
			self.origin[[curr_obj_idx, curr_dimension]].set_upper_bound(
				ctx,
				sweep[curr_dimension],
				reason,
			)?;

			self.origin_ub[[curr_obj_idx, curr_dimension]] = sweep[curr_dimension];
		}
		Ok(())
	}

	/// Given the position of the jump point acquired from the forbidden region
	/// the sweep point overlapped, check if the jump point is contained within
	/// the bounds of the rectangle we are pruning, if it is in a dimension, we
	/// can continue searching in that direction and check if it is a feasible
	/// origin
	fn adjust_sweep_min(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		curr_dimension: usize,
		dimensions: usize,
	) -> bool {
		for i in (0..dimensions).rev() {
			// Ensures that we check the dimension we are pruning last
			let rotation = (i + curr_dimension) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = curr_obj_ub[rotation] + 1;
			// If the current position of the sweep is still within the bounds of our
			// domains we can continue searching in this direction (dimension), otherwise
			// reset it
			if sweep[rotation] <= curr_obj_ub[rotation] {
				return true;
			} else {
				sweep[rotation] = curr_obj_lb[rotation];
			}
		}
		// No feasible origin for the rectangle exists, adjust the sweep point to
		// guarantee a conflict
		sweep[curr_dimension] = curr_obj_ub[curr_dimension] + 1;
		false
	}

	/// Given the position of the jump point acquired from the forbidden region
	/// the sweep point overlapped, check if the jump point is contained within
	/// the bounds of the rectangle we are pruning, if it is in a dimension, we
	/// can continue searching in that direction and check if it is a feasible
	/// origin
	fn adjust_sweep_max(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		curr_dimension: usize,
		dimensions: usize,
	) -> bool {
		for i in (0..dimensions).rev() {
			// Ensures that we check the dimension we are pruning last
			let rotation = (i + curr_dimension) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = curr_obj_lb[rotation] - 1;
			// If the current position of the sweep is still within the bounds of our
			// domains we can continue searching in this direction (dimension), otherwise
			// reset it
			if sweep[rotation] >= curr_obj_lb[rotation] {
				return true;
			} else {
				sweep[rotation] = curr_obj_ub[rotation];
			}
		}
		sweep[curr_dimension] = curr_obj_lb[curr_dimension] - 1;
		false
	}

	/// Checks if a forbidden overlaps with the given domain of lower and
	/// upper-bounds
	fn overlaps(
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		fr: &Region,
		dimensions: usize,
	) -> bool {
		for d in 0..dimensions {
			if curr_obj_lb[d] > fr.ub[d] || curr_obj_ub[d] < fr.lb[d] {
				return false;
			}
		}
		true
	}

	/// Generates forbidden regions given object o, forbidden regions that do
	/// not overlap with the starting domain of o are not included. Forbidden
	/// regions that are a subset of another are also not considered.
	fn gen_forbidden_regions<Ctx>(
		&mut self,
		ctx: &mut Ctx,
		fr_support: &mut Vec<usize>,
		o_idx: usize,
		dimensions: usize,
	) -> Option<()>
	where
		Ctx: ReasoningContext + TrailingActions,
	{
		self.forbidden_regions.clear();
		for i in 0..self.num_objects() {
			// Check if the current object can be ignored if it has lost its source property
			if ctx.trailed_int(self.source[i]) == 1 {
				continue;
			}

			if i == o_idx {
				continue;
			};

			let mut fr = Region {
				lb: Vec::new(),
				ub: Vec::new(),
			};

			let mut exists = true;
			for d in 0..self.num_dimensions() {
				let fr_lb = self.origin_ub[[i, d]] - self.size_lb[[o_idx, d]] + 1;
				let fr_ub = self.origin_lb[[i, d]] + self.size_lb[[i, d]] - 1;
				if fr_lb <= fr_ub {
					fr.lb.push(fr_lb);
					fr.ub.push(fr_ub);
				} else {
					exists = false;
				}
			}
			let mut regions_to_remove: Vec<(usize, usize)> = Vec::new();

			let lb = self.origin_lb.row(o_idx);
			let ub = self.origin_ub.row(o_idx);

			// Look for forbidden regions that are a subset of another such that they can be
			// merged
			if exists && Self::overlaps(&lb, &ub, &fr, dimensions) {
				let mut c = 0;
				let num_dimensions = self.num_dimensions();
				for f in &mut self.forbidden_regions {
					let fr_object = fr_support[c];
					let v = Self::coalesce(f, &fr, num_dimensions);

					match v {
						// fr is a subset of f
						0 | 1 => {
							//Do not add f vector of forbidden regions and do not track
							exists = false;
							break;
						}
						// f is a subset of fr
						2 => {
							// remove that forbidden region from all_fr and remove it from tracking
							regions_to_remove.push((c, fr_object));
						}
						// No overlap possible
						3 => continue,
						_ => unreachable!("should not be possible"),
					}
					c += 1;
				}

				for (c, o) in regions_to_remove.iter().rev() {
					let _ = self.forbidden_regions.remove(*c);
					fr_support.retain(|&x| x != *o);
				}

				if exists {
					fr_support.push(i);
					self.forbidden_regions.push(fr);
				}
			}
		}

		if self.forbidden_regions.is_empty() {
			None
		} else {
			Some(())
		}
	}

	/// Checks whether the sweep point is in a feasible position, if it is not,
	/// return the forbidden region it collided with
	fn infeasible_sweep<'a>(
		sweep: &[IntVal],
		dimensions: usize,
		all_fr: &'a [Region],
	) -> Option<&'a Region> {
		all_fr
			.iter()
			.find(|fr| (0..dimensions).all(|i| sweep[i] >= fr.lb[i] && sweep[i] <= fr.ub[i]))
	}

	/// Checks if given rectangle has a fixed origin position in all dimensions
	fn fixed_in_all_dimensions(&self, curr_obj_idx: usize) -> bool {
		for d in 0..self.num_dimensions() {
			if self.origin_lb[[curr_obj_idx, d]] != self.origin_ub[[curr_obj_idx, d]] {
				return false;
			}
		}
		true
	}

	/// Checks if tw forbidden regions can be coalesced into one
	/// Returns:
	/// 0 - Coalescing not possible
	/// 1 - fr2 is a subset of fr1
	/// 2 - fr1 is a subset of fr2
	/// 3 - The forbidden regions are equal
	fn coalesce(fr1: &mut Region, fr2: &Region, dimensions: usize) -> usize {
		let mut trend = 0;
		for d in 0..dimensions {
			// No overlapping possible
			if fr1.ub[d] + 1 < fr2.lb[d] || fr1.lb[d] > fr2.ub[d] + 1 {
				return 3;
			// The regions are equal
			} else if fr1.lb[d] == fr2.lb[d] && fr1.ub[d] == fr2.ub[d] {
				continue;
			// fr2 is a subset of fr1
			} else if fr1.lb[d] <= fr2.lb[d] && fr1.ub[d] >= fr2.ub[d] {
				match trend {
					0 | 1 => trend = 1,
					_ => return 3,
				}
			// fr1 is a subset of fr2
			} else if fr1.lb[d] >= fr2.lb[d] && fr1.ub[d] <= fr2.ub[d] {
				match trend {
					0 | 2 => trend = 2,
					_ => return 3,
				}
			// They overlap, but not such one is a subset of another
			} else {
				return 3;
			}
		}
		trend
	}

	/// Returns true if the given object and bounding_box are completely
	/// disjoint in any dimension
	fn disjoint(&self, bounding_box: &Region, curr_obj_idx: usize) -> bool {
		for d in 0..self.num_dimensions() {
			if self.origin_ub[[curr_obj_idx, d]] + self.size_lb[[curr_obj_idx, d]] - 1
				< bounding_box.lb[d]
				|| self.origin_lb[[curr_obj_idx, d]] > bounding_box.ub[d]
			{
				return true;
			}
		}
		false
	}

	/// Explains all forbidden regions by explaining all bounds of them and also
	/// attempting to lift the explained bounds if any forbidden region is
	/// overhanging the bounds of the object currently being propagated.
	fn explain_forbidden_regions<Ctx>(
		&mut self,
		ctx: &mut Ctx,
		fr_support: &[usize],
		curr_obj_idx: usize,
	) -> Vec<Ctx::Atom>
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		let mut reason = Vec::new();
		for (fr, &o_idx) in fr_support.iter().enumerate() {
			for d in 0..self.num_dimensions() {
				// If sizes are not fixed, the lower bounds are assumed throughout the algorithm
				// and thus have to be added to the explanation
				if !self.size_fixed {
					reason.push(self.size[[o_idx, d]].lower_bound_lit(ctx));
				}
				let mut possible_ub = self.origin_ub[[o_idx, d]];
				let origin_ub = self.origin_ub[[curr_obj_idx, d]];

				let mut possible_lb = self.origin_lb[[o_idx, d]];
				let origin_lb = self.origin_lb[[curr_obj_idx, d]];

				// If a forbidden region is overhanging the currently active object, it can be
				// assumed to be smaller when explaining which
				if self.forbidden_regions[fr].ub[d] > origin_ub {
					possible_lb = origin_ub - self.size_lb[[o_idx, d]] + 1;
				}

				if self.forbidden_regions[fr].lb[d] < origin_lb {
					possible_ub = origin_lb + self.size_lb[[curr_obj_idx, d]] - 1;
				}

				reason.push(self.origin[[o_idx, d]].lit(ctx, IntLitMeaning::Less(possible_ub + 1)));
				reason
					.push(self.origin[[o_idx, d]].lit(ctx, IntLitMeaning::GreaterEq(possible_lb)));
			}
		}
		reason
	}

	/// Explains the propagation, by first explaining the bounds of the object
	/// that is currently being propagated and secondly, the bounds of the
	/// forbidden regions connected to that object.
	fn explain_propagation<Ctx>(
		&mut self,
		ctx: &mut Ctx,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
		prune_upper: bool,
	) -> Vec<Ctx::Atom>
	where
		Ctx: ReasoningContext + ?Sized,
		I: IntDecisionActions<Ctx>,
	{
		let mut reason: Vec<_> = Vec::new();
		for d in 0..self.num_dimensions() {
			// If sizes are not fixed, the lower bounds are assumed throughout the algorithm
			// and thus have to be added to the explanation
			if !self.size_fixed {
				reason.push(self.size[[curr_obj_idx, d]].lower_bound_lit(ctx));
			}

			// The literal describing the opposite bound in the same dimension and object we
			// are propagating can be removed. Make sure the correct literal is not
			// explained.
			if d == curr_dimension {
				if prune_upper {
					reason.push(self.origin[[curr_obj_idx, d]].lit(
						ctx,
						IntLitMeaning::Less(self.origin_ub[[curr_obj_idx, d]] + 1),
					));
				} else {
					reason.push(self.origin[[curr_obj_idx, d]].lit(
						ctx,
						IntLitMeaning::GreaterEq(self.origin_lb[[curr_obj_idx, d]]),
					));
				}
			} else {
				reason.push(self.origin[[curr_obj_idx, d]].lit(
					ctx,
					IntLitMeaning::Less(self.origin_ub[[curr_obj_idx, d]] + 1),
				));
				reason.push(self.origin[[curr_obj_idx, d]].lit(
					ctx,
					IntLitMeaning::GreaterEq(self.origin_lb[[curr_obj_idx, d]]),
				));
			}
		}
		reason.extend(self.explain_forbidden_regions(ctx, fr_support, curr_obj_idx));
		reason
	}
}

impl<const STRICT: bool> IntDiffnSweep<STRICT, IntView> {
	/// Create a new [`IntDiffnSweep`] propagator and post it in the solver.
	pub fn post<E>(solver: &mut E, box_posn: Vec<Vec<IntView>>, box_size: Vec<Vec<IntView>>)
	where
		E: AddAssign<BoxedPropagator> + ConstructionActions + ReasoningContext + ?Sized,
		IntView: IntInspectionActions<E>,
	{
		let con: BoxedPropagator = Box::new(Self::new(solver, box_posn, box_size));
		*solver += con;
	}
}

impl<const STRICT: bool, E, I> Propagator<E> for IntDiffnSweep<STRICT, I>
where
	E: ReasoningEngine,
	I: SolverIntView<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		ctx.set_priority(PriorityLevel::Lowest);

		for v in self.origin.iter_elem().chain(self.size.iter_elem()) {
			v.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	#[tracing::instrument(name = "diffn", level = "trace", skip(self, ctx))]
	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		for o in 0..self.num_objects() {
			for d in 0..self.num_dimensions() {
				self.origin_ub[[o, d]] = self.origin[[o, d]].upper_bound(ctx);
				self.origin_lb[[o, d]] = self.origin[[o, d]].lower_bound(ctx);
				self.size_lb[[o, d]] = self.size[[o, d]].lower_bound(ctx);
			}
		}

		for o_idx in 0..self.num_objects() {
			// Skip if target property has been lost
			if ctx.trailed_int(self.target[o_idx]) == 1 {
				continue;
			}

			if !STRICT && self.size.row(o_idx).iter().any(|v| v.val(ctx) == Some(0)) {
				continue;
			}
			let mut fr_support: Vec<usize> = Vec::new();

			if let Some(()) =
				self.gen_forbidden_regions(ctx, &mut fr_support, o_idx, self.num_dimensions())
			{
				if self.fixed_in_all_dimensions(o_idx) {
					// Conflict will occur here since there exists forbidden regions for a fixed
					// object
					let reason = self.explain_propagation(ctx, &fr_support, o_idx, 0, false);
					self.origin[[o_idx, 0]].set_lower_bound(
						ctx,
						self.origin_ub[[o_idx, 0]] + 1,
						reason,
					)?;
				}
				let mut all_fixed = true;
				for d in 0..self.num_dimensions() {
					self.prune_min(ctx, &fr_support, o_idx, d)?;
					self.prune_max(ctx, &fr_support, o_idx, d)?;

					if self.origin_lb[[o_idx, d]] != self.origin_ub[[o_idx, d]] {
						all_fixed = false;
					}
				}
				// Since it is fixed in all dimensions and it is at a feasible position by not
				// causing any conflicts, remove its target property
				if all_fixed {
					let _ = ctx.set_trailed_int(self.target[o_idx], 1);
				}
			}
		}

		// Source optimizations, create the largest possible bounding box
		for o_idx in 0..self.num_objects() {
			if ctx.trailed_int(self.target[o_idx]) == 1 {
				continue;
			}
			for i in 0..self.num_dimensions() {
				self.bounding_box.lb[i] =
					cmp::min(self.bounding_box.lb[i], self.origin_lb[[o_idx, i]]);
				self.bounding_box.ub[i] = cmp::max(
					self.bounding_box.ub[i],
					self.origin_ub[[o_idx, i]] + self.size_lb[[o_idx, i]] - 1,
				);
			}
		}

		// If the current rectangle has lost its target property (is fixed in a feasible
		// position) and is completely disjoint from the bounding box, remove its
		// source property (disregard it in the rest of the algorithm)
		for o_idx in 0..self.num_objects() {
			if ctx.trailed_int(self.target[o_idx]) == 1 && self.disjoint(&self.bounding_box, o_idx)
			{
				let _ = ctx.set_trailed_int(self.source[o_idx], 1);
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{Decision, Model, diffn_int, reformulate::InitConfig};

	#[test]
	#[traced_test]
	fn test_diffn_unsat() {
		let mut prb = Model::default();
		let x1 = prb.new_int_var(1..=2);
		let y1 = prb.new_int_var(1..=2);

		let x2 = prb.new_int_var(1..=2);
		let y2 = prb.new_int_var(1..=2);

		let size = prb.new_int_var(4..=4);

		diffn_int(
			&mut prb,
			vec![vec![x1, y1], vec![x2, y2]],
			vec![vec![size, size], vec![size, size]],
			false,
		);

		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_diffn_sat_2d() {
		let mut prb = Model::default();

		let x1 = prb.new_int_var(1..=3);
		let y1 = prb.new_int_var(1..=3);

		let x2 = prb.new_int_var(1..=1);
		let y2 = prb.new_int_var(1..=1);

		let size = prb.new_int_var(2..=2);

		diffn_int(
			&mut prb,
			vec![vec![x1, y1], vec![x2, y2]],
			vec![vec![size, size], vec![size, size]],
			false,
		);

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, x2, y2]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
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
	fn test_diffn_sat_3d() {
		let mut prb = Model::default();

		let x1 = prb.new_int_var(2..=3);
		let y1 = prb.new_int_var(5..=5);
		let z1 = prb.new_int_var(2..=3);

		let x2 = prb.new_int_var(1..=3);
		let y2 = prb.new_int_var(4..=4);
		let z2 = prb.new_int_var(2..=7);

		let size = prb.new_int_var(5..=5);

		diffn_int(
			&mut prb,
			vec![vec![x1, y1, z1], vec![x2, y2, z2]],
			vec![vec![size, size, size], vec![size, size, size]],
			false,
		);

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, z1, x2, y2, z2]
			.into_iter()
			.map(|v| map.get(&mut slv, &Decision::from(v)))
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
	fn test_diffn_sat_2d_nonstrict() {
		let mut prb = Model::default();

		let x1 = prb.new_int_var(1..=3);
		let y1 = prb.new_int_var(1..=1);

		let x2 = prb.new_int_var(2..=3);
		let y2 = prb.new_int_var(1..=1);

		let size1 = prb.new_int_var(2..=2);
		let size2 = prb.new_int_var(0..=0);

		diffn_int(
			&mut prb,
			vec![vec![x1, y1], vec![x2, y2]],
			vec![vec![size1, size1], vec![size2, size2]],
			true,
		);

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![x1, y1, x2, y2]
			.into_iter()
			.map(|x| map.get(&mut slv, &Decision::from(x)))
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
}
