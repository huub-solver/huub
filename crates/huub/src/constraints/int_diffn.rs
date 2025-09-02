//! Structure and algorithms for the integer diffn constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
use crate::{
	actions::{
		ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
	},
	constraints::{Conflict, Constraint, PropagationActions, Propagator},
	reformulate::ReformulationError,
	solver::{
		activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt, BoolView, IntView,
	},
	IntDecision, IntLitMeaning, IntVal,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `diffn_int` constraint within a model.
///
/// This constraint enforces that all k-dimensional rectangles do not overlap
/// given their starting position `box_posn` and their sizes `box_sizes`.
pub struct IntDiffn {
	/// The origin positions of all objects in all dimensions
	pub(crate) box_posn: Vec<Vec<IntDecision>>,
	/// The sizes of all objects in all dimensions
	pub(crate) box_size: Vec<Vec<IntDecision>>,
	/// True if non_strict diffn is used, i.e ignore all rectangles
	/// with a size of 0
	pub(crate) non_strict: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `diffn_int` constraint.
///
/// This propagator was first proposed in "Sweep as a Generic Pruning Technique
/// Applied to the Non-overlapping Rectangles Constraint" by Beldinau, Nicolas
/// and Carlsson, Mats. Then it was implemented within Gecode in https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-325845 and then
/// extended to lazy clause generation within this solver in
/// https://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-562628.
///
/// The core idea is that we reason about forbidden regions of each rectangle,
/// that is, regions we are not allowed to place the lower-left corner of a
/// rectangle due to the domains of the other rectangles. These regions are
/// forbidden in the sense that if we would put our rectangle at that
/// place, it would guarantee that atleast two rectangles are overlapping, which
/// violates the constraint.
pub struct IntDiffnSweep<const NON_STRICT: bool> {
	/// The origin positions of all objects in all dimensions
	box_posn: Vec<DimStore<IntView>>,
	/// The sizes of all objects in all dimensions
	box_size: Vec<DimStore<IntView>>,
	/// Number of dimensions
	dimensions: usize,
	/// Trail which tracks the target property, target[i] = 1 if is has been
	/// lost, and will let us skip some iterations since it at that point has
	/// been checked to be at a feasible position and fixed.
	target: Vec<TrailedInt>,
	/// Trail which tracks the source property, target[i] = 1 if is has been
	/// lost, and will allow it to be disregarded through the entire algorithm
	/// since it will not affect any other rectangle.
	source: Vec<TrailedInt>,
	/// Are all sizes fixed
	fixed_sizes: bool,
	/// Tracks the upper bound of the positions
	ub_tracker: Vec<DimStore<IntVal>>,
	/// Tracks the lower bound of the positions
	lb_tracker: Vec<DimStore<IntVal>>,
	/// Tracks the lower bound of the sizes
	lb_sizes: Vec<DimStore<IntVal>>,
	/// Used to see if any rectangle has lost its source property, that is; it
	/// is completely disjoint from all the others and therefore can be
	/// removed completely when reasoning in the rest of the algorithm since
	/// it will not effect any other triangle
	bounding_box: ForbiddenRegion,
	/// Stores all forbidden regions for a given object
	all_fr: Vec<ForbiddenRegion>,
}

impl<S: SimplificationActions> Constraint<S> for IntDiffn {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
		let box_pos: Vec<Vec<_>> = self
			.box_posn
			.iter()
			.map(|row| row.iter().map(|v| slv.get_solver_int(*v)).collect())
			.collect();

		let box_size: Vec<Vec<_>> = self
			.box_size
			.iter()
			.map(|row| row.iter().map(|v| slv.get_solver_int(*v)).collect())
			.collect();
		if self.non_strict {
			IntDiffnSweep::<true>::new_in(slv, box_pos, box_size);
		} else {
			IntDiffnSweep::<false>::new_in(slv, box_pos, box_size);
		}
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Active forbidden regions
struct ForbiddenRegion {
	/// Lower bound in each dimension
	lb: Vec<IntVal>,
	/// Upper bound in each dimension
	ub: Vec<IntVal>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Stores the all values for specific dimension
struct DimStore<T> {
    /// All values in a given dimension
	values: Vec<T>,
}

impl<const NON_STRICT: bool> IntDiffnSweep<NON_STRICT> {
	/// Prepare a new [`IntDiffnSweep`] propagator to be posted to the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
		solver: &mut P,
		box_posn: Vec<Vec<IntView>>,
		box_size: Vec<Vec<IntView>>,
	) {
		// Make sure all sizes are fixed before enqueueing
		let fixed = box_size
			.iter()
			.flatten()
			.all(|&v| solver.get_int_val(v).is_some());

		let mut box_posn_prop = Vec::new();
		let mut box_size_prop = Vec::new();

		for i in 0..box_posn.len() {
			box_posn_prop.push(DimStore {
				values: box_posn[i].clone(),
			});
			box_size_prop.push(DimStore {
				values: box_size[i].clone(),
			});
		}

		let target_trail = (0..box_size[0].len())
			.map(|_| solver.new_trailed_int(0))
			.collect();
		let source_trail = (0..box_size[0].len())
			.map(|_| solver.new_trailed_int(0))
			.collect();

		let lb_sizes_prop = vec![
			DimStore {
				values: vec![0; box_posn[0].len()]
			};
			box_posn.len()
		];
		let ub_tracker_prop = vec![
			DimStore {
				values: vec![0; box_posn[0].len()]
			};
			box_posn.len()
		];
		let lb_tracker_prop = vec![
			DimStore {
				values: vec![0; box_posn[0].len()]
			};
			box_posn.len()
		];

		let bounding_box_prop = ForbiddenRegion {
			lb: vec![i64::MAX; box_posn.len()],
			ub: vec![i64::MIN; box_posn.len()],
		};

		let all_fr_prop = Vec::new();

		let prop = solver.add_propagator(
			Box::new(Self {
				box_posn: box_posn_prop,
				box_size: box_size_prop,
				dimensions: box_posn.len(),
				target: target_trail,
				source: source_trail,
				fixed_sizes: fixed,
				ub_tracker: ub_tracker_prop,
				lb_tracker: lb_tracker_prop,
				lb_sizes: lb_sizes_prop,
				bounding_box: bounding_box_prop,
				all_fr: all_fr_prop,
			}),
			PriorityLevel::Lowest,
		);

		for v in box_posn.into_iter().flatten() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
		solver.enqueue_now(prop);
	}

	/// Prunes the lower bound of a given rectangle by searching for a feasible
	/// origin by using a sweep point which tracks the search and a jump point
	/// which tracks the actions to be taken by the sweep point. If a feasible
	/// origin is found, set the lower-bound of the rectangle to the position
	/// of the sweep, if no feasible origin is found, a conflict is reported.
	fn prune_min<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
	) -> Result<(), Conflict> {
		let mut sweep = vec![];
		let mut jump = vec![];
		let mut b = true;

		for d in 0..self.dimensions {
			sweep.push(self.lb_tracker[d].values[curr_obj_idx]);
			jump.push(self.ub_tracker[d].values[curr_obj_idx] + 1);
		}
		// Get the forbidden region our current sweep point is overlapping with
		let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, &self.all_fr);
		while b && infeasible_fr.is_some() {
			// The jump is always pointed toward upper bounds of forbiddens as this is where
			// we will find feasible origins
			for j in 0..self.dimensions {
				jump[j] = jump[j].min(infeasible_fr.unwrap().ub[j] + 1);
			}

			let lb: Vec<_> = self
				.lb_tracker
				.iter()
				.map(|d| d.values[curr_obj_idx])
				.collect();

			let ub: Vec<_> = self
				.ub_tracker
				.iter()
				.map(|d| d.values[curr_obj_idx])
				.collect();

			b = Self::adjust_sweep_min(
				&mut sweep,
				&mut jump,
				&lb,
				&ub,
				curr_dimension,
				self.dimensions,
			);

			infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, &self.all_fr);
		}
		// Don't bother to do any propagation if the sweep point is at the same place it
		// started
		if sweep[curr_dimension] != self.lb_tracker[curr_dimension].values[curr_obj_idx] {
			let reason =
				self.explain_propagation(actions, fr_support, curr_obj_idx, curr_dimension, false);
			actions.set_int_lower_bound(
				self.box_posn[curr_dimension].values[curr_obj_idx],
				sweep[curr_dimension],
				reason,
			)?;

			self.lb_tracker[curr_dimension].values[curr_obj_idx] = sweep[curr_dimension];
		}
		Ok(())
	}

	/// Prunes the upper bound of a given rectangle by searching for a feasible
	/// origin by using a sweep point which tracks the search and a jump point
	/// which tracks the actions to be taken by the sweep point. If a feasible
	/// origin is found, set the upper-bound of the rectangle to the position
	/// of the sweep, if no feasible origin is found, a conflict is reported.
	fn prune_max<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
	) -> Result<(), Conflict> {
		let mut sweep = vec![];
		let mut jump = vec![];
		let mut b = true;

		for i in 0..self.dimensions {
			sweep.push(self.ub_tracker[i].values[curr_obj_idx]);
			jump.push(self.lb_tracker[i].values[curr_obj_idx] - 1);
		}
		// Get the forbidden region our current sweep point is overlapping with
		let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, &self.all_fr);
		while b && infeasible_fr.is_some() {
			// The jump is always pointed toward upper bounds of forbiddens as this is where
			// we will find feasible origins
			for j in 0..self.dimensions {
				jump[j] = jump[j].max(infeasible_fr.unwrap().lb[j] - 1);
			}
			let lb: Vec<_> = self
				.lb_tracker
				.iter()
				.map(|d| d.values[curr_obj_idx])
				.collect();

			let ub: Vec<_> = self
				.ub_tracker
				.iter()
				.map(|d| d.values[curr_obj_idx])
				.collect();

			b = Self::adjust_sweep_max(
				&mut sweep,
				&mut jump,
				&lb,
				&ub,
				curr_dimension,
				self.dimensions,
			);

			infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, &self.all_fr);
		}

		// Don't bother to do any propagation if the sweep point is at the same place it
		// started
		if sweep[curr_dimension] != self.ub_tracker[curr_dimension].values[curr_obj_idx] {
			let reason =
				self.explain_propagation(actions, fr_support, curr_obj_idx, curr_dimension, true);

			actions.set_int_upper_bound(
				self.box_posn[curr_dimension].values[curr_obj_idx],
				sweep[curr_dimension],
				reason,
			)?;

			self.ub_tracker[curr_dimension].values[curr_obj_idx] = sweep[curr_dimension];
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
		fr: &ForbiddenRegion,
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
	fn gen_forbidden_regions<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &mut Vec<usize>,
		o_idx: usize,
		dimensions: usize,
	) -> Option<()> {
		self.all_fr.clear();
		for i in 0..self.box_posn[0].values.len() {
			// Check if the current object can be ignored if it has lost its source property
			if actions.get_trailed_int(self.source[i]) == 1 {
				continue;
			}

			if i == o_idx {
				continue;
			};

			let mut fr = ForbiddenRegion {
				lb: Vec::new(),
				ub: Vec::new(),
			};

			let mut exists = true;
			for d in 0..self.dimensions {
				let fr_lb = self.ub_tracker[d].values[i] - self.lb_sizes[d].values[o_idx] + 1;
				let fr_ub = self.lb_tracker[d].values[i] + self.lb_sizes[d].values[i] - 1;
				if fr_lb <= fr_ub {
					fr.lb.push(fr_lb);
					fr.ub.push(fr_ub);
				} else {
					exists = false;
				}
			}
			let mut regions_to_remove: Vec<(usize, usize)> = Vec::new();

			let lb: Vec<_> = self.lb_tracker.iter().map(|d| d.values[o_idx]).collect();

			let ub: Vec<_> = self.ub_tracker.iter().map(|d| d.values[o_idx]).collect();

			// Look for forbidden regions that are a subset of another such that they can be
			// merged
			if exists && Self::overlaps(&lb, &ub, &fr, dimensions) {
				let mut c = 0;
				for f in &mut self.all_fr {
					let fr_object = fr_support[c];
					let v = Self::coalesce(f, &fr, self.dimensions);

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
						// They overlap whilst none is a subset of another, they could be combined
						3 => continue,
						// No overlap possible
						4 => continue,
						_ => unreachable!("should not be possible"),
					}
					c += 1;
				}

				for (c, o) in regions_to_remove.iter().rev() {
					let _ = self.all_fr.remove(*c);
					fr_support.retain(|&x| x != *o);
				}

				if exists {
					fr_support.push(i);
					self.all_fr.push(fr);
				}
			}
		}

		if self.all_fr.is_empty() {
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
		all_fr: &'a [ForbiddenRegion],
	) -> Option<&'a ForbiddenRegion> {
		all_fr
			.iter()
			.find(|fr| (0..dimensions).all(|i| sweep[i] >= fr.lb[i] && sweep[i] <= fr.ub[i]))
	}

	/// Checks if given rectangle has a fixed origin position in all dimensions
	fn fixed_in_all_dimensions(&self, curr_obj_idx: usize) -> bool {
		let mut is_assigned = true;
		for d in 0..self.dimensions {
			let fixed =
				self.lb_tracker[d].values[curr_obj_idx] == self.ub_tracker[d].values[curr_obj_idx];
			if !fixed {
				is_assigned = false;
			}
		}
		is_assigned
	}

	/// Checks if tw forbidden regions can be coalesced into one
	/// Returns:
	/// 0 - Coalescing not possbile
	/// 1 - fr2 is a subset of fr1
	/// 2 - fr1 is a subset of fr2
	/// 3 - The regions are overlapping such that
	///     they are equal in all dimensions except 1
	/// 4 - The forbidden regions are equal
	fn coalesce(fr1: &mut ForbiddenRegion, fr2: &ForbiddenRegion, dimensions: usize) -> usize {
		let mut trend = 0;
		for d in 0..dimensions {
			// No overlapping possible
			if fr1.ub[d] + 1 < fr2.lb[d] || fr1.lb[d] > fr2.ub[d] + 1 {
				return 4;
			// The regions are equal
			} else if fr1.lb[d] == fr2.lb[d] && fr1.ub[d] == fr2.ub[d] {
				continue;
			// fr2 is a subset of fr1
			} else if fr1.lb[d] <= fr2.lb[d] && fr1.ub[d] >= fr2.ub[d] {
				match trend {
					0 | 1 => trend = 1,
					_ => return 4,
				}
			// fr1 is a subset of fr2
			} else if fr1.lb[d] >= fr2.lb[d] && fr1.ub[d] <= fr2.ub[d] {
				match trend {
					0 | 2 => trend = 2,
					_ => return 4,
				}
			// They overlap, but not such one is a subset of another
			// only allow this trend in one dimensions
			} else {
				match trend {
					0 => trend = 3,
					_ => return 4,
				}
			}
		}
		trend
	}

	/// Returns true if the given object and bounding_box are completely
	/// disjoint in any dimension
	fn disjoint(&self, bounding_box: &ForbiddenRegion, curr_obj_idx: usize) -> bool {
		for d in 0..self.dimensions {
			if self.ub_tracker[d].values[curr_obj_idx] + self.lb_sizes[d].values[curr_obj_idx] - 1
				< bounding_box.lb[d]
				|| self.lb_tracker[d].values[curr_obj_idx] > bounding_box.ub[d]
			{
				return true;
			}
		}
		false
	}

	/// Explains all forbidden regions by explaining all bounds of them and also
	/// attempting to lift the explained bounds if any forbidden region is
	/// overhanging the bounds of the object currently being propagated.
	fn explain_forbidden_regions<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
	) -> Vec<BoolView> {
		let mut reason = Vec::new();
		for (fr, &o_idx) in fr_support.iter().enumerate() {
			for d in 0..self.dimensions {
				// If sizes are not fixed, the lower bounds are assumed throughout the algorithm
				// and thus have to be added to the explanation
				if !self.fixed_sizes {
					reason.push(actions.get_int_lower_bound_lit(self.box_size[d].values[o_idx]));
				}
				let mut possible_ub = self.ub_tracker[d].values[o_idx];
				let origin_ub = self.ub_tracker[d].values[curr_obj_idx];

				let mut possible_lb = self.lb_tracker[d].values[o_idx];
				let origin_lb = self.lb_tracker[d].values[curr_obj_idx];

				// If a forbidden region is overhanging the currently active obejct, it can be
				// assumed to be smaller when explaining which
				if self.all_fr[fr].ub[d] > origin_ub {
					possible_lb = origin_ub - self.lb_sizes[d].values[o_idx] + 1;
				}

				if self.all_fr[fr].lb[d] < origin_lb {
					possible_ub = origin_lb + self.lb_sizes[d].values[curr_obj_idx] - 1;
				}

				reason.push(actions.get_int_lit(
					self.box_posn[d].values[o_idx],
					IntLitMeaning::Less(possible_ub + 1),
				));

				reason.push(actions.get_int_lit(
					self.box_posn[d].values[o_idx],
					IntLitMeaning::GreaterEq(possible_lb),
				));
			}
		}
		reason
	}

	/// Explains the propagation, by first explaining the bounds of the object
	/// that is currently being propagated and secondly, the bounds of the
	/// forbidden regions connected to that object.
	fn explain_propagation<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
		prune_upper: bool,
	) -> Vec<BoolView> {
		let mut reason: Vec<_> = Vec::new();
		for d in 0..self.dimensions {
			// If sizes are not fixed, the lower bounds are assumed throughout the algorithm
			// and thus have to be added to the explanation
			if !self.fixed_sizes {
				reason.push(actions.get_int_lower_bound_lit(self.box_size[d].values[curr_obj_idx]));
			}

			// The literal describing the opposite bound in the same dimension and object we
			// are propagating can be removed. Make sure the correct literal is not
			// explained.
			if d == curr_dimension {
				if prune_upper {
					reason.push(actions.get_int_lit(
						self.box_posn[d].values[curr_obj_idx],
						IntLitMeaning::Less(self.ub_tracker[d].values[curr_obj_idx] + 1),
					));
				} else {
					reason.push(actions.get_int_lit(
						self.box_posn[d].values[curr_obj_idx],
						IntLitMeaning::GreaterEq(self.lb_tracker[d].values[curr_obj_idx]),
					));
				}
			} else {
				reason.push(actions.get_int_lit(
					self.box_posn[d].values[curr_obj_idx],
					IntLitMeaning::Less(self.ub_tracker[d].values[curr_obj_idx] + 1),
				));
				reason.push(actions.get_int_lit(
					self.box_posn[d].values[curr_obj_idx],
					IntLitMeaning::GreaterEq(self.lb_tracker[d].values[curr_obj_idx]),
				));
			}
		}
		reason.extend(self.explain_forbidden_regions(actions, fr_support, curr_obj_idx));
		reason
	}
}

impl<const NON_STRICT: bool, P, E> Propagator<P, E> for IntDiffnSweep<NON_STRICT>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		for d in 0..self.dimensions {
			for o in 0..self.box_posn[0].values.len() {
				self.ub_tracker[d].values[o] =
					actions.get_int_upper_bound(self.box_posn[d].values[o]);
				self.lb_tracker[d].values[o] =
					actions.get_int_lower_bound(self.box_posn[d].values[o]);
				self.lb_sizes[d].values[o] =
					actions.get_int_lower_bound(self.box_size[d].values[o]);
			}
		}

		for o_idx in 0..self.box_posn[0].values.len() {
			// Skip if target property has been lost
			if actions.get_trailed_int(self.target[o_idx]) == 1 {
				continue;
			}

			if NON_STRICT
				&& (0..self.dimensions)
					.any(|d| actions.get_int_val(self.box_size[d].values[o_idx]) == Some(0))
			{
				continue;
			}
			let mut fr_support: Vec<usize> = Vec::new();

			if let Some(()) =
				self.gen_forbidden_regions::<P>(actions, &mut fr_support, o_idx, self.dimensions)
			{
				if self.fixed_in_all_dimensions(o_idx) {
					// Conflict will occur here since there exists forbidden regions for a fixed
					// object
					let reason = self.explain_propagation(actions, &fr_support, o_idx, 0, false);
					actions.set_int_lower_bound(
						self.box_posn[0].values[o_idx],
						self.ub_tracker[0].values[o_idx] + 1,
						reason,
					)?;
				}
				let mut all_fixed = true;
				for d in 0..self.dimensions {
					self.prune_min(actions, &fr_support, o_idx, d)?;

					self.prune_max(actions, &fr_support, o_idx, d)?;

					if self.lb_tracker[d].values[o_idx] != self.ub_tracker[d].values[o_idx] {
						all_fixed = false;
					}
				}
				// Since it is fixed in all dimensions and it is at a feasible position by not
				// causing any conflicts, remove its target property
				if all_fixed {
					let _ = actions.set_trailed_int(self.target[o_idx], 1);
				}
			}
		}

		// Source optimisations, create the largest possible bounding box
		for o_idx in 0..self.box_posn[0].values.len() {
			if actions.get_trailed_int(self.target[o_idx]) == 1 {
				continue;
			}
			for i in 0..self.dimensions {
				self.bounding_box.lb[i] =
					self.bounding_box.lb[i].min(self.lb_tracker[i].values[o_idx]);
				self.bounding_box.ub[i] = self.bounding_box.ub[i]
					.max(self.ub_tracker[i].values[o_idx] + self.lb_sizes[i].values[o_idx] - 1);
			}
		}

		// If the current rectangle has lost its target property (is fixed in a feasible
		// position) and is completely disjoint from the bounding box, remove its
		// source property (disregard it in the rest of the algorhtm)
		for o_idx in 0..self.box_posn[0].values.len() {
			if actions.get_trailed_int(self.target[o_idx]) == 1
				&& self.disjoint(&self.bounding_box, o_idx)
			{
				let _ = actions.set_trailed_int(self.source[o_idx], 1);
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

	use crate::{diffn_int, reformulate::InitConfig, Decision, Model};

	#[test]
	#[traced_test]
	fn test_diffn_unsat() {
		let mut prb = Model::default();
		let x1 = prb.new_int_var(1..=2);
		let x2 = prb.new_int_var(1..=2);

		let y1 = prb.new_int_var(1..=2);
		let y2 = prb.new_int_var(1..=2);

		let size = prb.new_int_var(4..=4);

		prb += diffn_int(
			vec![vec![x1, x2], vec![y1, y2]],
			vec![vec![size, size], vec![size, size]],
			false,
		);

		let (mut slv, _) = prb.to_solver(&InitConfig::default()).unwrap();

		slv.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_diffn_sat_2d() {
		let mut prb = Model::default();

		let x1 = prb.new_int_var(1..=3);
		let x2 = prb.new_int_var(1..=1);

		let y1 = prb.new_int_var(1..=3);
		let y2 = prb.new_int_var(1..=1);

		let size = prb.new_int_var(2..=2);

		prb += diffn_int(
			vec![vec![x1, x2], vec![y1, y2]],
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
		let x2 = prb.new_int_var(1..=3);

		let y1 = prb.new_int_var(5..=5);
		let y2 = prb.new_int_var(4..=4);

		let z1 = prb.new_int_var(2..=3);
		let z2 = prb.new_int_var(2..=7);

		let size = prb.new_int_var(5..=5);

		prb += diffn_int(
			vec![vec![x1, x2], vec![y1, y2], vec![z1, z2]],
			vec![vec![size, size], vec![size, size], vec![size, size]],
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
}
