//! Structure and algorithms for the integer diffn constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
use std::cmp;
use tracing::trace;

use itertools::Itertools;
use smallvec::SmallVec;

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
/// This constraint enforces that all k-dimensional rectangles does no overlap
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
pub struct IntDiffnSweep {
	/// The origin positions of all objects in all dimensions
	box_posn: Vec<Vec<IntView>>,
	/// The sizes of all objects in all dimensions
	box_size: Vec<Vec<IntView>>,
	/// Number of dimensions
	dimensions: usize,
	/// Trail which tracks the target property, target[i] = 1 if is has been lost,
	/// and will make let us skip some iterations since it at that point has been
	/// checked to be at a feasible position and fixed.
	target: Vec<TrailedInt>,
	/// Trail which tracks the source property, target[i] = 1 if is has been lost,
	/// and will allow it to be disregarded through the entire algorithm since
	/// it will not affect any other rectangle.
	source: Vec<TrailedInt>,
	/// Are all sizes fixed
	fixed_sizes: bool,
	/// Tracks the upper bound of the positions
	ub_tracker: Vec<Vec<IntVal>>,
	/// Tracks the lower bound of the positions
	lb_tracker: Vec<Vec<IntVal>>,
	/// Tracks the lower bound of the sizes
	lb_sizes: Vec<Vec<IntVal>>,
	/// True if non_strict diffn is used, i.e ignore all rectangles with a size of 0
	non_strict: bool,
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
		IntDiffnSweep::new_in(slv, box_pos, box_size, self.non_strict);
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Active forbidden regions
struct ForbiddenRegion {
	/// lower bound of each dimension
	lb: SmallVec<[IntVal; 3]>,
	/// upper bound of each dimension
	ub: SmallVec<[IntVal; 3]>,
}

impl IntDiffnSweep {
	/// Prepare a new [`IntDiffnSweep`] propagator to be posted to the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
		solver: &mut P,
		box_posn: Vec<Vec<IntView>>,
		box_size: Vec<Vec<IntView>>,
		non_strict: bool,
	) {
		// Make sure all sizes are fixed before enqueueing
		let fixed = box_size
			.iter()
			.flatten()
			.all(|&v| solver.get_int_val(v).is_some());

		let mut box_posn_prop: Vec<Vec<IntView>> = box_posn.clone();
		let box_size_prop: Vec<Vec<IntView>> = box_size.clone();

		// Do not consider objects that are fixed and have a size of 0 when non_strict
		if non_strict && fixed {
			let mut box_size_fixed: Vec<_> = box_size
				.iter()
				.map(|row| {
					row.iter().map(|&v| {
						if solver.get_int_val(v) == Some(0) {
							1
						} else {
							0
						}
					})
				})
				.collect();

			let contains_zero: Vec<usize> = box_size_fixed
				.iter_mut()
				.map(|row| if row.contains(&1) { 1 } else { 0 })
				.collect();

			box_posn_prop = box_posn_prop
				.into_iter()
				.enumerate()
				.filter(|(i, _)| contains_zero[*i] == 0)
				.map(|(_, row)| row)
				.collect();

			box_posn_prop = box_posn_prop
				.into_iter()
				.enumerate()
				.filter(|(i, _)| contains_zero[*i] == 0)
				.map(|(_, row)| row)
				.collect();
		}

		// Tracks whether an rectangles posn domains are fixed
		let fixed_trail = (0..box_size.len())
			.map(|_| solver.new_trailed_int(0))
			.collect();
		let remove_trail = (0..box_size.len())
			.map(|_| solver.new_trailed_int(0))
			.collect();
		let lb_sizes_prop = vec![vec![0; box_posn[0].len()]; box_posn.len()];
		let ub_tracker_prop = vec![vec![0; box_posn[0].len()]; box_posn.len()];
		let lb_tracker_prop = vec![vec![0; box_posn[0].len()]; box_posn.len()];

		let prop = solver.add_propagator(
			Box::new(Self {
				box_posn: box_posn_prop,
				box_size: box_size_prop,
				dimensions: box_posn[0].len(),
				target: fixed_trail,
				source: remove_trail,
				fixed_sizes: fixed,
				ub_tracker: ub_tracker_prop,
				lb_tracker: lb_tracker_prop,
				lb_sizes: lb_sizes_prop,
				non_strict,
			}),
			PriorityLevel::Lowest,
		);

		for v in box_posn.into_iter().flatten() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
		}
	}

	/// Prune the lower bounds of the domain
	fn prune_min<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
		all_fr: &[ForbiddenRegion],
		all_fr_explain: &[ForbiddenRegion],
	) -> Result<(), Conflict> {
		let mut sweep = vec![];
		let mut jump = vec![];
		let mut b = true;

		for d in 0..self.dimensions {
			sweep.push(self.lb_tracker[curr_obj_idx][d]);
			jump.push(self.ub_tracker[curr_obj_idx][d] + 1);
		}
		let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
		while b && infeasible_fr.is_some() {
			for j in 0..self.dimensions {
				jump[j] = cmp::min(jump[j], infeasible_fr.unwrap().ub[j] + 1);
			}
			// Contains side-effects to change sweep
			b = Self::adjust_sweep_min(
				&mut sweep,
				&mut jump,
				&self.lb_tracker[curr_obj_idx],
				&self.ub_tracker[curr_obj_idx],
				curr_dimension,
				self.dimensions,
			);

			infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
		}
		// Start pruning here
		if sweep[curr_dimension] != self.lb_tracker[curr_obj_idx][curr_dimension] {
            trace!("SET [{:?}..{:?}] >= {}", self.lb_tracker[curr_obj_idx][curr_dimension], self.ub_tracker[curr_obj_idx][curr_dimension], sweep[curr_dimension]);
			let reason = self.explain_propagation(
				actions,
				all_fr_explain,
				fr_support,
				curr_obj_idx,
				curr_dimension,
				false,
			);
			actions.set_int_lower_bound(
				self.box_posn[curr_obj_idx][curr_dimension],
				sweep[curr_dimension],
				reason,
			)?;

			self.lb_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
		}
		Ok(())
	}

	/// Prune the upper bounds of the domain
	fn prune_max<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
		all_fr: &[ForbiddenRegion],
		all_fr_explain: &[ForbiddenRegion],
	) -> Result<(), Conflict> {
		let mut sweep = vec![];
		let mut jump = vec![];
		let mut b = true;

		for i in 0..self.dimensions {
			sweep.push(self.ub_tracker[curr_obj_idx][i]);
			jump.push(self.lb_tracker[curr_obj_idx][i] - 1);
		}
		let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
		while b && infeasible_fr.is_some() {
			for j in 0..self.dimensions {
				jump[j] = cmp::max(jump[j], infeasible_fr.unwrap().lb[j] - 1);
			}
			// Contains side-effects to change sweep
			b = Self::adjust_sweep_max(
				&mut sweep,
				&mut jump,
				&self.lb_tracker[curr_obj_idx],
				&self.ub_tracker[curr_obj_idx],
				curr_dimension,
				self.dimensions,
			);

			infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
		}
		if sweep[curr_dimension] != self.ub_tracker[curr_obj_idx][curr_dimension] {
			let reason = self.explain_propagation(
				actions,
				all_fr_explain,
				fr_support,
				curr_obj_idx,
				curr_dimension,
				true,
			);

			actions.set_int_upper_bound(
				self.box_posn[curr_obj_idx][curr_dimension],
				sweep[curr_dimension],
				reason,
			)?;

			self.ub_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
		}
		Ok(())
	}

	/// Adjusts the sweep and jump point when pruning the lower bound
	fn adjust_sweep_min(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		curr_dimension: usize,
		dimensions: usize,
	) -> bool {
		for i in (0..dimensions).rev() {
			let rotation = (i + curr_dimension) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = curr_obj_ub[rotation] + 1;
			if sweep[rotation] <= curr_obj_ub[rotation] {
				return true;
			} else {
				// Reset sweep-point
				sweep[rotation] = curr_obj_lb[rotation];
			}
		}
		sweep[curr_dimension] = curr_obj_ub[curr_dimension] + 1;
		false
	}

	/// Adjusts the sweep and jump point when pruning the upper bound
	fn adjust_sweep_max(
		sweep: &mut [IntVal],
		jump: &mut [IntVal],
		curr_obj_lb: &[IntVal],
		curr_obj_ub: &[IntVal],
		curr_dimension: usize,
		dimensions: usize,
	) -> bool {
		for i in (0..dimensions).rev() {
			let rotation = (i + curr_dimension) % dimensions;
			sweep[rotation] = jump[rotation];
			jump[rotation] = curr_obj_lb[rotation] - 1;
			if sweep[rotation] >= curr_obj_lb[rotation] {
				return true;
			} else {
				// Reset sweep-point
				sweep[rotation] = curr_obj_ub[rotation];
			}
		}
		sweep[curr_dimension] = curr_obj_lb[curr_dimension] - 1;
		false
	}

	/// Checks if a forbidden overlaps with the starting domain
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

	/// Generates forbidden regions given object o, forbidden regions that do not overlap with
	/// the starting domain of o are not included
	fn generate_fr<P: PropagationActions>(
		&self,
		actions: &mut P,
		fr_support: &mut Vec<usize>,
		o_idx: usize,
		dimensions: usize,
	) -> Option<(Vec<ForbiddenRegion>, Vec<ForbiddenRegion>)> {
		// TODO: To avoid uneccesary allocations, this could be moved to self
		let mut all_fr: Vec<ForbiddenRegion> = Vec::new();
		// All forbidden regions but excluding the combine optimization from coalesce
		let mut all_fr_no_combine: Vec<ForbiddenRegion> = Vec::new();
		for i in 0..self.box_posn.len() {
			// Check if the current object can be ignored if it has lost its source property
			if actions.get_trailed_int(self.source[i]) == 1 {
				continue;
			}
			let mut fr = ForbiddenRegion {
				lb: SmallVec::<[IntVal; 3]>::new(),
				ub: SmallVec::<[IntVal; 3]>::new(),
			};

			if i == o_idx {
				continue;
			};
			let mut exists = true;
			for d in 0..self.dimensions {
				let pos_ub: IntVal = self.ub_tracker[i][d];
				let pos_lb: IntVal = self.lb_tracker[i][d];
				let curr_size = self.lb_sizes[o_idx][d];
				let size = self.lb_sizes[i][d];
				let fr_lb = pos_ub - curr_size + 1;
				let fr_ub = pos_lb + size - 1;
				if fr_lb <= fr_ub {
					fr.lb.push(fr_lb);
					fr.ub.push(fr_ub);
				} else {
					exists = false;
				}
			}
			let mut regions_to_remove: Vec<(usize, usize)> = Vec::new();
			if exists
				&& Self::overlaps(
					&self.lb_tracker[o_idx],
					&self.ub_tracker[o_idx],
					&fr,
					dimensions,
				) {
				let fr_copy = fr.clone();
				let mut c = 0;
				for f in &mut all_fr {
					let fr_object = fr_support[c];
					let (v, e) = Self::coalesce(f, &fr, self.dimensions);

					match (v, e) {
						// fr is a subset of f
						(0 | 1, _) => {
							//Do not add f vector of forbidden regions and do not track
							exists = false;
							break;
						}
						// f is a subset of fr
						(2, _) => {
							// remove that forbidden region from all_fr and remove it from tracking
							regions_to_remove.push((c, fr_object));
						}
						// they overlap whilst none is a subset of another combine them
						(3, Some(e)) => {
							f.lb[e] = cmp::min(f.lb[e], fr.lb[e]);
							f.ub[e] = cmp::max(f.ub[e], fr.ub[e]);
							// exists = false;
							break;
						}
						// No overlap possible
						(4, _) => continue,
						_ => panic!("should not be possible"),
					}
					c += 1;
				}

				for (c, o) in regions_to_remove.iter().rev() {
					assert!(fr_support[*c] == *o, "wrong fr support");
					//println!("WOHOOO IGNORED WSHIT");
					let _ = all_fr.remove(*c);
					let _ = all_fr_no_combine.remove(*c);
					fr_support.retain(|&x| x != *o);
				}

				if exists {
					fr_support.push(i);
					all_fr.push(fr);
					all_fr_no_combine.push(fr_copy);
				}
			}
		}
		if all_fr.is_empty() {
			None
		} else {
			Some((all_fr, all_fr_no_combine))
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
			let fixed = self.lb_tracker[curr_obj_idx][d] == self.ub_tracker[curr_obj_idx][d];
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
	fn coalesce(
		fr1: &mut ForbiddenRegion,
		fr2: &ForbiddenRegion,
		dimensions: usize,
	) -> (usize, Option<usize>) {
		let mut trend = 0;
		let mut e = None;
		for d in 0..dimensions {
			// No overlapping possible
			if fr1.ub[d] + 1 < fr2.lb[d] || fr1.lb[d] > fr2.ub[d] + 1 {
				return (4, None);
			// The regions are equal
			} else if fr1.lb[d] == fr2.lb[d] && fr1.ub[d] == fr2.ub[d] {
				continue;
			// fr2 is a subset of fr1
			} else if fr1.lb[d] <= fr2.lb[d] && fr1.ub[d] >= fr2.ub[d] {
				match trend {
					0 | 1 => trend = 1,
					_ => return (4, None),
				}
			// fr1 is a subset of fr2
			} else if fr1.lb[d] >= fr2.lb[d] && fr1.ub[d] <= fr2.ub[d] {
				match trend {
					0 | 2 => trend = 2,
					_ => return (4, None),
				}
			// They overlap, but not such one is a subset of another
			// only allow this trend in one dimensions
			} else {
				e = Some(d);
				match trend {
					0 => trend = 3,
					_ => return (4, None),
				}
			}
		}
		(trend, e)
	}

	/// Returns turue if the given object and bounding_box are completely disjoint
	/// in any dimension
	fn disjoint(&self, bounding_box: &ForbiddenRegion, curr_obj_idx: usize) -> bool {
		for d in 0..self.dimensions {
			if self.ub_tracker[curr_obj_idx][d] + self.lb_sizes[curr_obj_idx][d] - 1
				< bounding_box.lb[d]
				|| self.lb_tracker[curr_obj_idx][d] > bounding_box.ub[d]
			{
				return true;
			}
		}
		false
	}

	/// Explains all forbidden regions
	fn explain_fr<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		all_fr: &[ForbiddenRegion],
		fr_support: &[usize],
		curr_obj_idx: usize,
	) -> Vec<BoolView> {
		let mut reason = Vec::new();
		for (fr, &o_idx) in fr_support.iter().enumerate() {
			for d in 0..self.dimensions {
				if !self.fixed_sizes {
					reason.push(actions.get_int_lower_bound_lit(self.box_size[o_idx][d]));
				}
				let mut possible_ub = self.ub_tracker[o_idx][d];
				let origin_ub = self.ub_tracker[curr_obj_idx][d];

				let mut possible_lb = self.lb_tracker[o_idx][d];
				let origin_lb = self.lb_tracker[curr_obj_idx][d];

				if all_fr[fr].ub[d] > origin_ub {
					possible_lb =
						origin_ub - actions.get_int_lower_bound(self.box_size[o_idx][d]) + 1;
				}

				if all_fr[fr].lb[d] < origin_lb {
					possible_ub =
						origin_lb + actions.get_int_lower_bound(self.box_size[curr_obj_idx][d]) - 1;
				}

                trace!("reason [{:?}..{:?}] < {}", self.lb_tracker[o_idx][d], self.ub_tracker[o_idx][d], possible_ub+1);
				reason.push(actions.get_int_lit(
					self.box_posn[o_idx][d],
					IntLitMeaning::Less(possible_ub + 1),
				));

                trace!("reason [{:?}..{:?}] >= {}", self.lb_tracker[o_idx][d], self.ub_tracker[o_idx][d], possible_lb);
				reason.push(actions.get_int_lit(
					self.box_posn[o_idx][d],
					IntLitMeaning::GreaterEq(possible_lb),
				));
			}
		}
		reason
	}

	/// Explains the propagations
	fn explain_propagation<P: PropagationActions>(
		&mut self,
		actions: &mut P,
		all_fr: &[ForbiddenRegion],
		fr_support: &[usize],
		curr_obj_idx: usize,
		curr_dimension: usize,
		prune_upper: bool,
	) -> Vec<BoolView> {
        trace!("PROPAGATION");
		let mut reason: Vec<_> = Vec::new();
		for d in 0..self.dimensions {
			// If sizes are not fixed, add reason for them
			if !self.fixed_sizes {
                trace!("reason size [{:?}..{:?}] >= {}", actions.get_int_lower_bound(self.box_size[curr_obj_idx][d]), actions.get_int_upper_bound(self.box_size[curr_obj_idx][d]), actions.get_int_lower_bound(self.box_size[curr_obj_idx][d]));
				reason.push(actions.get_int_lower_bound_lit(self.box_size[curr_obj_idx][d]));
			}

			if d == curr_dimension {
				if prune_upper {
                    trace!("reason [{:?}..{:?}] < {}", self.lb_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d] + 1);
					reason.push(actions.get_int_lit(
						self.box_posn[curr_obj_idx][d],
						IntLitMeaning::Less(self.ub_tracker[curr_obj_idx][d] + 1),
					));
				} else {
                    trace!("reason [{:?}..{:?}] >= {}", self.lb_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d], self.lb_tracker[curr_obj_idx][d]);
					reason.push(actions.get_int_lit(
						self.box_posn[curr_obj_idx][d],
						IntLitMeaning::GreaterEq(self.lb_tracker[curr_obj_idx][d]),
					));
				}
			} else {
                trace!("reason [{:?}..{:?}] < {}", self.lb_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d] + 1);
				reason.push(actions.get_int_lit(
					self.box_posn[curr_obj_idx][d],
					IntLitMeaning::Less(self.ub_tracker[curr_obj_idx][d] + 1),
				));
                trace!("reason [{:?}..{:?}] >= {}", self.lb_tracker[curr_obj_idx][d], self.ub_tracker[curr_obj_idx][d], self.lb_tracker[curr_obj_idx][d]);
				reason.push(actions.get_int_lit(
					self.box_posn[curr_obj_idx][d],
					IntLitMeaning::GreaterEq(self.lb_tracker[curr_obj_idx][d]),
				));
			}
		}
		reason.extend(self.explain_fr(actions, all_fr, fr_support, curr_obj_idx));
		reason
	}
}

impl<P, E> Propagator<P, E> for IntDiffnSweep
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		for o in 0..self.box_posn.len() {
			for d in 0..self.dimensions {
				self.ub_tracker[o][d] = actions.get_int_upper_bound(self.box_posn[o][d]);
				self.lb_tracker[o][d] = actions.get_int_lower_bound(self.box_posn[o][d]);
				self.lb_sizes[o][d] = actions.get_int_lower_bound(self.box_size[o][d]);
			}
		}

		for o_idx in 0..self.box_posn.len() {
			// Skip if target property has been lost
			if actions.get_trailed_int(self.target[o_idx]) == 1 {
				continue;
			}

			if self.non_strict
				&& (0..self.dimensions)
					.any(|d| actions.get_int_val(self.box_size[o_idx][d]) == Some(0))
			{
				continue;
			}
			let mut fr_support: Vec<usize> = Vec::new();

			if let Some((all_fr, all_fr_explain)) =
				self.generate_fr::<P>(actions, &mut fr_support, o_idx, self.dimensions)
			{
				if self.fixed_in_all_dimensions(o_idx) {
					// Conflict will occur here since there exists forbidden regions for a fixed
					// object
					// TODO: Conflict occurs in all dimensions but we only reason about it in one
					let reason =
						self.explain_propagation(actions, &all_fr, &fr_support, o_idx, 0, false);
					actions.set_int_upper_bound(
						self.box_posn[o_idx][0],
						self.ub_tracker[o_idx][0] + 1,
						reason,
					)?;
				}
				let mut all_fixed = true;
				for d in 0..self.dimensions {
					self.prune_min(actions, &fr_support, o_idx, d, &all_fr, &all_fr_explain)?;

					self.prune_max(actions, &fr_support, o_idx, d, &all_fr, &all_fr_explain)?;

					if self.lb_tracker[o_idx][d] != self.ub_tracker[o_idx][d] {
						all_fixed = false;
					}
				}
				if all_fixed {
					let _ = actions.set_trailed_int(self.target[o_idx], 1);
				}
			}
		}

		// Source optimisations
		let mut active_b = ForbiddenRegion {
			lb: SmallVec::<[IntVal; 3]>::new(),
			ub: SmallVec::<[IntVal; 3]>::new(),
		};

		for _ in 0..self.dimensions {
			active_b.lb.push(i64::MAX);
			active_b.ub.push(i64::MIN);
		}

		for o_idx in 0..self.box_posn.len() {
			if actions.get_trailed_int(self.target[o_idx]) == 1 {
				continue;
			}
			for i in 0..self.dimensions {
				active_b.lb[i] = cmp::min(active_b.lb[i], self.lb_tracker[o_idx][i]);
				active_b.ub[i] = cmp::max(
					active_b.ub[i],
					self.ub_tracker[o_idx][i] + self.lb_sizes[o_idx][i] - 1,
				);
			}
		}

		for o_idx in 0..self.box_posn.len() {
			if actions.get_trailed_int(self.target[o_idx]) == 1 && self.disjoint(&active_b, o_idx) {
				let _ = actions.set_trailed_int(self.source[o_idx], 1);
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_diffn::IntDiffnSweep,
		diffn_int,
		reformulate::InitConfig,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
		Decision, Model,
	};

	#[test]
	#[traced_test]
	fn test_diffn() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let pos_1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let pos_2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([0..=5]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let pos_3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let pos_4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([4..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		let size_1 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([4..=4]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let size_2 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([3..=3]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let size_3 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let size_4 = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([2..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntDiffnSweep::new_in(
			&mut slv,
			vec![vec![pos_1, pos_2], vec![pos_3, pos_4]],
			vec![vec![size_1, size_2], vec![size_3, size_4]],
			false,
		);

		// slv.assert_all_solutions(&[pos_2, pos_4], |sol| sol.iter().all_unique());
	}

	#[test]
	#[traced_test]
	fn test_diffn_1() {
		let mut prb = Model::default();
		let x_pos_1 = prb.new_int_var((0..=5).into());
		let x_pos_2 = prb.new_int_var((1..=3).into());
		let x_pos_3 = prb.new_int_var((1..=3).into());
		let x_pos_4 = prb.new_int_var((3..=6).into());

		let x_size_1 = prb.new_int_var((4..=4).into());
		let x_size_2 = prb.new_int_var((1..=1).into());
		let x_size_3 = prb.new_int_var((2..=2).into());
		let x_size_4 = prb.new_int_var((2..=2).into());

		let y_pos_1 = prb.new_int_var((0..=5).into());
		let y_pos_2 = prb.new_int_var((1..=2).into());
		let y_pos_3 = prb.new_int_var((4..=4).into());
		let y_pos_4 = prb.new_int_var((2..=2).into());

		let y_size_1 = prb.new_int_var((3..=3).into());
		let y_size_2 = prb.new_int_var((1..=1).into());
		let y_size_3 = prb.new_int_var((2..=2).into());
		let y_size_4 = prb.new_int_var((1..=1).into());

		prb += diffn_int(
			vec![
				vec![x_pos_1, y_pos_1],
				vec![x_pos_2, y_pos_2],
				vec![x_pos_3, y_pos_3],
				vec![x_pos_4, y_pos_4],
			],
			vec![
				vec![x_size_1, y_size_1],
				vec![x_size_2, y_size_2],
				vec![x_size_3, y_size_3],
				vec![x_size_4, y_size_4],
			],
			false,
		);
		let (mut slv, map) = prb
			.to_solver::<PropagatingCadical<_>>(&InitConfig::default())
			.unwrap();
		let pos_vars = vec![
			vec![x_pos_1, y_pos_1],
			vec![x_pos_2, y_pos_2],
			vec![x_pos_3, y_pos_3],
			vec![x_pos_4, y_pos_4],
		]
		.into_iter()
		.flatten()
		.map(|x| map.get(&mut slv, &Decision::from(x)))
		.collect_vec();

		// let (solve_result, value) = slv.get_all_solutions(&pos_vars);
		// println!("solve_result {:?}, value {:?}", solve_result, value);
	}

	#[test]
	#[traced_test]
	fn test_diffn_2() {
		let mut prb = Model::default();
		let x_pos_1 = prb.new_int_var((0..=6).into());
		let x_pos_2 = prb.new_int_var((0..=6).into());
		let x_pos_3 = prb.new_int_var((0..=6).into());

		let x_size_1 = prb.new_int_var((1..=1).into());
		let x_size_2 = prb.new_int_var((2..=2).into());
		let x_size_3 = prb.new_int_var((3..=3).into());

		let y_pos_1 = prb.new_int_var((0..=6).into());
		let y_pos_2 = prb.new_int_var((0..=6).into());
		let y_pos_3 = prb.new_int_var((0..=6).into());

		let y_size_1 = prb.new_int_var((1..=1).into());
		let y_size_2 = prb.new_int_var((2..=2).into());
		let y_size_3 = prb.new_int_var((3..=3).into());

		prb += diffn_int(
			vec![
				vec![x_pos_1, y_pos_1],
				vec![x_pos_2, y_pos_2],
				vec![x_pos_3, y_pos_3],
			],
			vec![
				vec![x_size_1, y_size_1],
				vec![x_size_2, y_size_2],
				vec![x_size_3, y_size_3],
			],
			false,
		);
		let (mut slv, map) = prb
			.to_solver::<PropagatingCadical<_>>(&InitConfig::default())
			.unwrap();
		let pos_vars = vec![
			vec![x_pos_1, y_pos_1],
			vec![x_pos_2, y_pos_2],
			vec![x_pos_3, y_pos_3],
		]
		.into_iter()
		.flatten()
		.map(|x| map.get(&mut slv, &Decision::from(x)))
		.collect_vec();

		// let (solve_result, value) = slv.get_all_solutions(&pos_vars);
		// println!("solve_result {:?}, value {:?}", solve_result, value);
	}
}
