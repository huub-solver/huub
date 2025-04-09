//! Structure and algorithms for the integer diffn constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.
use std::cmp; use crate::{actions::{
    ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
},  constraints::{Conflict, Constraint, PropagationActions, Propagator},
    reformulate::ReformulationError, solver::{
	activation_list::IntPropCond, BoolView, trail::TrailedInt, queue::PriorityLevel, IntView, IntViewInner,
},  IntDecision, IntVal, IntLitMeaning};
use tracing::trace;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `diffn_int` constraint within a model.
///
/// This constraint enforces that all k-dimensional rectangles does no overlap
/// given their starting position `box_posn` and their sizes `box_sizes`.
pub struct IntDiffn {
    pub(crate) box_posn: Vec<Vec<IntDecision>>,
    pub(crate) box_size: Vec<Vec<IntDecision>>,
    pub(crate) non_strict: bool
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `diffn_int` constraint.
pub struct IntDiffnSweep {
    /// The origin positions of all objects in all dimensions
    box_posn: Vec<Vec<IntView>>,
    /// The sizes of all objects in all dimensions
    box_size: Vec<Vec<IntVal>>,
    /// Number of dimensions
    dimensions: usize,
    /// Trail which objects are fixed and can be fixed during propagation
    /// view this as a bitset where object i can be fixed if
    /// fixed[i] = 1
    fixed: TrailedInt,
    /// Trailed int of fixed objects that no longer have to be considered
    removed_objs: TrailedInt,
    bounded_box: BoundedBox
}

impl<S: SimplificationActions> Constraint<S> for IntDiffn {
	fn to_solver(&self, slv: &mut dyn ReformulationActions) -> Result<(), ReformulationError> {
        let box_pos: Vec<Vec<_>> = self.box_posn.iter()
            .map(|row|
                  row.iter()
                     .map(|v| slv.get_solver_int(*v))
                     .collect()
             )
             .collect();

        let box_size: Vec<Vec<_>> = self.box_size.iter()
            .map(|row|
                  row.iter()
                     .map(|v| slv.get_solver_int(*v))
                     .collect()
             )
             .collect();
        IntDiffnSweep::new_in(slv, box_pos, box_size, self.non_strict);
        Ok(())
	}
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
// Active forbidden regions
struct ForbiddenRegion {
	lb: Vec<IntVal>, // lower bound of each dimension
	ub: Vec<IntVal>  // upper bound of each dimension
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
// Active forbidden regions
struct BoundedBox {
	lb: Vec<TrailedInt>, // lower bound of each dimension
	ub: Vec<TrailedInt>  // upper bound of each dimension
}


impl IntDiffnSweep {
	/// Prepare a new [`IntDiffnSweep`] propagator to be posted to the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>(
        solver: &mut P,
        box_posn: Vec<Vec<IntView>>,
        box_size: Vec<Vec<IntView>>,
        non_strict: bool
        ) {
        // Make sure all sizes are fixed before enqueueing
		let enqueue = box_size
			.iter()
            .flatten()
			.all(|v| matches!(v, IntView(IntViewInner::Const(_))));
        // TODO: is there some way to delay the propagator
        // until all sizes are fixed
        if !enqueue { return () }


        let box_size_fixed: Vec<Vec<IntVal>> = box_size.iter()
             .map(|row|
                  row.iter()
                     .map(|&v| solver.get_int_lower_bound(v))
                     .collect()
             )
             .collect();


        let mut box_posn_prop: Vec<Vec<IntView>> = box_posn.clone();

        let bounded_lb = (0..box_posn.len())
            .map(|_| solver.new_trailed_int(i64::MAX))
            .collect();

        let bounded_ub = (0..box_posn.len())
            .map(|_| solver.new_trailed_int(i64::MIN))
            .collect();

        let bounded_box_trail = BoundedBox {
            lb: bounded_lb,
            ub: bounded_ub

        };

        if non_strict {
            let contains_zero: Vec<usize> = box_size_fixed.iter()
                .map(|row| if row.contains(&0) { 1 } else { 0 })
                .collect();

            box_posn_prop = box_posn_prop.into_iter()
                .enumerate()
                .filter(|(i, _)| contains_zero[*i] == 0)
                .map(|(_, row)| row)
                .collect();

            box_posn_prop = box_posn_prop.into_iter()
                .enumerate()
                .filter(|(i, _)| contains_zero[*i] == 0)
                .map(|(_, row)| row)
                .collect();

            println!("{:?}", box_posn_prop.len());
        }

        let fixed_trail = solver.new_trailed_int(0);
        let remove_trail = solver.new_trailed_int(0);

		let prop = solver.add_propagator(Box::new(Self {
            box_posn: box_posn_prop,
            box_size: box_size_fixed,
            dimensions: box_posn[0].len(),
            fixed: fixed_trail,
            removed_objs: remove_trail,
            bounded_box: bounded_box_trail
        }), PriorityLevel::Low);

        for v in box_posn.into_iter().flatten() {
            solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
        }
    }

    /// Prune the lower bounds of the domain
    fn prune_min<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        lb_tracker: &mut Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    //) -> Result<bool, Conflict> {
    ) -> Result<(bool, bool), Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for d in 0..self.dimensions {
            sweep.push(lb_tracker[curr_obj_idx][d]);
            jump.push(ub_tracker[curr_obj_idx][d] + 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep,
                                                       self.dimensions,
                                                       all_fr);
        while b && infeasible_fr.is_some() {
            for j in 0..self.dimensions {
                jump[j] = cmp::min(jump[j], infeasible_fr.unwrap().ub[j] + 1);
            }
            // Contains side-effects to change sweep
            b = Self::adjust_sweep_min::<P>(&mut sweep,
                                            &mut jump,
                                            &lb_tracker[curr_obj_idx],
                                            &ub_tracker[curr_obj_idx],
                                            curr_dimension,
                                            self.dimensions);

            infeasible_fr = Self::infeasible_sweep(&sweep,
                                                   self.dimensions,
                                                   all_fr);
        }
        // Start pruning here
        if b && sweep[curr_dimension] != lb_tracker[curr_obj_idx][curr_dimension]{
            let reason = self.explain_propagation(actions,
                                                  lb_tracker,
                                                  ub_tracker,
                                                  all_fr,
                                                  fr_support,
                                                  curr_obj_idx,
                                                  curr_dimension,
                                                  false);
            actions.set_int_lower_bound(
                self.box_posn[curr_obj_idx][curr_dimension],
                sweep[curr_dimension], reason)?;

            lb_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
            trace!("Setting lb of object {} to {:?} in dimension {} in max",
                   curr_obj_idx,
                   sweep[curr_dimension],
                   curr_dimension);
            return Ok((b, true));
        }
        Ok((b, false))
    }

    /// Prune the upper bounds of the domain
    fn prune_max<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &mut Vec<Vec<IntVal>>,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    ) -> Result<(bool, bool), Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for i in 0..self.dimensions {
            sweep.push(ub_tracker[curr_obj_idx][i]);
            jump.push(lb_tracker[curr_obj_idx][i] - 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep,
                                                       self.dimensions,
                                                       all_fr);
        while b && infeasible_fr.is_some() {
            for j in 0..self.dimensions {
                jump[j] = cmp::max(jump[j], infeasible_fr.unwrap().lb[j] - 1);
            }
            // Contains side-effects to change sweep
            b = Self::adjust_sweep_max::<P>(&mut sweep,
                                            &mut jump,
                                            &lb_tracker[curr_obj_idx],
                                            &ub_tracker[curr_obj_idx],
                                            curr_dimension,
                                            self.dimensions);

            infeasible_fr = Self::infeasible_sweep(&sweep,
                                                   self.dimensions,
                                                   all_fr);
        }
        if b && sweep[curr_dimension] != ub_tracker[curr_obj_idx][curr_dimension]{
            let reason = self.explain_propagation(actions,
                                                  lb_tracker,
                                                  ub_tracker,
                                                  all_fr,
                                                  fr_support,
                                                  curr_obj_idx,
                                                  curr_dimension,
                                                  true);

            actions.set_int_upper_bound(self.box_posn[curr_obj_idx][curr_dimension],
                sweep[curr_dimension], reason)?;

            ub_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
            trace!("Setting ub of object {} to {:?} in dimension {} in max",
                   curr_obj_idx,
                   sweep[curr_dimension],
                   curr_dimension);
            return Ok((b, true));
        }
        Ok((b, false))
    }

    /// Adjusts the sweep and jump point when pruning the lower bound
    fn adjust_sweep_min<P: PropagationActions>(
        sweep: &mut Vec<IntVal>,
        jump: &mut Vec<IntVal>,
        curr_obj_lb: &Vec<IntVal>,
        curr_obj_ub: &Vec<IntVal>,
        curr_dimension: usize,
        dimensions: usize
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
        false
    }

    /// Adjusts the sweep and jump point when pruning the upper bound
    fn adjust_sweep_max<P: PropagationActions>(
        sweep: &mut Vec<IntVal>,
        jump: &mut Vec<IntVal>,
        curr_obj_lb: &Vec<IntVal>,
        curr_obj_ub: &Vec<IntVal>,
        curr_dimension: usize,
        dimensions: usize
    ) -> bool {
        for i in (0..dimensions).rev() {
            let rotation = (i + curr_dimension) % dimensions;
            sweep[rotation] = jump[rotation];
            jump[rotation] = curr_obj_lb[rotation] - 1;
            if sweep[rotation] >= curr_obj_lb[rotation] {
                return true
            } else {
                // Reset sweep-point
                sweep[rotation] = curr_obj_ub[rotation];
            }
        }
        false
    }



    /// Checks if a forbidden overlaps with the starting domain
    fn overlaps(
        curr_obj_lb: &Vec<IntVal>,
        curr_obj_ub: &Vec<IntVal>,
        fr: &ForbiddenRegion,
        dimensions:usize
    ) -> bool {
        for d in 0..dimensions {
            if curr_obj_lb[d] > fr.ub[d] || curr_obj_ub[d] < fr.lb[d] {
                return false;
            }
        }
        true
    }




    /// Generates forbidden regions given object o, forbidden regions that do not overlap with
    /// the starting domain of o is not included
    fn generate_fr<P: PropagationActions>(
        &self,
        actions: &mut P,
        fr_support: &mut Vec<usize>,
        o_idx:usize,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        dimensions:usize
    ) -> Option<Vec<ForbiddenRegion>> {
        let mut all_fr:Vec<ForbiddenRegion> = vec![];
        for i in 0..self.box_posn.len() {
            if actions.get_trailed_int(self.removed_objs) & (1 << o_idx) != 0 {
                continue;
            }
            let mut fr = ForbiddenRegion {
                lb: Vec::new(),
                ub: Vec::new()
            };

            if i == o_idx { continue };
            let mut exists = true;
            for d in 0..self.dimensions {
                let pos_ub: IntVal = ub_tracker[i][d];
                let pos_lb: IntVal = lb_tracker[i][d];
                let curr_size = self.box_size[o_idx][d];
                let size = self.box_size[i][d];
                let fr_lb = pos_ub - curr_size + 1;
                let fr_ub = pos_lb + size - 1;
                if fr_lb <= fr_ub {
                    fr.lb.push(fr_lb);
                    fr.ub.push(fr_ub);
                } else {
                    exists = false;
                }
            }
            assert!(all_fr.len() == fr_support.len());
            let mut regions_to_remove: Vec<(usize, usize)> = Vec::new();
            if exists && Self::overlaps(&lb_tracker[o_idx], &ub_tracker[o_idx], &fr, dimensions) {
                let mut c = 0;
                for f in &mut all_fr {
                    let fr_object = fr_support[c];
                    let v = Self::coalesce(f, &fr, self.dimensions);

                    match v {
                        // No overlap
                        0 => continue,
                        // fr is a subset of f
                        1 => {
                            //Do not add f vector of forbidden regions and do not track
                            exists = false;
                            break;
                        }
                        // f is a subset of fr
                        2 => {
                            // remove that forbidden region from all_fr and remove it from tracking
                            regions_to_remove.push((c, fr_object));
                        }
                        // they overlap whilst none is a subset of another
                        // we coalesce with
                        3 => {
                            exists = false;
                            break;
                        }
                        // The regions are equal TODO: Could we ignore one of them?
                        4 => {
                            break;
                        }
                        _ => panic!("should not be possible")
                    }
                    c = c + 1;
                }

                for (c, o) in regions_to_remove.iter().rev() {
                    assert!(fr_support[*c] == *o, "wrong fr support");
                    //println!("WOHOOO IGNORED WSHIT");
                    let _ = all_fr.remove(*c);
                    fr_support.retain(|&x| x != *o);
                }

                if exists {
                    fr_support.push(i);
                    all_fr.push(fr);
                }

            }
        }
        if all_fr.is_empty() { None } else { Some(all_fr) }
    }

    /// Checks whether the sweep point is in a feasible position, if it is not,
    /// return the forbidden region it collided with
    fn infeasible_sweep<'a>(
        sweep: &Vec<IntVal>,
        dimensions: usize,
        all_fr: &'a Vec<ForbiddenRegion>
    ) -> Option<&'a ForbiddenRegion> {
        all_fr.iter()
            .find(|fr|
                    (0..dimensions).all(|i| sweep[i] >= fr.lb[i] && sweep[i] <= fr.ub[i]))
    }

    fn fixed_in_all_dimensions(
        &self,
        ub_tracker: &Vec<Vec<IntVal>>,
        lb_tracker: &Vec<Vec<IntVal>>,
        curr_obj_idx: usize
        ) -> bool {
        let mut is_assigned = true;
        for d in 0..self.dimensions {
            let fixed = lb_tracker[curr_obj_idx][d] == ub_tracker[curr_obj_idx][d];
            if !fixed {
                is_assigned = false;
            }
        }
        is_assigned
    }

    // TODO: Very bad name
    fn find_smallest_lb(
        &self,
        ub_tracker: &Vec<Vec<IntVal>>,
        lb_tracker: &Vec<Vec<IntVal>>,
        curr_obj_idx: usize,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
        ) -> Option<IntVal> {
        let feasible_fr: Vec<_> = all_fr.into_iter()
            .filter(|fr| fr.lb[curr_dimension] < lb_tracker[curr_obj_idx][curr_dimension])
            .collect();


        for d in 0..self.dimensions {
            if d == curr_dimension { continue; }
            let posn_ub = ub_tracker[curr_obj_idx][d];
            let posn_lb = lb_tracker[curr_obj_idx][d];
            let mut range_list: Vec<_> = (posn_lb..=posn_ub).collect();

            for fr in &feasible_fr {
                let fr_range: Vec<_> = (fr.lb[d]..=fr.ub[d]).collect();
                range_list = range_list.into_iter()
                    .filter(|v| !fr_range.contains(v))
                    .collect();
                if range_list.is_empty() { break; }
            }
            if !range_list.is_empty() {
                return None;
            }
        }
        feasible_fr.iter()
            .map(|fr| fr.lb[curr_dimension])
            .max()
    }

    // TODO: Very bad name
    fn find_largest_ub(
        &self,
        ub_tracker: &Vec<Vec<IntVal>>,
        lb_tracker: &Vec<Vec<IntVal>>,
        curr_obj_idx: usize,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
        ) -> Option<IntVal> {
        let feasible_fr: Vec<_> = all_fr.into_iter()
            .filter(|fr| fr.ub[curr_dimension] > ub_tracker[curr_obj_idx][curr_dimension])
            .collect();


        for d in 0..self.dimensions {
            if d == curr_dimension { continue; }
            let posn_ub = ub_tracker[curr_obj_idx][d];
            let posn_lb = lb_tracker[curr_obj_idx][d];
            let mut range_list: Vec<_> = (posn_lb..=posn_ub).collect();

            for fr in &feasible_fr {
                let fr_range: Vec<_> = (fr.lb[d]..=fr.ub[d]).collect();
                range_list = range_list.into_iter()
                    .filter(|v| !fr_range.contains(v))
                    .collect();
                if range_list.is_empty() { break; }
            }
            if !range_list.is_empty() {
                return None;
            }
        }
        feasible_fr.iter()
            .map(|fr| fr.ub[curr_dimension])
            .min()
    }


    /// Checks if two forbidden regions can be coalesced into one
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
        dimensions:usize
    ) -> usize {
        let mut trend = 0;
        let mut e = 0;
        for d in 0..dimensions {
            // No overlapping possible
            if fr1.ub[d] + 1 < fr2.lb[d] || fr1.lb[d] > fr2.ub[d] + 1 {
                return 0;
            // The regions are equal
            } else if fr1.lb[d] == fr2.lb[d] && fr1.ub[d] == fr2.ub[d] {
                continue;
            // fr2 is a subset of fr1
            } else if fr1.lb[d] <= fr2.lb[d] && fr1.ub[d] >= fr2.ub[d] {
                match trend {
                    0 | 1 => trend = 1,
                    _ => return 0
                }
            // fr1 is a subset of fr2
            } else if fr1.lb[d] >= fr2.lb[d] && fr1.ub[d] <= fr2.ub[d] {
                match trend {
                    0 | 2 => trend = 2,
                    _ => return 0
            }
            // They overlap, but not such one is a subset of another
            // only allow this trend in one dimensions
            } else {
                e = d;
                match trend {
                    0 => trend = 3,
                    _ => return 0
                }
            }
        }

        match trend {
            0 => 4,
            1 => 1,
            2 => 2,
            3 => {
                // The regions looks something like:
                // +--------+----+-------+
                // |        |    |       |
                // |        |    |       |
                // +--------+----+-------+
                fr1.lb[e] = cmp::min(fr1.lb[e], fr2.lb[e]);
                fr1.ub[e] = cmp::max(fr1.ub[e], fr2.ub[e]);
                3
            },
            _ => 0
        }
    }

    fn disjoint(
        &self,
        bounding_box: &ForbiddenRegion,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        curr_obj_idx: usize,
        ) -> bool {
        for d in 0..self.dimensions {
            if ub_tracker[curr_obj_idx][d] + self.box_size[curr_obj_idx][d] - 1 < bounding_box.lb[d]
                || lb_tracker[curr_obj_idx][d] > bounding_box.ub[d]
                {
                    return true;
                }
        }
        false
    }


    /// Gives a reason for the conflict
    fn explain_conflict<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        curr_obj_idx: usize
    ) -> Vec<BoolView> {
        let mut reason: Vec<_> = self.explain_fr(actions, fr_support, lb_tracker, ub_tracker);
        for d in 0..self.dimensions {
            reason.push(
                actions.get_int_lit(self.box_posn[curr_obj_idx][d],
                                    IntLitMeaning::Less(ub_tracker[curr_obj_idx][d] + 1))
            );
            trace!(
                "Reason [[var {:?} [{:?}, {:?}] < {:?}]",
                curr_obj_idx,
                actions.get_int_lower_bound(self.box_posn[curr_obj_idx][d]),
                actions.get_int_upper_bound(self.box_posn[curr_obj_idx][d]),
                ub_tracker[curr_obj_idx][d] + 1
            );
            reason.push(
                actions.get_int_lit(self.box_posn[curr_obj_idx][d],
                                    IntLitMeaning::GreaterEq(lb_tracker[curr_obj_idx][d]))
            );
            trace!(
                "Reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                curr_obj_idx,
                actions.get_int_lower_bound(self.box_posn[curr_obj_idx][d]),
                actions.get_int_upper_bound(self.box_posn[curr_obj_idx][d]),
                lb_tracker[curr_obj_idx][d]
            );
        }
        reason
    }


    fn explain_fr<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>
    ) -> Vec<BoolView> {
        let mut reason = Vec::new();
        for &o_idx in fr_support {
            if actions.get_trailed_int(self.removed_objs) & (1 << o_idx) != 0 {
                continue;
            }
            // for o_idx in 0..self.box_posn.len() {
            for d in 0..self.dimensions {
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[o_idx][d],
                        IntLitMeaning::Less(ub_tracker[o_idx][d] + 1))
                );
                trace!(
                    "Reason [[var {:?} [{:?}, {:?}] < {:?}]",
                    o_idx,
                    lb_tracker[o_idx][d],
                    ub_tracker[o_idx][d],
                    ub_tracker[o_idx][d] + 1
                );
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[o_idx][d],
                        IntLitMeaning::GreaterEq(lb_tracker[o_idx][d]))
                );
                trace!(
                    "reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                    o_idx,
                    lb_tracker[o_idx][d],
                    ub_tracker[o_idx][d],
                    lb_tracker[o_idx][d]
                );
            }
        }
        reason
    }

    fn add_generalized_bound<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        all_fr: &Vec<ForbiddenRegion>,
        curr_dimension: usize,
        curr_obj_idx: usize,
        prune_upper: bool
    ) -> Option<Vec<BoolView>> {
        let mut reason = Vec::new();
        if prune_upper {
            if let Some(v) = self.find_largest_ub(ub_tracker, lb_tracker, curr_obj_idx, curr_dimension, all_fr) {
                trace!("GENERALIZED max from {:?} to {:?}",ub_tracker[curr_obj_idx][curr_dimension] + 1, v);
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][curr_dimension],
                        IntLitMeaning::Less(v + 1))
                );
                trace!(
                    "Reason [[var {:?} [{:?}, {:?}] < {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][curr_dimension],
                    ub_tracker[curr_obj_idx][curr_dimension],
                    v + 1
                );

                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][curr_dimension],
                        IntLitMeaning::GreaterEq(lb_tracker[curr_obj_idx][curr_dimension]))
                );

                trace!(
                    "Reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][curr_dimension],
                    ub_tracker[curr_obj_idx][curr_dimension],
                    lb_tracker[curr_obj_idx][curr_dimension]
                );
            } else {
                return None;
            }
        } else {
            if let Some(v) = self.find_smallest_lb(ub_tracker, lb_tracker, curr_obj_idx, curr_dimension, all_fr) {
                trace!("GENERALIZED min from {:?} to {:?}",lb_tracker[curr_obj_idx][curr_dimension], v);
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][curr_dimension],
                        IntLitMeaning::GreaterEq(v))
                );
                trace!(
                    "Reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][curr_dimension],
                    ub_tracker[curr_obj_idx][curr_dimension],
                    v
                );
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][curr_dimension],
                        IntLitMeaning::Less(ub_tracker[curr_obj_idx][curr_dimension] + 1))
                );
                trace!(
                    "Reason [[var {:?} [{:?}, {:?}] < {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][curr_dimension],
                    ub_tracker[curr_obj_idx][curr_dimension],
                    ub_tracker[curr_obj_idx][curr_dimension] + 1
                )
            } else {
                return None;
            }

        }
        Some(reason)
    }

    fn explain_propagation<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        all_fr: &Vec<ForbiddenRegion>,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        curr_dimension: usize,
        prune_upper: bool
    ) -> Vec<BoolView> {
        let mut reason: Vec<_> = self.explain_fr(actions, fr_support, lb_tracker, ub_tracker);
        for d in 0..self.dimensions {
            if d == curr_dimension {
                if let Some(r)
                    = self.add_generalized_bound(actions,
                                                 lb_tracker,
                                                 ub_tracker,
                                                 all_fr,
                                                 curr_dimension,
                                                 curr_obj_idx,
                                                 prune_upper)
                    {
                    reason.extend(r);
                } else {
                    reason.push(
                        actions.get_int_lit(
                            self.box_posn[curr_obj_idx][d],
                            IntLitMeaning::Less(ub_tracker[curr_obj_idx][d] + 1))
                    );
                    trace!(
                        "Reason [[var {:?} [{:?}, {:?}] < {:?}]",
                        curr_obj_idx,
                        lb_tracker[curr_obj_idx][d],
                        ub_tracker[curr_obj_idx][d],
                        ub_tracker[curr_obj_idx][d] + 1
                    );

                    reason.push(
                        actions.get_int_lit(
                            self.box_posn[curr_obj_idx][d],
                            IntLitMeaning::GreaterEq(lb_tracker[curr_obj_idx][d]))
                    );
                    trace!(
                        "Reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                        curr_obj_idx,
                        lb_tracker[curr_obj_idx][d],
                        ub_tracker[curr_obj_idx][d],
                        lb_tracker[curr_obj_idx][d]
                    );
                }
            } else {
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][d],
                        IntLitMeaning::Less(ub_tracker[curr_obj_idx][d] + 1))
                );
                trace!(
                    "reason [[var {:?} [{:?}, {:?}] < {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][d],
                    ub_tracker[curr_obj_idx][d],
                    ub_tracker[curr_obj_idx][d] + 1
                );
                reason.push(
                    actions.get_int_lit(
                        self.box_posn[curr_obj_idx][d],
                        IntLitMeaning::GreaterEq(lb_tracker[curr_obj_idx][d]))
                );
                trace!(
                    "reason [[var {:?} [{:?}, {:?}] >= {:?}]",
                    curr_obj_idx,
                    lb_tracker[curr_obj_idx][d],
                    ub_tracker[curr_obj_idx][d],
                    lb_tracker[curr_obj_idx][d]
                );
            }
        }
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
        trace!("new propagation");
        let mut lb_tracker: Vec<Vec<IntVal>> = self.box_posn.iter()
            .map(|row|
                 row.iter()
                 .map(|&v| actions.get_int_lower_bound(v))
                 .collect())
            .collect();
        let mut ub_tracker: Vec<Vec<IntVal>> = self.box_posn.iter()
            .map(|row|
                 row.iter()
                 .map(|&v| actions.get_int_upper_bound(v))
                 .collect())
            .collect();

        // let mut internal_b = ForbiddenRegion {
        //     lb: Vec::new(),
        //     ub: Vec::new()
        // };

        // for i in 0..self.dimensions {
        //     internal_b.lb.push(actions.get_trailed_int(self.bounded_box.lb[i]));
        //     internal_b.ub.push(actions.get_trailed_int(self.bounded_box.ub[i]));

        //     let _ = actions.set_trailed_int(self.bounded_box.lb[i], i64::MAX);
        //     let _ = actions.set_trailed_int(self.bounded_box.ub[i], i64::MIN);
        // }

        for o_idx in 0..self.box_posn.len() {
            if actions.get_trailed_int(self.fixed) & (1 << o_idx) != 0 {
                continue;
            }

            // TODO: add so that external events are also considered and affects
            // the bounding box
            // if self.disjoint(&internal_b, &lb_tracker, &ub_tracker, o_idx) {
            //     continue;
            // }

            trace!("DOING OBJECT {:?}", o_idx);
            // for o in 0..self.box_posn.len() {
            //     trace!("object {:?}: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?}, size {}",
            //          o,
            //          ub_tracker[o][0],
            //          lb_tracker[o][0],
            //          ub_tracker[o][1],
            //          lb_tracker[o][1],
            //          self.box_size[o][0]
            //     );
            // }
            let mut fr_support: Vec<usize> = Vec::new();

            if let Some(all_fr) = self.generate_fr::<P>(actions, &mut fr_support, o_idx, &lb_tracker, &ub_tracker, self.dimensions) {
                // for f in 0..all_fr.len() {
                //     trace!("FORBIDDEN REGION: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?} ",
                //              all_fr[f].ub[0],
                //              all_fr[f].lb[0],
                //              all_fr[f].ub[1],
                //              all_fr[f].lb[1],
                //     );
                // }

                if self.fixed_in_all_dimensions(&ub_tracker, &lb_tracker, o_idx) {
                    let reason = self.explain_conflict(actions,
                                                       &fr_support,
                                                       &lb_tracker,
                                                       &ub_tracker,
                                                       o_idx);
                    // trace!("CONFLICT assigned {:?}", reason.len());
                    return Err(Conflict::new(actions, None, reason));
                }
                let mut all_fixed = true;
                for d in 0..self.dimensions {
                    let fixed = lb_tracker[o_idx][d] == ub_tracker[o_idx][d];
                    let (b1, c1) = self.prune_min(actions,
                                            &fr_support,
                                            o_idx,
                                            &mut lb_tracker,
                                            &ub_tracker,
                                            d,
                                            &all_fr)?;
                    if !fixed && !b1 {
                        // Conflict since there is no feasible origin in this dimension
                        let reason = self.explain_conflict(actions,
                                                           &fr_support,
                                                           &lb_tracker,
                                                           &ub_tracker,
                                                           o_idx);

                        // trace!("CONFLICT assigned min {}", reason.len());

                        return Err(Conflict::new(actions, None, reason));
                    }

                    let fixed = lb_tracker[o_idx][d] == ub_tracker[o_idx][d];
                    let (b2, c2) = self.prune_max(actions,
                                            &fr_support,
                                            o_idx,
                                            &lb_tracker,
                                            &mut ub_tracker,
                                            d,
                                            &all_fr)?;
                    if !fixed && !b2 {
                        // Conflict since there is no feasible origin in this dimension
                        let reason = self.explain_conflict(actions,
                                                           &fr_support,
                                                           &lb_tracker,
                                                           &ub_tracker,
                                                           o_idx);
                        // trace!("CONFLICT assigned max");
                        // trace!("CONFLICT prune_max");
                        return Err(Conflict::new(actions, None, reason));
                    }
                    if !fixed {
                        all_fixed = false;
                    }

                    if c1 || c2 {
                    //    for i in 0..self.dimensions {
                    //        let _ = actions.set_trailed_int(self.bounded_box.lb[i],
                    //                                        cmp::min(actions.get_trailed_int(self.bounded_box.lb[i]),
                    //                                        lb_tracker[o_idx][i]));
                    //        let _ = actions.set_trailed_int(self.bounded_box.ub[i],
                    //                                        cmp::max(actions.get_trailed_int(self.bounded_box.ub[i]),
                    //                                        ub_tracker[o_idx][i]) + self.box_size[o_idx][i] - 1);
                    //    }
                    }

                }
                if all_fixed {
                    let fix_o_idx = actions.get_trailed_int(self.fixed) + (1 << o_idx);
                    let _ = actions.set_trailed_int(self.fixed, fix_o_idx);
                }
            }
        }

        let mut active_b = ForbiddenRegion {
            lb: Vec::new(),
            ub: Vec::new()
        };

        for i in 0..self.dimensions {
            active_b.lb.push(actions.get_trailed_int(self.bounded_box.lb[i]));
            active_b.ub.push(actions.get_trailed_int(self.bounded_box.ub[i]));

            // let _ = actions.set_trailed_int(self.bounded_box.lb[i], i64::MAX);
            // let _ = actions.set_trailed_int(self.bounded_box.ub[i], i64::MIN);
        }

        for o_idx in 0..self.box_posn.len() {
            if actions.get_trailed_int(self.fixed) & (1 << o_idx) != 0 {
                continue;
            }
            for i in 0..self.dimensions {
                active_b.lb[i] = cmp::min(active_b.lb[i], lb_tracker[o_idx][i]);
                active_b.ub[i] = cmp::max(active_b.ub[i], ub_tracker[o_idx][i] + self.box_size[o_idx][i] - 1);
            }

        }

        for o_idx in 0..self.box_posn.len() {
            if actions.get_trailed_int(self.fixed) & (1 << o_idx) != 0 &&
                self.disjoint(&active_b, &lb_tracker, &ub_tracker, o_idx)
            {
                let rmv_o_idx = actions.get_trailed_int(self.removed_objs) + (1 << o_idx);
                let _ = actions.set_trailed_int(self.fixed, rmv_o_idx);
            }
        }
        for i in 0..self.dimensions {
            let _ = actions.set_trailed_int(self.bounded_box.lb[i], i64::MAX);
            let _ = actions.set_trailed_int(self.bounded_box.ub[i], i64::MIN);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;
	use itertools::Itertools;

	use crate::{diffn_int, reformulate::InitConfig, Decision, Model};
	use crate::{
		constraints::int_diffn::IntDiffnSweep,
		solver::{
			int_var::{EncodingType, IntVar},
			Solver,
		},
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


		IntDiffnSweep::new_in(&mut slv, vec![vec![pos_1, pos_2], vec![pos_3, pos_4]], vec![vec![size_1, size_2], vec![size_3, size_4]], false);

		slv.assert_all_solutions(&[pos_2, pos_4], |sol| sol.iter().all_unique());
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
            vec![x_pos_4, y_pos_4]
        ],
        vec![
            vec![x_size_1, y_size_1],
            vec![x_size_2, y_size_2],
            vec![x_size_3, y_size_3],
            vec![x_size_4, y_size_4]
        ],
        false
        );
		let (mut slv, map) = prb.to_solver::<PropagatingCadical<_>>(&InitConfig::default()).unwrap();
		let pos_vars = vec![
                vec![x_pos_1, y_pos_1],
                vec![x_pos_2, y_pos_2],
                vec![x_pos_3, y_pos_3],
                vec![x_pos_4, y_pos_4]]
            .into_iter()
            .flatten()
            .map(|x| map.get(&mut slv, &Decision::from(x)))
            .collect_vec();

	    let (solve_result, value) = slv.get_all_solutions(&pos_vars);
        println!("solve_result {:?}, value {:?}",solve_result, value);
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
            false
        );
        let (mut slv, map) = prb.to_solver::<PropagatingCadical<_>>(&InitConfig::default()).unwrap();
        let pos_vars = vec![
            vec![x_pos_1, y_pos_1],
            vec![x_pos_2, y_pos_2],
            vec![x_pos_3, y_pos_3]]
            .into_iter()
            .flatten()
            .map(|x| map.get(&mut slv, &Decision::from(x)))
            .collect_vec();

        let (solve_result, value) = slv.get_all_solutions(&pos_vars);
        println!("solve_result {:?}, value {:?}",solve_result, value);
    }
}
