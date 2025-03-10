use itertools::izip;
use std::cmp; use crate::{actions::{
	ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
}, constraints::{Conflict, Constraint, PropagationActions, Propagator, SimplificationStatus}, reformulate::ReformulationError, solver::{
	activation_list::IntPropCond, queue::PriorityLevel, IntLitMeaning, IntView, IntViewInner,
}, IntDecision, IntVal};


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `diffn_int` constraint within a model.
///
/// This constraint enforces that all k-dimensional rectangles does no overlap
/// given their starting position `box_posn` and their sizes `box_sizes`.
pub struct IntDiffn {
    pub(crate) box_posn: Vec<Vec<IntDecision>>,
    pub(crate) box_size: Vec<Vec<IntDecision>>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Sweep based propagator for the `diffn_int` constraint.
pub struct IntDiffnSweep {
    box_posn: Vec<Vec<IntView>>,
    box_size: Vec<Vec<IntVal>>,
    dimensions: usize
}

impl<S: SimplificationActions> Constraint<S> for IntDiffn {
	fn simplify(&mut self, _actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
		Ok(SimplificationStatus::Fixpoint)
	}

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
        IntDiffnSweep::new_in(slv, box_pos, box_size);
        Ok(())
	}
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
// Active forbidden regions
struct ForbiddenRegion {
	lb: Vec<IntVal>, // lower bound of each dimension
	ub: Vec<IntVal>  // upper bound of each dimension
}


impl IntDiffnSweep {
	/// Prepare a new [`IntDiffnSweep`] propagator to be posted to the
	/// solver.
	pub fn new_in<P: PropagatorInitActions + ?Sized>
        (solver: &mut P,
        box_posn: Vec<Vec<IntView>>,
        box_size: Vec<Vec<IntView>>) {

        // Make sure all sizes are fixed before enqueueing
		let enqueue = box_size
			.iter()
            .flatten()
			.all(|v| matches!(v, IntView(IntViewInner::Const(_))));

        if !enqueue { return () } // don't propagate if not all sizes are fixed

        let box_size_fixed: Vec<Vec<IntVal>> = box_size.iter()
             .map(|row|
                  row.iter()
                     .map(|&v| solver.get_int_lower_bound(v))
                     .collect()
             )
             .collect();

		let prop = solver.add_propagator(Box::new(Self {
            box_posn: box_posn.clone(),
            box_size: box_size_fixed,
            dimensions: box_posn[0].len()
        }), PriorityLevel::Low);

        for v in box_posn.into_iter().flatten() {
            solver.enqueue_on_int_change(prop, v, IntPropCond::Bounds);
        }
    }

    fn prune_min<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    ) -> Result<(), Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for i in 0..self.dimensions {
            sweep.push(actions.get_int_lower_bound(self.box_posn[curr_obj_idx][i]));
            jump.push(actions.get_int_upper_bound(self.box_posn[curr_obj_idx][i]) + 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        while b && infeasible_fr.is_some() {
            println!("prune_min - in loop");
            jump[curr_dimension] = cmp::min(jump[curr_dimension], infeasible_fr.unwrap().ub[curr_dimension] + 1);
            // Contains side-effects to change sweep
            b = Self::adjust_sweep_min(actions, &mut sweep, &mut jump, &self.box_posn[curr_obj_idx], curr_dimension, self.dimensions);
            infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        }

        // Start pruning here
        if b {
            // Creating explanation clauses
            let mut reason = Vec::new();

            for o_idx in 0..self.box_posn.len() {
                // There is no fr for jndex o_idx
                if fr_support[o_idx] == 0 { continue }
                if all_fr[o_idx].ub[curr_dimension] == sweep[curr_dimension] {
                    // Explains that the objects ub is such that it doesnt exceed the sweep
                    // let r = sweep[curr_dimension] - self.box_size[curr_obj_idx][curr_dimension] + 1;
                    // reason.push(actions.get_int_lit(self.box_posn[o_idx][curr_dimension], IntLitMeaning::Less(r+1)));
                    //
                    // Not convinced this is correct since if we would enfore fr.ub[x] <= 3 on both
                    // we are not constraining them to be less than 3 and if we are also setting fr.ub[x] == 3 then the
                    // explanation might be invalid since one of them would be allowed to be > 3
                    // +----------------+
                    // |    |           |
                    // | 1  |           |
                    // +----+           |
                    // |    |           |
                    // | 2  |           |
                    // |    |           |
                    // +----------------+
                    //      3
                    reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][curr_dimension]))

                } else {
                    // Explain that in the other dimensions where we are exceeding the point where
                    // we are sweeping, there is some space such that the current object could
                    // still be place
                    let valid_objs = (0..self.box_posn.len()).filter(|i| all_fr[o_idx].ub[curr_dimension] <= sweep[curr_dimension]).collect();
                    for d in 0..self.dimensions {
                        // We don't have to look at our current dimension
                        if d == curr_dimension { continue }

                        // +----+-----------+
                        // |    |           |
                        // |    |    2      |
                        // |    +-----------+
                        // | 1  |           |
                        // |    |           |
                        // |    |           |
                        // +----+-----------+
                        //
                        if all_fr[o_idx].ub[d] > actions.get_int_upper_bound(self.box_posn[curr_obj_idx][d]) {
                             let p =  self.find_lowest_point(actions, curr_dimension, curr_obj_idx, &valid_objs);
                        }
                        // +----+-----------+
                        // |    |           |
                        // |    |           |
                        // |    |           |
                        // | 1  +-----------+
                        // |    |    2      |
                        // |    |           |
                        // +----+-----------+
                        else if all_fr[o_idx].lb[d] < actions.get_int_lower_bound(self.box_posn[curr_obj_idx][d]) {
                             let p =  self.find_highest_point(actions, curr_dimension, curr_obj_idx, &valid_objs);
                        }

                    }
                }
            }
            actions.set_int_upper_bound(self.box_posn[curr_obj_idx][curr_dimension], sweep[curr_dimension], reason)?;

        }
        Ok(())
    }

    fn prune_max<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    ) -> Result<(), Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for i in 0..self.dimensions {
            sweep.push(actions.get_int_upper_bound(self.box_posn[curr_obj_idx][i]));
            jump.push(actions.get_int_lower_bound(self.box_posn[curr_obj_idx][i]) - 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        while b && infeasible_fr.is_some() {
            //println!("prune max - in loop");
            jump[curr_dimension] = cmp::max(jump[curr_dimension], infeasible_fr.unwrap().lb[curr_dimension] - 1);
            // println!("sweep before x: {:?} y: {:?}", sweep[0], sweep[1]);
            // println!("jump before x: {:?} y: {:?}", jump[0], jump[1]);
            // Contains side-effects to change sweep
            b = Self::adjust_sweep_max(actions, &mut sweep, &mut jump, &self.box_posn[curr_obj_idx], curr_dimension, self.dimensions);
            // println!("sweep after x: {:?} y: {:?}", sweep[0], sweep[1]);
            // println!("jump after x: {:?} y: {:?}", jump[0], jump[1]);
            infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        }


        if b {
            //println!("SWEEP IS x: {:?} y: {:?}", sweep[0], sweep[1]);
            if curr_dimension == 1 {
                println!("CURRENT SWEEP IS {:?} in dimension {:?} for object {:?}", sweep[curr_dimension], curr_dimension, curr_obj_idx);
                let reason = actions.get_int_lit(self.box_posn[1][curr_dimension], IntLitMeaning::GreaterEq(4));
                actions.set_int_upper_bound(self.box_posn[curr_obj_idx][curr_dimension], sweep[curr_dimension], reason)?;
                println!("PRUNING DONE");
            }

        }
        Ok(())
    }

    fn find_highest_point<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        curr_dimension: usize,
        curr_obj_idx: usize,
        valid_objs: &Vec<usize>
    ) -> IntVal {
        for o in valid_objs {

        }
    }

    fn find_lowest_point<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        curr_dimension: usize,
        curr_obj_idx: usize,
        valid_objs: &Vec<usize>
    ) -> IntVal {
        for o in valid_objs {

        }
    }

    fn adjust_sweep_min<P: PropagationActions>(
        actions: &mut P,
        sweep: &mut Vec<IntVal>,
        jump: &mut Vec<IntVal>,
        curr_obj_pos: &Vec<IntView>,
        curr_dimension: usize,
        dimensions: usize
    ) -> bool {
        for i in (0..dimensions).rev() {
            let rotation = (i + curr_dimension) % dimensions;
            sweep[rotation] = jump[rotation];
            jump[rotation] = actions.get_int_upper_bound(curr_obj_pos[rotation]) + 1;
            if sweep[rotation] <= actions.get_int_upper_bound(curr_obj_pos[rotation]) {
                return true;
            } else {
                // Reset sweep-point
                sweep[rotation] = actions.get_int_lower_bound(curr_obj_pos[rotation]);
            }
        }
        false
    }

    fn adjust_sweep_max<P: PropagationActions>(
        actions: &mut P,
        sweep: &mut Vec<IntVal>,
        jump: &mut Vec<IntVal>,
        curr_obj_pos: &Vec<IntView>,
        curr_dimension: usize,
        dimensions: usize
    ) -> bool {
        for i in (0..dimensions).rev() {
            let rotation = (i + curr_dimension) % dimensions;
            // println!("sweep before x: {:?} y: {:?}", sweep[0], sweep[1]);
            // println!("jump before x: {:?} y: {:?}", jump[0], jump[1]);
            sweep[rotation] = jump[rotation];
            jump[rotation] = actions.get_int_lower_bound(curr_obj_pos[rotation]) - 1;
            //println!("sweep after x: {:?} y: {:?}", sweep[0], sweep[1]);
            //println!("jump after x: {:?} y: {:?}", jump[0], jump[1]);
            // Current sweep-point is withing the bounds of the current object
            if sweep[rotation] >= actions.get_int_lower_bound(curr_obj_pos[rotation]) {
                return true
            } else {
                // Reset sweep-point
                sweep[rotation] = actions.get_int_upper_bound(curr_obj_pos[rotation]);
                //println!("sweep ADD x: {:?} y: {:?}", sweep[0], sweep[1]);
            }
        }
        false
    }



    fn overlaps<P: PropagationActions>(
        actions: &mut P,
        curr_obj_pos: &Vec<IntView>,
        fr: &ForbiddenRegion,
        dimensions:usize
    ) -> bool {
        println!("size: {:?}", fr.lb.len());
        // !(0..dimensions).any(|d|
        //                actions.get_int_upper_bound(curr_obj_pos[d]) < fr.lb[d] ||
        //                actions.get_int_lower_bound(curr_obj_pos[d]) > fr.ub[d])
        for d in 0..dimensions {
            let a = actions.get_int_upper_bound(curr_obj_pos[d]) < fr.lb[d];
            let b = actions.get_int_lower_bound(curr_obj_pos[d]) > fr.ub[d];
            if a || b {
                return false;
            }
        }
        true
    }




    /// Generates forbidden regions given object o
    fn generate_fr<P: PropagationActions>(
        &self,
        actions: &mut P,
        fr_support: &mut Vec<usize>,
        o_idx:usize,
        dimensions:usize
    ) -> Option<Vec<ForbiddenRegion>> {
        let mut all_fr:Vec<ForbiddenRegion> = vec![];
        let no_objects = self.box_posn.len();
        let curr_obj_size = &self.box_size[o_idx];
        for i in 0..no_objects {
            let mut fr = ForbiddenRegion {
                lb: Vec::new(),
                ub: Vec::new()
            };

            if i == o_idx { continue };
            let obj_pos = &self.box_posn[i];
            let obj_size = &self.box_size[i];

            for (&pos, size, curr_size) in izip!(obj_pos, obj_size, curr_obj_size) {
                let pos_ub: IntVal = actions.get_int_upper_bound(pos);
                let pos_lb: IntVal = actions.get_int_lower_bound(pos);

                let fr_lb = pos_ub - curr_size + 1;
                let fr_ub = pos_lb + size - 1;
                if fr_lb <= fr_ub {
                    fr.lb.push(fr_lb);
                    fr.ub.push(fr_ub);
                } else {
                    fr_support.push(0);
                    break;
                }
            }
            if fr.lb.len() == dimensions {
                let is_overlapping = Self::overlaps::<P>(
                    actions,
                    &self.box_posn[o_idx],
                    &fr,
                    dimensions);

                if is_overlapping{
                    fr_support.push(1);
                    all_fr.push(fr);
                } else {
                    fr_support.push(0);
                }

            }
        }
        if all_fr.is_empty() { None } else { Some(all_fr) }
    }

    // Checks whether the sweep point is in a feasible position, if it is feas
    fn infeasible_sweep<'a>(
        sweep: &Vec<IntVal>,
        dimensions: usize,
        all_fr: &'a Vec<ForbiddenRegion>
    ) -> Option<&'a ForbiddenRegion> {
    //     all_fr.iter()
    //         .find(|fr|
    //                 (0..dimensions).all(|i| sweep[i] >= fr.lb[i] && sweep[i] <= fr.ub[i]))
    // }
        for fr in all_fr {
            if !Self::isfeasible(sweep, dimensions, fr) {
                return Some(fr)
            }
        }
        None
    }

    fn isfeasible(
        sweep: &Vec<IntVal>,
        dimensions: usize,
        fr: &ForbiddenRegion
    ) -> bool {
        for i in 0..dimensions {
            if sweep[i] < fr.lb[i] || sweep[i] > fr.ub[i] { return true; }
        }
        false
    }
}


impl<P, E> Propagator<P, E> for IntDiffnSweep
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        for o_idx in 0..self.box_posn.len() {
            // Check whether there exists any forbidden regions
            println!("object {:?}: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?} ",
                     0,
                     actions.get_int_upper_bound(self.box_posn[0][0]),
                     actions.get_int_lower_bound(self.box_posn[0][0]),
                     actions.get_int_upper_bound(self.box_posn[0][1]),
                     actions.get_int_lower_bound(self.box_posn[0][1]),
            );

            println!("object {:?}: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?} ",
                     1,
                     actions.get_int_upper_bound(self.box_posn[1][0]),
                     actions.get_int_lower_bound(self.box_posn[1][0]),
                     actions.get_int_upper_bound(self.box_posn[1][1]),
                     actions.get_int_lower_bound(self.box_posn[1][1]),
            );
            let mut fr_support: Vec<usize> = Vec::new();
            if let Some(all_fr) = self.generate_fr(actions, &mut fr_support, o_idx, self.dimensions) {
                println!("FORBIDDEN REGION: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?} ",
                         all_fr[0].ub[0],
                         all_fr[0].lb[0],
                         all_fr[0].ub[1],
                         all_fr[0].lb[1],
                );
                for d in 0..self.dimensions {
                    self.prune_min(actions, &fr_support, o_idx, d, &all_fr)?;
                    self.prune_max(actions, &fr_support, o_idx, d, &all_fr)?;

                }
            }
        }
        Ok(())
	}
}

#[cfg(test)]
mod tests {
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;
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


		IntDiffnSweep::new_in(&mut slv, vec![vec![pos_1, pos_2], vec![pos_3, pos_4]], vec![vec![size_1, size_2], vec![size_3, size_4]] );

        slv.assert_unsatisfiable();
    }
}
