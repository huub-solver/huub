//! Structure and algorithms for the integer diffn constraint, which
//! enforces that a number of k-dimensional hyperrectangles do not overlap.

use itertools::izip;
use std::cmp; use crate::{actions::{
    ExplanationActions, PropagatorInitActions, ReformulationActions, SimplificationActions,
},  constraints::{Conflict, Constraint, PropagationActions, Propagator},
    reformulate::ReformulationError, solver::{
	activation_list::IntPropCond, queue::PriorityLevel, IntView, IntViewInner,
},  IntDecision, IntVal};

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
    dimensions: usize,
}

impl<S: SimplificationActions> Constraint<S> for IntDiffn {
    // TODO: Add good simplifications
	// fn simplify(&mut self, _actions: &mut S) -> Result<SimplificationStatus, ReformulationError> {
	// 	let fixed = self.box_posn
	// 		.iter()
    //         .flatten()
	// 		.all(|&v| matches!(v, IntDecision(IntDecisionInner::Const(_))));
    //     if fixed {
    //         Ok(SimplificationStatus::Subsumed)
    //     } else {
    //     }
    //     Ok(SimplificationStatus::Fixpoint)
	// }

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
            dimensions: box_posn[0].len(),
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
        lb_tracker: &mut Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    ) -> Result<bool, Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for d in 0..self.dimensions {
            sweep.push(lb_tracker[curr_obj_idx][d]);
            jump.push(ub_tracker[curr_obj_idx][d] + 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        while b && infeasible_fr.is_some() {
            for j in 0..self.dimensions {
                jump[j] = cmp::min(jump[j], infeasible_fr.unwrap().ub[j] + 1);
            }
            // println!("prune_min - in loop");
            // Contains side-effects to change sweep
            b = Self::adjust_sweep_min::<P>(&mut sweep, &mut jump, &lb_tracker[curr_obj_idx], &ub_tracker[curr_obj_idx], curr_dimension, self.dimensions);
            infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        }
        println!("sweep: x {} y {}", sweep[0], sweep[1]);

        // Start pruning here
        // TODO: Remove this b to so we dont have to reason for conflict in propagate
        if b && sweep[curr_dimension] != lb_tracker[curr_obj_idx][curr_dimension]{
            let mut reason = Vec::new();
            for &o_idx in fr_support {
                for d in 0..self.dimensions {
                    reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][d]));
                    reason.push(actions.get_int_lower_bound_lit(self.box_posn[o_idx][d]));

                }
            }
            for d in (0..self.dimensions).filter(|&x| x == curr_dimension) {
                reason.push(actions.get_int_upper_bound_lit(self.box_posn[curr_obj_idx][d]));
                reason.push(actions.get_int_lower_bound_lit(self.box_posn[curr_obj_idx][d]));
            }
            actions.set_int_lower_bound(self.box_posn[curr_obj_idx][curr_dimension], sweep[curr_dimension], reason)?;
            lb_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
            println!("Setting min of object {} to {:?} in dimension {} in min",curr_obj_idx, sweep[curr_dimension], curr_dimension);
        }
        Ok(b)
    }

    fn prune_max<P: PropagationActions>(
        &mut self,
        actions: &mut P,
        fr_support: &Vec<usize>,
        curr_obj_idx: usize,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &mut Vec<Vec<IntVal>>,
        curr_dimension: usize,
        all_fr: &Vec<ForbiddenRegion>
    ) -> Result<bool, Conflict> {
        let mut sweep = vec![];
        let mut jump = vec![];
        let mut b = true;

        for i in 0..self.dimensions {
            sweep.push(ub_tracker[curr_obj_idx][i]);
            jump.push(lb_tracker[curr_obj_idx][i] - 1);
        }
        let mut infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
        while b && infeasible_fr.is_some() {
            // println!("prune max - in loop");
            for j in 0..self.dimensions {
                jump[j] = cmp::max(jump[j], infeasible_fr.unwrap().lb[j] - 1);
            }
            // println!("jump before x: {:?} y: {:?}", jump[0], jump[1]);
            // Contains side-effects to change sweep
            println!("sweep before x: {:?} y: {:?}", sweep[0], sweep[1]);
            b = Self::adjust_sweep_max::<P>(&mut sweep, &mut jump, &lb_tracker[curr_obj_idx], &ub_tracker[curr_obj_idx], curr_dimension, self.dimensions);
            println!("sweep after x: {:?} y: {:?}", sweep[0], sweep[1]);
            // println!("jump after x: {:?} y: {:?}", jump[0], jump[1]);
            infeasible_fr = Self::infeasible_sweep(&sweep, self.dimensions, all_fr);
            // println!("sweep: {:?} y: {:?}", sweep[0], sweep[1]);
        }
        println!("sweep: x {:?} y: {:?}", sweep[0], sweep[1]);

        // TODO: Remove this b to so we dont have to reason for conflict in propagate
        if b && sweep[curr_dimension] != ub_tracker[curr_obj_idx][curr_dimension]{
            let mut reason = Vec::new();
            for &o_idx in fr_support {
                for d in 0..self.dimensions {
                    reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][d]));
                    reason.push(actions.get_int_lower_bound_lit(self.box_posn[o_idx][d]));

                }
            }
            for d in (0..self.dimensions).filter(|&x| x == curr_dimension) {
                reason.push(actions.get_int_upper_bound_lit(self.box_posn[curr_obj_idx][d]));
                reason.push(actions.get_int_lower_bound_lit(self.box_posn[curr_obj_idx][d]));
            }
            actions.set_int_upper_bound(self.box_posn[curr_obj_idx][curr_dimension], sweep[curr_dimension], reason)?;
            ub_tracker[curr_obj_idx][curr_dimension] = sweep[curr_dimension];
            println!("Setting ub of object {} to {:?} in dimension {} in max",curr_obj_idx, sweep[curr_dimension], curr_dimension);
        }
        Ok(b)
    }

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
            println!("sweep: x {:?} y: {:?} in rotation {}", sweep[0], sweep[1], rotation);
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



    fn overlaps<P: PropagationActions>(
        curr_obj_lb: &Vec<IntVal>,
        curr_obj_ub: &Vec<IntVal>,
        fr: &ForbiddenRegion,
        dimensions:usize
    ) -> bool {
        // println!("size: {:?}", fr.lb.len());
        // (0..dimensions).all(|d|
        //                actions.get_int_upper_bound(curr_obj_pos[d]) >= fr.lb[d] &&
        //                actions.get_int_lower_bound(curr_obj_pos[d]) <= fr.ub[d])
        for d in 0..dimensions {
            //TODO: Change to better names or use iterators
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
        fr_support: &mut Vec<usize>,
        o_idx:usize,
        lb_tracker: &Vec<Vec<IntVal>>,
        ub_tracker: &Vec<Vec<IntVal>>,
        dimensions:usize
    ) -> Option<Vec<ForbiddenRegion>> {
        let mut all_fr:Vec<ForbiddenRegion> = vec![];
        let no_objects = self.box_posn.len();
        for i in 0..no_objects {
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
            if exists {
                let is_overlapping = Self::overlaps::<P>(
                    &lb_tracker[o_idx],
                    &ub_tracker[o_idx],
                    &fr,
                    dimensions);

                if is_overlapping{
                    fr_support.push(i);
                    println!("Valid fr for {}", i);
                    all_fr.push(fr);
                } else {
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
}


impl<P, E> Propagator<P, E> for IntDiffnSweep
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        // TODO: Create a tracker which tracks all lower bounds and upper bounds aswell as
        // commiting changes to them!!!!
        let mut lb_tracker: Vec<Vec<IntVal>> = self.box_posn.iter()
            .map(|row|
                 row.iter()
                 .map(|&v| actions.get_int_lower_bound(v))
                 .collect()).collect();
        let mut ub_tracker: Vec<Vec<IntVal>> = self.box_posn.iter()
            .map(|row|
                 row.iter()
                 .map(|&v| actions.get_int_upper_bound(v))
                 .collect()).collect();

        for o_idx in 0..self.box_posn.len() {
            println!("DOING OBJECT {:?}", o_idx);
            for o in 0..self.box_posn.len() {
                println!("object {:?}: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?}, size {}",
                     o,
                     ub_tracker[o][0],
                     lb_tracker[o][0],
                     ub_tracker[o][1],
                     lb_tracker[o][1],
                     self.box_size[o][0]
                );
            }

            let mut fr_support: Vec<usize> = Vec::new();

            if let Some(all_fr) = self.generate_fr::<P>(
                &mut fr_support,
                o_idx,
                &lb_tracker,
                &ub_tracker,
                self.dimensions) {
                for f in 0..all_fr.len() {
                    println!("FORBIDDEN REGION: x - ub: {:?} lb: {:?} y - ub: {:?}, lb: {:?} ",
                             all_fr[f].ub[0],
                             all_fr[f].lb[0],
                             all_fr[f].ub[1],
                             all_fr[f].lb[1],
                    );
                }

                let mut assigned = true;
                for d in 0..self.dimensions {
                    let fixed = actions.get_int_val(self.box_posn[o_idx][d]);
                    if fixed.is_none() {
                        assigned = false;
                    }
                }
                if assigned {
                    let mut reason: Vec<_> = Vec::new();
                    for i in fr_support {
                        for d in 0..self.dimensions {
                            reason.push(actions.get_int_upper_bound_lit(self.box_posn[i][d]));
                            reason.push(actions.get_int_lower_bound_lit(self.box_posn[i][d]));
                        }
                    }
                    for d in 0..self.dimensions {
                        reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][d]));
                        reason.push(actions.get_int_lower_bound_lit(self.box_posn[o_idx][d]));
                    }
                    return Err(Conflict::new(actions, None, reason));
                }

                for d in 0..self.dimensions {
                    let fixed = lb_tracker[o_idx][d] == ub_tracker[o_idx][d];
                    println!("fixed? {:?} dimension {}", fixed, d);

                    let b1 = self.prune_min(
                        actions,
                        &fr_support,
                        o_idx,
                        &mut lb_tracker,
                        &ub_tracker,
                        d,
                        &all_fr)?;

                    println!("b1? {:?}", b1);
                    if !fixed && !b1 {
                        let mut reason: Vec<_> = Vec::new();
                        for &i in &fr_support {
                            for di in 0..self.dimensions {
                                reason.push(actions.get_int_upper_bound_lit(self.box_posn[i][di]));
                                reason.push(actions.get_int_lower_bound_lit(self.box_posn[i][di]));
                            }
                        }
                        for di in 0..self.dimensions {
                            reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][di]));
                            reason.push(actions.get_int_lower_bound_lit(self.box_posn[o_idx][di]));
                        }
                        println!("CONFLICT in prune_min");
                        return Err(Conflict::new(actions, None, reason));
                    }
                    let fixed = lb_tracker[o_idx][d] == ub_tracker[o_idx][d];

                    let b2 = self.prune_max(
                        actions,
                        &fr_support,
                        o_idx,
                        &lb_tracker,
                        &mut ub_tracker,
                        d,
                        &all_fr)?;


                    println!("b2? {:?}", b2);
                    if !fixed && !b2 {
                        let mut reason: Vec<_> = Vec::new();
                        for i in fr_support {
                            for di in 0..self.dimensions {
                                reason.push(actions.get_int_upper_bound_lit(self.box_posn[i][di]));
                                reason.push(actions.get_int_lower_bound_lit(self.box_posn[i][di]));
                            }
                        }
                        for di in 0..self.dimensions {
                            reason.push(actions.get_int_upper_bound_lit(self.box_posn[o_idx][di]));
                            reason.push(actions.get_int_lower_bound_lit(self.box_posn[o_idx][di]));
                        }
                        println!("CONFLICT in prune_max");
                        return Err(Conflict::new(actions, None, reason));
                    }
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


		IntDiffnSweep::new_in(&mut slv, vec![vec![pos_1, pos_2], vec![pos_3, pos_4]], vec![vec![size_1, size_2], vec![size_3, size_4]] );

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
        ]);
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
            ]);
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
