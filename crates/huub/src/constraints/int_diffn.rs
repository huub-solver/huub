use itertools::izip;
use crate::{actions::{
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
        actions: &mut P,
        o_idx:usize
    ) -> Result<(), Conflict> {
        Ok(())
    }
    fn prune_max<P: PropagationActions>(
        actions: &mut P,
        o_idx:usize
    ) -> Result<(), Conflict> {
        Ok(())
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
            sweep[rotation] = jump[rotation];
            jump[rotation] = actions.get_int_lower_bound(curr_obj_pos[rotation]) - 1;
            // Current sweep-point is withing the bounds of the current object
            if sweep[rotation] <= actions.get_int_lower_bound(curr_obj_pos[rotation]) {
                return true;
            } else {
                // Reset sweep-point
                sweep[rotation] = actions.get_int_upper_bound(curr_obj_pos[rotation]);
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
        for d in 0..dimensions {
            let no_overlap = actions.get_int_upper_bound(curr_obj_pos[d]) < fr.lb[d] ||
                actions.get_int_lower_bound(curr_obj_pos[d]) > fr.ub[d];
            if no_overlap {
                return false;
            }
        }
        true
    } 

        


    /// Generates forbidden regions given object o
    fn generate_fr<P: PropagationActions>(
        actions: &mut P,
        o_idx:usize,
        box_posn:Vec<Vec<IntView>>,
        box_size:Vec<Vec<IntVal>>,
        dimensions:usize
    ) -> Option<Vec<ForbiddenRegion>> {
        let mut all_fr:Vec<ForbiddenRegion> = vec![];
        let no_objects = box_posn.len();
        let curr_obj_size = &box_size[o_idx]; // get the address &?
        for i in 0..no_objects {
            let mut fr = ForbiddenRegion {
                lb: Vec::new(),
                ub: Vec::new()
            };

            if i == o_idx { continue };
            let obj_pos = &box_posn[i];
            let obj_size = &box_size[i];

            for (&pos, size, curr_size) in izip!(obj_pos, obj_size, curr_obj_size) { 
                let pos_ub: IntVal = actions.get_int_upper_bound(pos); 
                let pos_lb: IntVal = actions.get_int_lower_bound(pos); 

                let fr_lb = pos_ub - curr_size + 1;
                let fr_ub = pos_lb + size - 1; 
                if fr_lb <= fr_ub {
                    fr.lb.push(fr_lb);
                    fr.ub.push(fr_lb);
                } else {
                    break;
                }
            }

            let is_overlapping = Self::overlaps::<P>(
                actions,
                &box_posn[o_idx],
                &fr,
                dimensions);

            if fr.lb.len() == dimensions && is_overlapping{
                all_fr.push(fr);
            }
        }
        if all_fr.is_empty() { return None };
        Some(all_fr)
    }

}

impl<P, E> Propagator<P, E> for IntDiffnSweep
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "diffn", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        // TODO
		Ok(())
	}

}

