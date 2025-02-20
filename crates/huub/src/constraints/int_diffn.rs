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
struct ForbiddenRegions {
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

    /// Generates forbidden regions given object o
    fn gen_fr<P: PropagationActions>(&mut self, actions: &mut P, o_idx:usize) -> Option<ForbiddenRegions> {
        let mut fr = ForbiddenRegions {
            lb: Vec::new(),
            ub: Vec::new()
        };
        let no_objects = self.box_posn.len();
        let curr_obj_size = &self.box_size[o_idx];
        for i in 0..no_objects {
            if i == o_idx { continue };
            let obj_pos = &self.box_posn[i];
            let obj_size = &self.box_size[i];
            for (&pos, size, curr_size) in izip!(obj_pos, obj_size, curr_obj_size) { 
                let pos_ub: IntVal = actions.get_int_upper_bound(pos); 
                let pos_lb: IntVal = actions.get_int_lower_bound(pos); 

                let fr_lb = pos_ub - curr_size + 1;
                let fr_ub = pos_lb + size - 1; 
                

            }
            // izip!(obj_pos, obj_size, curr_obj_size)
            //     .filter(|(pos, size, curr_size)| {
            //         actions.get_int_upper_bound(pos) - curr_obj_size + 1 <= actions.get_int_lower_bound(pos)
            //     })
        }

        Some(fr)


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

