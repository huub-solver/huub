use crate::actions::{PropagatorInitActions, TrailingActions};
use crate::solver::trail::TrailedInt;
use crate::solver::BoolView;
use crate::IntVal;
use index_vec::IndexVec;
use std::mem;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// Infrastructure to use [TrailedInt] before the actual trailing infrastructure is available.
pub(crate) struct InitialTrail {
    /// Elements locally stored before trailing.
    elements: IndexVec<TrailedInt, IntVal>,
    /// Whether elements should actually be trailed.
    should_trail: IndexVec<TrailedInt, bool>,
    /// The position of the elements in the actual trailing infrastructure.
    trail_position: IndexVec<TrailedInt, Option<TrailedInt>>,
    /// Whether the contents are actually trailed.
    is_trailed: bool,
}

impl InitialTrail {
    
    pub(crate) fn new() -> InitialTrail {
        InitialTrail { 
            elements: IndexVec::new(),
            should_trail: IndexVec::new(),
            trail_position: IndexVec::new(),
            is_trailed: false,
        }
    }
    
    /// Add a new trailed integer. Only available until actually trailed.
    pub(crate) fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
        assert!(!self.is_trailed, "Actual trailing infrastructure has to be used at this point");
        let _ = self.should_trail.push(true);
        self.elements.push(init)
    }

    /// Actually trail the integers that were not removed. Note that after calling this method, only 
    /// [InitialTrail::map_to_trail] can be used.
    pub(crate) fn init_trail<P: PropagatorInitActions + ?Sized>(&mut self, actions: &mut P) {
        for (&val, &should_trail) in self.elements.iter().zip(self.should_trail.iter()) {
            if should_trail {
                let _ = self.trail_position.push(Some(actions.new_trailed_int(val)));
            } else { 
                let _ = self.trail_position.push(None);
            }
        }
    }
    
    /// Remove a trailed integer from actual trailing.
    pub(crate) fn remove(&mut self, i: TrailedInt) {
        assert!(!self.is_trailed, "Actual trailing infrastructure has to be used at this point");
        self.should_trail[i] = false;
    }

    /// Map the initial trailed integer to the actual trailed integer. Note that this will fail 
    /// before calling [InitialTrail::init_trail], and for trailed integers that were removed.
    pub(crate) fn map_to_trail(&self, initial: TrailedInt) -> TrailedInt {
        self.trail_position[initial].unwrap()
    }
    
}

impl TrailingActions for InitialTrail {
    
    fn get_bool_val(&self, _bv: BoolView) -> Option<bool> {
        assert!(!self.is_trailed, "Actual trailing infrastructure has to be used at this point");
        None
    }

    fn get_trailed_int(&self, i: TrailedInt) -> IntVal {
        assert!(!self.is_trailed, "Actual trailing infrastructure has to be used at this point");
        self.elements[i]
    }

    fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal {
        assert!(!self.is_trailed, "Actual trailing infrastructure has to be used at this point");
        if self.elements[i] == v {
            return v;
        }
        mem::replace(&mut self.elements[i], v)
    }
    
}