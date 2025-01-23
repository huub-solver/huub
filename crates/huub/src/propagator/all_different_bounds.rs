use crate::{actions::{ExplanationActions, InitializationActions}, propagator::{Conflict, PropagationActions, Propagator}, solver::{
    engine::{activation_list::IntPropCond, int_var::LitMeaning, queue::PriorityLevel},
    poster::{BoxedPropagator, Poster, QueuePreferences},
    view::{IntView, IntViewInner},
}, IntVal, ReformulationError};
use crate::propagator::all_different_int::AllDifferentIntValue;
use std::cmp;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Interval {
    next: usize,
    min:  IntVal, max:  IntVal,
    min_rank: usize,
    max_rank: usize
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `all_different_int` constraint.
pub(crate) struct AllDifferentBound {
	/// List of integer variables that must take different values.
	vars: Vec<IntView>,
    interval: Vec<Interval>,
    min_sorted: Vec<usize>,
    max_sorted: Vec<usize>,
    nb: usize,            //TODO: Give better names
    bounds: Vec<IntVal>,
    t: Vec<usize>,
    d: Vec<IntVal>,
    h: Vec<usize>,
    bucket: Vec<usize>
}

/// [`Poster`] for [`AllDifferentBound`].
struct AllDifferentBoundPoster {
	/// The list of variables that must take different values.
	vars: Vec<IntView>,
    interval: Vec<Interval>,
    min_sorted: Vec<usize>,
    max_sorted: Vec<usize>,
    nb: usize,            //TODO: Give better names
    bounds: Vec<IntVal>,
    t: Vec<usize>,
    d: Vec<IntVal>,
    h: Vec<usize>,
    bucket: Vec<usize>,
}

impl AllDifferentBound {
	/// Prepare a new [`AllDifferentBound`] propagator to be posted to the
	/// solver.
	pub(crate) fn prepare<V: Into<IntView>, I: IntoIterator<Item = V>>(vars: I) -> impl Poster {
        let vars: Vec<IntView> = vars.into_iter().map(Into::into).collect();
        let size: usize = vars.len();
        let interval: Vec<Interval> = Vec::with_capacity(size);
        let min_sorted: Vec<usize> = (0..size).collect();
        let max_sorted: Vec<usize> = (0..size).collect();
        let nb: usize = 0;

        let n: usize = 2 * size + 2;
        let bounds: Vec<IntVal> = Vec::with_capacity(n); // Sorted array min and max bounds
        let t: Vec<usize> = Vec::with_capacity(n); // Critical capacity pointers
        let d: Vec<IntVal> = Vec::with_capacity(n); // Difference between critical capacities
        let h: Vec<usize> = Vec::with_capacity(n); // Hall interval pointers
        let bucket: Vec<usize> = Vec::with_capacity(n);

        AllDifferentBoundPoster { vars, interval, min_sorted, max_sorted, nb, bounds, t, d, h, bucket }
    }
}

impl<P, E> Propagator<P, E> for AllDifferentBound
where
    P: PropagationActions,
    E: ExplanationActions,
{

    #[tracing::instrument(name = "all_different", level = "trace", skip(self, actions))]
    fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        self.sort(actions);


        Ok(())
    }
}

impl AllDifferentBound {
    fn path_set(t: &mut Vec<usize>, start: usize, end: usize, to: usize) -> () {
        let mut k = start;
        let mut l;
        while k != end {
            t[k] = to;
            l = t[k];
            k = l;
        }
    }
    fn path_max(t: &Vec<usize>, mut i: usize) -> usize{
        while t[i] < i {
            i = t[i];
        }
        return i;
    }
    fn path_min(t: Vec<usize>, mut i: usize) -> usize {
        while t[i] > i {
            i = t[i];
        }
        return i;
    }
    fn filter_lower<P: PropagationActions>(&mut self, actions: &mut P) -> bool {
        let size: usize = self.vars.len();
        let mut j: usize;
        let mut z: usize;
        let mut w: usize;

        for i in 1..self.nb + 1 {
            self.h[i] = i - 1;
            self.t[i] = self.h[i];
            self.d[i] = self.bounds[i] - self.bounds[i - 1];
        }
        

        for i in 1..size {
            let min_rank = self.interval[self.max_sorted[i]].min_rank;
            let max_rank = self.interval[self.max_sorted[i]].max_rank;
            
            z = AllDifferentBound::path_max(&self.t, min_rank + 1);
            j = self.t[z];
            self.d[z] -= 1;
            self.bucket[z] = self.max_sorted[i];
            if self.d[z] == 0 {
                self.t[z] = z + 1;
                z = AllDifferentBound::path_max(&self.t, self.t[z]);
                self.t[z] = j;
            }
            AllDifferentBound::path_set(&mut self.t, min_rank + 1, z, z);
            if self.d[z] < self.bounds[z] - self.bounds[max_rank] {
                return false;
            }

            if self.h[min_rank] > min_rank {
                w = AllDifferentBound::path_max(&self.h, self.h[min_rank]);
                let hall_max: IntVal = self.bounds[w];
                let mut hall_min: IntVal = self.bounds[min_rank];
                let mut k: usize = w;
                while self.bounds[k] > hall_min {
                    let mut l = self.bucket[k];
                    while l >= 0 {
                        hall_min = cmp::min(hall_min, self.interval[l].min);
                        l = self.interval[l].next;
                    }
                    k -= 1;

                }
                
            }
        }
        return true; 
    }

    fn filter_upper<P: PropagationActions>(&mut self, actions: &mut P) {

    }
    fn sort<P: PropagationActions>(&mut self, actions: &mut P) {
        let size: usize = self.vars.len();
        let mut saved_j;

        for i in (0..size - 1).rev() {
            let t: usize = self.min_sorted[i];
            self.interval[t].min = actions.get_int_lower_bound(self.vars[t]);
            saved_j = i;
            for j in i..size {
                if self.interval[t].min < self.interval[self.min_sorted[j + 1]].min {
                    saved_j = j;
                    break;
                }
                self.min_sorted[j] = self.min_sorted[j + 1];
            }
            self.min_sorted[saved_j] = t;
        }

        for i in (0..size - 1).rev() {
            let t: usize = self.max_sorted[i];
            self.interval[t].max = actions.get_int_upper_bound(self.vars[t]) + 1;
            saved_j = i;
            for j in i..size - 1 { 
                if self.interval[t].max < self.interval[self.max_sorted[j + 1]].max {
                    saved_j = j;
                    break;
                }
                self.max_sorted[j] = self.max_sorted[j + 1];
            }
            self.max_sorted[saved_j] = t;
        }

        let mut min: IntVal = self.interval[self.min_sorted[0]].min;
        let mut max: IntVal = self.interval[self.max_sorted[0]].max;
        let mut last: IntVal = min - 2;
        self.bounds[0] = min - 2;

        let mut i = 0;
        let mut j = 0;
        loop {
            if i < size && min <= max {
                if min != last {
                    self.nb += 1;
                    last = min;
                    self.bounds[self.nb] = min;
                }
                self.interval[self.min_sorted[i]].min_rank = self.nb;
                i += 1;
                if i < size {
                    min = self.interval[self.min_sorted[i]].min;
                }
            } else {
                if max != last {
                    self.nb += 1;
                    last = max;
                    self.bounds[self.nb] = max;
                }
                self.interval[self.max_sorted[i]].max_rank = self.nb;
                j += 1;
                if j == size {
                    break;
                }
                max = self.interval[self.max_sorted[i]].max;
            }
        }
        self.bounds[self.nb + 1] = self.bounds[self.nb] + 2;
    }
}


impl Poster for AllDifferentBoundPoster {
    fn post<I: InitializationActions>(
        self,
        actions: &mut I,
    ) -> Option<I> {//Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
        None
    }
}


