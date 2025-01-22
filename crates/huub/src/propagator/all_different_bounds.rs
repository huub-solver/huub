use crate::{actions::{ExplanationActions, InitializationActions}, propagator::{Conflict, PropagationActions, Propagator}, solver::{
    engine::{activation_list::IntPropCond, int_var::LitMeaning, queue::PriorityLevel},
    poster::{BoxedPropagator, Poster, QueuePreferences},
    view::{IntView, IntViewInner},
}, IntVal, ReformulationError};
use crate::propagator::all_different_int::AllDifferentIntValue;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Interval {
    next: IntVal,
    min:  IntVal,
    max:  IntVal,
    min_rank: IntVal,
    max_rank: IntVal
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `all_different_int` constraint.
pub(crate) struct AllDifferentBound {
	/// List of integer variables that must take different values.
	vars: Vec<IntView>,
    interval: Vec<Interval>,
    min_sorted: Vec<usize>,
    max_sorted: Vec<usize>,
    nb: IntVal,            //TODO: Give better names
    bounds: Vec<IntVal>,
    t: Vec<IntVal>,
    d: Vec<IntVal>,
    h: Vec<IntVal>,
    bucket: Vec<IntVal>,
}

/// [`Poster`] for [`AllDifferentBound`].
struct AllDifferentBoundPoster {
	/// The list of variables that must take different values.
	vars: Vec<IntView>,
    interval: Vec<Interval>,
    min_sorted: Vec<usize>,
    max_sorted: Vec<usize>,
    nb: IntVal,            //TODO: Give better names
    bounds: Vec<IntVal>,
    t: Vec<IntVal>,
    d: Vec<IntVal>,
    h: Vec<IntVal>,
    bucket: Vec<IntVal>,
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
        let nb: IntVal = 0;

        let n: usize = 2 * size + 2;
        let bounds: Vec<IntVal> = Vec::with_capacity(n); // Sorted array min and max bounds
        let t: Vec<IntVal> = Vec::with_capacity(n); // Critical capacity pointers
        let d: Vec<IntVal> = Vec::with_capacity(n); // Difference between critical capacities
        let h: Vec<IntVal> = Vec::with_capacity(n); // Hall interval pointers
        let bucket: Vec<IntVal> = Vec::with_capacity(n);

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

    fn filter_lower<P: PropagationActions>(&mut self, actions: &mut P) {
        
    }
    fn filter_upper<P: PropagationActions>(&mut self, actions: &mut P) {

    }
    fn sort<P: PropagationActions>(&mut self, actions: &mut P) {
        let size: usize = self.vars.len();
        let mut saved_j = 0;

        for i in (0..size).rev() {
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

        for i in (0..size).rev() {
            let t: usize = self.max_sorted[i];
            self.interval[t].max = actions.get_int_upper_bound(self.vars[t]) + 1;
            saved_j = i;
            for j in i..size { // index might be incorrect
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
    fn path_set(t: &mut Vec<IntVal>, start: IntVal, end: IntVal, to: IntVal) -> () {
        let mut k: IntVal = start;;
        let mut l: IntVal = start;
        while k != end {
            t[k] = to;
            l = t[k];
            k = l;
        }
    }
    fn path_max(t: Vec<IntVal>, mut i: IntVal) -> IntVal {
        while t[i] < i {
            i = t[i];
        }
        i
    }
    fn path_min(t: Vec<IntVal>, mut i: IntVal) -> IntVal {
        while t[i] > i {
            i = t[i];
        }
        i
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


