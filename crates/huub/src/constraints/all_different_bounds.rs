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
    bound: Vec<IntVal>,
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
    bound: Vec<IntVal>,
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
        let bound: Vec<IntVal> = Vec::with_capacity(n);
        let t: Vec<IntVal> = Vec::with_capacity(n);
        let d: Vec<IntVal> = Vec::with_capacity(n);
        let h: Vec<IntVal> = Vec::with_capacity(n);
        let bucket: Vec<IntVal> = Vec::with_capacity(n);

        AllDifferentBoundPoster { vars, interval, min_sorted, max_sorted, nb, bound, t, d, h, bucket }
    }
}

impl<P, E> Propagator<P, E> for AllDifferentBound
where
    P: PropagationActions,
    E: ExplanationActions,
{

    #[tracing::instrument(name = "all_different", level = "trace", skip(self, actions))]
    fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        let size: usize = self.vars.len();
        for i in (0..size).rev() {
            let t: usize  = self.min_sorted[i];
            self.interval[t].min = actions.get_int_lower_bound(self.vars[t]);
            for j in (i..size) {
                if self.interval[t].min < self.interval[self.min_sorted[j+1]].min {
                    break;
                }
                self.min_sorted[j] = t;
            }
            self.min_sorted[j] = t;
        }
        Ok(())
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


