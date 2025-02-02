use crate::{
    actions::{ExplanationActions, InitializationActions},
    propagator::{Conflict, PropagationActions, Propagator},
    solver::{
        engine::{activation_list::IntPropCond, int_var::LitMeaning, queue::PriorityLevel},
        poster::{BoxedPropagator, Poster, QueuePreferences},
        view::{IntView, IntViewInner},
    },
    IntVal, ReformulationError
};
use std::cmp;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Interval {
    next: usize,
    min:  IntVal, max:  IntVal, // Min and max value of variable
    min_rank: usize,            // Min index in bounds vector
    max_rank: usize             // Max index in bounds vector
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bound consistent propagator for the `all_different_bound` constraint.
pub(crate) struct AllDifferentBound {
	/// List of integer variables that must take different values.
	vars: Vec<IntView>,      // Integer variables with domains
    interval: Vec<Interval>, // Struct to store information about variable
    min_sorted: Vec<usize>,  // Index (from vars) of all variables sorted by min bound
    max_sorted: Vec<usize>,  // Index (from vars) of all variables sorted by max bound
    num_bounds: usize,       // Number of different bounds
    bounds: Vec<IntVal>,     // Ordered vector of all different max and min bounds with dummies
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
    num_bounds: usize,            //TODO: Give better names
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
        let mut interval: Vec<Interval> = Vec::with_capacity(size);
        for _i in 0..size {
            interval.push(Interval {
                next: 0,
                min: 0,
                max: 0,
                min_rank: 0,
                max_rank: 0
            })
        }
        let min_sorted: Vec<usize> = (0..size).collect();
        let max_sorted: Vec<usize> = (0..size).collect();

        let num_bounds: usize = 0;
        let n: usize = 2 * size + 2;
        AllDifferentBoundPoster {
            vars,
            interval,
            min_sorted,
            max_sorted,
            num_bounds,
            bounds: vec![0; n],
            t     : vec![0; n],
            d     : vec![0; n],
            h     : vec![0; n],
            bucket: vec![0; n]
        }
    }

    // Sets everything in t, between start and end to to e.g
    // start = 2, end = 3, to = 5
    // t = 0->4->3->1->2->0 gives:
    // 0->5->5->5->2->0
    fn path_set(t: &mut Vec<usize>, start: usize, end: usize, to: usize) -> () {
        let mut k;
        let mut l = start;
        while l != end {
            k = l;
            l = t[k];
            t[k] = to;
        }
    }

    // Follows path i, t[i], t[t[i]], ... until we stop increasing
    fn path_max(t: &Vec<usize>, mut i: usize) -> usize{
        while t[i] > i {
            i = t[i];
        }
        i
    }
    
    // Follows path i, t[i], t[t[i]], ... until we stop decreasing
    fn path_min(t: &Vec<usize>, mut i: usize) -> usize {
        while t[i] < i {
            i = t[i];
        }
        i
    }

    fn filter_lower<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict>{
        let size: usize = self.vars.len();
        let mut j: usize;
        let mut z: usize;
        let mut w: usize;

        println!("filter lower");
        for i in 1..=self.num_bounds + 1 {
            self.h[i] = i - 1;
            self.t[i] = self.h[i];
            self.d[i] = self.bounds[i] - self.bounds[i - 1];
            self.bucket[i]  = usize::MAX;
        }

        for i in 0..size {
            let max_rank = self.interval[self.max_sorted[i]].max_rank;
            let min_rank = self.interval[self.max_sorted[i]].min_rank;
            println!("var {:?}, [{:?}, {:?}))", self.max_sorted[i], self.bounds[min_rank], self.bounds[max_rank]);

            z = AllDifferentBound::path_max(&self.t, min_rank + 1);
            j = self.t[z];
            self.d[z] -= 1;
            self.interval[self.max_sorted[i]].next = self.bucket[z];
            self.bucket[z] = self.max_sorted[i];
            if self.d[z] == 0 {
                self.t[z] = z + 1;
                z = AllDifferentBound::path_max(&self.t, self.t[z]);
                self.t[z] = j;
            }
            AllDifferentBound::path_set(&mut self.t, min_rank + 1, z, z);

            if self.d[z] < self.bounds[z] - self.bounds[max_rank] {
                println!("No solution lower bound"); // We should probably not enter here
            }

            if self.h[min_rank] > min_rank {
                w = AllDifferentBound::path_max(&self.h, self.h[min_rank]);
                let hall_max: IntVal = self.bounds[w];
                let mut hall_min: IntVal = self.bounds[min_rank];
                let mut k: usize = w;
                while self.bounds[k] > hall_min {
                    let mut l = self.bucket[k];
                    while l != usize::MAX {
                        hall_min = cmp::min(hall_min, self.interval[l].min);
                        l = self.interval[l].next;
                    }
                    k -= 1;
                }

                k = w;
                println!("hall interval [{:?}, {:?})", hall_min, hall_max);
                let mut reason = Vec::new();
                println!("Reason [[ var {:?}: [{:?}, {:?}) >= {:?}]", i, self.interval[self.max_sorted[i]].min, self.interval[self.max_sorted[i]].max, hall_min);
                reason.push(actions.get_int_lit(self.vars[self.max_sorted[i]], LitMeaning::GreaterEq(hall_min)));
                while self.bounds[k] > hall_min {
                    let mut l = self.bucket[k];
                    while l != usize::MAX {
                        println!("Reason [[var {:?} [{:?}, {:?}) >= {:?}]", l, self.interval[l].min, self.interval[l].max, hall_max);
                        reason.push(actions.get_int_lit(self.vars[l], LitMeaning::GreaterEq(hall_min)));
                        println!("Reason [[ var {:?} [{:?}, {:?}) < {:?}]", l, self.interval[l].min, self.interval[l].max, hall_max);
                        reason.push(actions.get_int_lit(self.vars[l], LitMeaning::Less(hall_max))); // since [x<d+1] = [x<=d]
                        l = self.interval[l].next;
                    }
                    k -= 1;
                }

                actions.set_int_lower_bound(self.vars[self.max_sorted[i]], hall_max, &*reason)?; //reason type might be an issue
                self.interval[self.max_sorted[i]].min = hall_max;
                AllDifferentBound::path_set(&mut self.h, min_rank, w, w);
            }
            if self.d[z] == self.bounds[z] - self.bounds[max_rank] {
                let h_max_rank = self.h[max_rank];
                // Save Hall interval
                AllDifferentBound::path_set(&mut self.h, h_max_rank, j - 1, max_rank);
                self.h[min_rank] = j - 1;
            }
        }
        Ok(())
    }

    fn filter_upper<P: PropagationActions>(&mut self, actions: &mut P) -> Result<(), Conflict>{
        let size: usize = self.vars.len();
        let mut j: usize;
        let mut z: usize;
        let mut w: usize;

        println!("filter upper");
        for i in 1..=self.num_bounds + 1 {
            self.h[i] = i + 1;
            self.t[i] = self.h[i];
            self.d[i] = self.bounds[i] - self.bounds[i - 1];
            self.bucket[i]  = usize::MAX;
        }

        for i in (0..size).rev() {
            let max_rank = self.interval[self.min_sorted[i]].max_rank;
            let min_rank = self.interval[self.min_sorted[i]].min_rank;

            println!("var {:?}, [{:?}, {:?})", self.min_sorted[i], self.bounds[min_rank], self.bounds[max_rank]);
            z = AllDifferentBound::path_min(&self.t, max_rank - 1);
            j = self.t[z];
            self.d[z] -= 1;
            self.interval[self.min_sorted[i]].next = self.bucket[z];
            self.bucket[z] = self.min_sorted[i];
            if self.d[z] == 0 {
                self.t[z] = z - 1;
                z = AllDifferentBound::path_min(&self.t, self.t[z]);
                self.t[z] = j;
            }
            AllDifferentBound::path_set(&mut self.t, max_rank - 1, z, z);

            if self.d[z] < self.bounds[min_rank] - self.bounds[z] {
                println!("No solution upper bound"); // If not solution is found
            }

            if self.h[max_rank] < max_rank {
                w = AllDifferentBound::path_min(&self.h, self.h[max_rank]);
                let hall_min: IntVal = self.bounds[w];
                let mut hall_max: IntVal = self.bounds[max_rank];
                let mut k: usize = w;
                while self.bounds[k] < hall_max {
                    let mut l = self.bucket[k];
                    while l != usize::MAX {
                        hall_max = cmp::min(hall_max, self.interval[l].max);
                        l = self.interval[l].next;
                    }
                    k += 1;
                }

                k = w;
                println!("hall intervall [{:?}, {:?}))", hall_min, hall_max);
                let mut reason = Vec::new();
                reason.push(actions.get_int_lit(self.vars[self.min_sorted[i]], LitMeaning::Less(hall_max))); // since [x<d+1] = [x<=d]
                println!("Reason [[ var {:?}: [{:?}, {:?}) < {:?}]", i, self.interval[self.min_sorted[i]].min, self.interval[self.min_sorted[i]].max, hall_max);
                while self.bounds[k] < hall_max {
                    let mut l = self.bucket[k];
                    while l != usize::MAX {
                        reason.push(actions.get_int_lit(self.vars[l], LitMeaning::GreaterEq(hall_min)));
                        println!("Reason [[ var {:?}: [{:?}, {:?}) >= {:?}]", l, self.interval[l].min, self.interval[l].max, hall_min);
                        reason.push(actions.get_int_lit(self.vars[l], LitMeaning::Less(hall_max))); // since [x<d+1] = [x<=d]
                        println!("Reason [[ var {:?}: [{:?}, {:?}) < {:?}]", l, self.interval[l].min, self.interval[l].max, hall_max);
                        l = self.interval[l].next;
                    }
                    k += 1;
                }
                println!("Setting upper bound of variable {:?} with bounds [{:?}, {:?})  to {:?}", self.min_sorted[i], self.interval[self.min_sorted[i]].min, self.interval[self.min_sorted[i]].max, hall_min );
                actions.set_int_upper_bound(self.vars[self.min_sorted[i]], hall_min -1, &*reason)?;
                self.interval[self.min_sorted[i]].max = hall_min;

                // What is this needed for?
                // if actions.get_int_upper_bound(self.vars[self.min_sorted[i]]) < hall_min -1 PushInQueue()

                AllDifferentBound::path_set(&mut self.h, max_rank, w, w);
            }

            if self.d[z] == self.bounds[min_rank] - self.bounds[z] {
                let h_min_rank = self.h[min_rank]; // Can't send borrowed item twice
                // Save Hall interval
                AllDifferentBound::path_set(&mut self.h, h_min_rank, j + 1, min_rank);
                self.h[min_rank] = j + 1;
            }
        }
        Ok(())

    }
    //Sorts max_sorted and min_sorted and sets the bounds vector
    fn sort<P: PropagationActions>(&mut self, actions: &mut P) {
        let size: usize = self.vars.len();

        let mut min_values = vec![0; size];
        let mut max_values = vec![0; size];
        for i in 0..size {
            self.interval[i].min = actions.get_int_lower_bound(self.vars[i]);
            self.interval[i].max = actions.get_int_upper_bound(self.vars[i]) + 1;

            min_values[i] = self.interval[i].min;
            max_values[i] = self.interval[i].max;
        }

        self.min_sorted.sort_by(|&a, &b| min_values[a].cmp(&min_values[b]));
        self.max_sorted.sort_by(|&a, &b| max_values[a].cmp(&max_values[b]));

        let mut min: IntVal = self.interval[self.min_sorted[0]].min;
        let mut max: IntVal = self.interval[self.max_sorted[0]].max;
        let mut last: IntVal = min - 2;
        self.bounds[0] = min - 2; // Dummy


        let mut i = 0;
        let mut j = 0;
        self.num_bounds = 0;
        loop {
            if i < size && min <= max {
                if min != last {
                    self.num_bounds += 1;
                    last = min;
                    self.bounds[self.num_bounds] = min;
                }
                self.interval[self.min_sorted[i]].min_rank = self.num_bounds;
                i += 1;
                if i < size {
                    min = self.interval[self.min_sorted[i]].min;
                }
            } else {
                if max != last {
                    self.num_bounds += 1;
                    last = max;
                    self.bounds[self.num_bounds] = max;
                }
                self.interval[self.max_sorted[j]].max_rank = self.num_bounds;
                j += 1;
                if j == size {
                    break;
                }
                max = self.interval[self.max_sorted[j]].max;
            }
        }
        self.bounds[self.num_bounds + 1] = self.bounds[self.num_bounds] + 2; // Dummy
    }
}

impl<P, E> Propagator<P, E> for AllDifferentBound
where
    P: PropagationActions,
    E: ExplanationActions,
{

    #[tracing::instrument(name = "all_different_bounds", level = "trace", skip(self, actions))]
    fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
        self.sort(actions);
        self.filter_lower::<P>(actions)?;
        self.filter_upper::<P>(actions)?;
        Ok(())
    }
}

impl Poster for AllDifferentBoundPoster {
    fn post<I: InitializationActions>(
        self,
        actions: &mut I,
    ) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
        let enqueue = self
            .vars
            .iter()
            .any(|v| matches!(v, IntView(IntViewInner::Const(_))));
        let prop = AllDifferentBound {
            vars: self.vars,
            interval: self.interval,
            min_sorted: self.min_sorted,
            max_sorted: self.max_sorted,
            num_bounds: self.num_bounds,
            bounds: self.bounds,
            t: self.t,
            d: self.d,
            h: self.h,
            bucket: self.bucket
        };
        for &v in prop.vars.iter() {
            actions.enqueue_on_int_change(v, IntPropCond::Bounds);
        }
        Ok((
            Box::new(prop),
            QueuePreferences {
                enqueue_on_post: enqueue,
                priority: PriorityLevel::Low,
            },
        ))
    }
}
#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
    use rangelist::RangeList;
    use tracing_test::traced_test;

    use crate::{
        propagator::all_different_bounds::AllDifferentBound,
        solver::engine::int_var::{EncodingType, IntVar},
        // IntVal, IntView, SolveResult,
        Solver,
    };

    #[test]
    #[traced_test]
    fn test_all_different_bound() {
        let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
        let a = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=3]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let b = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=3]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let c = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=3]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        slv.add_propagator(AllDifferentBound::prepare(vec![a, b, c]))
            .unwrap();
        slv.assert_all_solutions(&[a, b, c], |sol| sol.iter().all_unique());
    }

    #[test]
    #[traced_test]
    fn test_all_different_bound_1() {
        let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
        let a = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let b = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([2..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let c = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let d = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([2..=5]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let e = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=6]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let f = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=6]),
            EncodingType::Eager,
            EncodingType::Eager,
        );

        slv.add_propagator(AllDifferentBound::prepare(vec![a, b, c, d, e, f]))
            .unwrap();
        slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
    }

    #[test]
    #[traced_test]
    fn test_all_different_bound_2() {
        let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
        let a = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=6]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let b = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let c = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([2..=5]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let d = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([2..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let e = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([3..=4]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let f = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=6]),
            EncodingType::Eager,
            EncodingType::Eager,
        );

        slv.add_propagator(AllDifferentBound::prepare(vec![a, b, c, d, e, f]))
            .unwrap();
        slv.assert_all_solutions(&[a, b, c, d, e, f], |sol| sol.iter().all_unique());
    }

    #[test]
    #[traced_test]
    fn test_all_different_bound_unsat() {
        let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
        let a = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=2]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let b = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=2]),
            EncodingType::Eager,
            EncodingType::Eager,
        );
        let c = IntVar::new_in(
            &mut slv,
            RangeList::from_iter([1..=2]),
            EncodingType::Eager,
            EncodingType::Eager,
        );

        slv.add_propagator(AllDifferentBound::prepare(vec![a, b, c]))
            .unwrap();
        slv.assert_unsatisfiable();
    }
}
