//! Time-table-edge-finding for the `cumulative` constraint:
//! the energy overload check, the est/lct bounds-filtering sweep, and the
//! opportunistic extended-edge-finding phase, together with their explanations.
//! Methods extend [`CumulativePropagator`].

use std::cmp;

use tracing::trace;

use crate::{
	IntVal,
	actions::{
		IntDecisionActions, PropagationActions, PropagationContext, ReasonActions, ReasoningEngine,
	},
	constraints::{IntSolverActions, cumulative::CumulativePropagator},
};

/// Per-task quantities used by the edge-finding phases, computed once
/// per propagation from the current domains.
///
/// All energy reasoning uses the *minimum* duration and usage (a sound lower
/// bound on the energy a task requires). The earliest completion time uses the
/// minimum duration (the smallest compulsory part), while the latest completion
/// time uses the maximum duration (the true deadline a task must respect).
///
/// Both are clamped to zero, so that `energy > 0` implies `usage > 0`: the
/// filtering divides available energy by a task's usage, and a negative bound
/// would silently turn that into an unsound update.
struct EdgeFindingData {
	/// Earliest start time `est_i = lb(S_i)`.
	est: IntVal,
	/// Latest start time `lst_i = ub(S_i)`.
	lst: IntVal,
	/// Earliest completion time `ect_i = est_i + dur_lb_i`.
	ect: IntVal,
	/// Latest completion time `lct_i = lst_i + dur_ub_i` (the deadline).
	lct: IntVal,
	/// Minimum duration of the task.
	dur: IntVal,
	/// Minimum usage of the task.
	usage: IntVal,
	/// Minimum energy `e_i = dur_lb_i * usage_lb_i`.
	energy: IntVal,
	/// Length of the compulsory part `pTT_i = max(0, ect_i - lst_i)`.
	fixed_dur: IntVal,
	/// Free energy `eEF_i = usage_lb_i * (dur_lb_i - pTT_i)` of the task.
	free_energy: IntVal,
	/// Latest start of the free part `lstEF_i = lst_i + pTT_i`.
	lst_ef: IntVal,
	/// Energy of the time-table profile in `[est_i, +inf)`.
	tt_after_est: IntVal,
	/// Energy of the time-table profile in `[lct_i, +inf)`.
	tt_after_lct: IntVal,
}

/// The complete set of edge-finding inputs for a single propagation: the
/// per-task [`EdgeFindingData`], the maximum resource capacity, and the
/// two task orderings the sweeps iterate.
///
/// The capacity is the *maximum* capacity available in a window (a sound upper
/// bound on the energy the resource makes available), which keeps the energy
/// reasoning sound.
struct EdgeFindingState {
	/// Per-task energy quantities, indexed by task.
	tasks: Vec<EdgeFindingData>,
	/// Maximum resource capacity `R`.
	capacity: IntVal,
	/// Task indices sorted by non-decreasing earliest start time.
	by_est: Vec<usize>,
	/// Task indices sorted by non-decreasing latest completion time.
	by_lct: Vec<usize>,
}

/// A candidate bound update found by the edge-finding bounds-filtering
/// phase: task `task`'s start time can be tightened thanks to the resource
/// overload that would otherwise occur in the time window `[begin, end)`. The
/// concrete bound is re-derived soundly from this window at application time,
/// so only the task, window, and direction are carried here.
struct EdgeFindingUpdate {
	/// Task whose bound is tightened.
	task: usize,
	/// Start of the overloaded time window justifying the update.
	begin: IntVal,
	/// End of the overloaded time window justifying the update.
	end: IntVal,
	/// Whether this update raises the earliest start (`true`) or lowers the
	/// latest completion (`false`).
	is_lb: bool,
}

impl<I1, I2, I3, I4> CumulativePropagator<I1, I2, I3, I4> {
	/// The energy of the time-table profile in `[bounds[i], +inf)` for every
	/// profile bound `i`, so that [`Self::profile_energy_after`] can answer in
	/// logarithmic time instead of rescanning the whole profile for every task.
	fn build_profile_energy(&self) -> Vec<IntVal> {
		let mut profile_energy = vec![0; self.bounds.len()];
		// The profile is empty after its last bound, so accumulate backwards from
		// there.
		for i in (0..self.bounds.len().saturating_sub(1)).rev() {
			profile_energy[i] =
				profile_energy[i + 1] + self.heights[i] * (self.bounds[i + 1] - self.bounds[i]);
		}
		profile_energy
	}

	/// Returns the first task interval `[begin, end)` whose required energy
	/// exceeds the available resource energy `R * (end - begin)`, or `None` if
	/// no interval is overloaded.
	fn consistency_check(state: &EdgeFindingState) -> Option<(IntVal, IntVal)> {
		// Iterate tasks by lct in non-increasing order.
		let mut prev_end: Option<IntVal> = None;
		for &b in state.by_lct.iter().rev() {
			if state.tasks[b].energy == 0 {
				continue;
			}
			let end = state.tasks[b].lct;
			if prev_end == Some(end) {
				// A window with this end was already checked (duplicate lct).
				continue;
			}
			prev_end = Some(end);

			// Accumulating the free energy required within [begin, end).
			let mut en_req_free = 0;
			for &j in state.by_est.iter().rev() {
				let begin = state.tasks[j].est;
				if begin >= end || state.tasks[j].energy == 0 {
					continue;
				}
				if state.tasks[j].lct <= end {
					// The free part of task j is entirely inside the window.
					en_req_free += state.tasks[j].free_energy;
				} else {
					// Task j starts inside the window but completes after it; only
					// the part of its free duration forced into the window counts.
					en_req_free += state.tasks[j].usage * cmp::max(end - state.tasks[j].lst_ef, 0);
				}
				let en_req =
					en_req_free + state.tasks[j].tt_after_est - state.tasks[b].tt_after_lct;
				if state.capacity * (end - begin) - en_req < 0
					&& Self::window_overloaded(state, begin, end)
				{
					return Some((begin, end));
				}
			}
		}
		None
	}

	/// Whether `task` is forced to place energy inside `[begin, end)` under
	/// every schedule allowed by its bounds (non-zero energy, `ect > begin`,
	/// and `lst < end`).
	fn contributes(task: &EdgeFindingData, begin: IntVal, end: IntVal) -> bool {
		task.energy > 0 && task.ect > begin && task.lst < end
	}

	/// Collects the per-task energy quantities, the capacity, and the task
	/// orderings for one propagation from the current domains.
	fn edge_finding_data<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		profile_energy: &[IntVal],
	) -> EdgeFindingState
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		let n = self.start_times.len();
		let mut tasks = Vec::with_capacity(n);
		for i in 0..n {
			let est = self.earliest_start_time(ctx, i);
			let lst = self.latest_start_time(ctx, i);
			let dur = cmp::max(self.durations[i].min(ctx), 0);
			let usage = cmp::max(self.usages[i].min(ctx), 0);
			let ect = est + dur;
			let lct = lst + cmp::max(self.durations[i].max(ctx), 0);
			// Length of the compulsory part.
			let fixed_dur = cmp::max(ect - lst, 0);
			tasks.push(EdgeFindingData {
				est,
				lst,
				ect,
				lct,
				dur,
				usage,
				energy: dur * usage,
				fixed_dur,
				free_energy: usage * (dur - fixed_dur),
				lst_ef: lst + fixed_dur,
				tt_after_est: self.profile_energy_after(profile_energy, est),
				tt_after_lct: self.profile_energy_after(profile_energy, lct),
			});
		}
		// Use the maximum capacity available in a window to ensure the energy
		// reasoning check is sound.
		let capacity = self.capacity.max(ctx);
		let mut by_est: Vec<usize> = (0..n).collect();
		by_est.sort_unstable_by_key(|&i| tasks[i].est);
		let mut by_lct: Vec<usize> = (0..n).collect();
		by_lct.sort_unstable_by_key(|&i| tasks[i].lct);
		EdgeFindingState {
			tasks,
			capacity,
			by_est,
			by_lct,
		}
	}

	/// Earliest-start-time filtering: for each task interval `[begin, end)`
	/// lifts the earliest start of the task overlapping it on the right that
	/// cannot fit in the energy left, appending the updates. Returns
	/// `Some((begin, end))` on a resource overload.
	fn est_filtering(
		state: &EdgeFindingState,
		opportunistic: bool,
		updates: &mut Vec<EdgeFindingUpdate>,
	) -> Option<(IntVal, IntVal)> {
		// Strongest new bounds found so far per task, to keep only the best update
		// and avoid queueing dominated ones.
		let mut new_est: Vec<IntVal> = state.tasks.iter().map(|t| t.est).collect();
		let mut new_lct: Vec<IntVal> = state.tasks.iter().map(|t| t.lct).collect();
		let horizon_energy = state.capacity
			* (state.tasks[*state.by_lct.last().unwrap()].lct - state.tasks[state.by_est[0]].est);
		let mut prev_end: Option<IntVal> = None;
		for &i in state.by_lct.iter().rev() {
			if state.tasks[i].energy == 0 {
				continue;
			}
			let end = state.tasks[i].lct;
			if prev_end == Some(end) {
				continue;
			}
			prev_end = Some(end);

			let mut en_req_free = 0;
			let mut max_en_req_start = -1;
			let mut iota: Option<usize> = None;
			// Minimum available energy and the begin achieving it, for the
			// opportunistic extended-edge-finding upper-bound update.
			let mut min_en_avail = horizon_energy;
			let mut min_begin: Option<IntVal> = None;
			for &j in state.by_est.iter().rev() {
				let begin = state.tasks[j].est;
				if begin >= end || state.tasks[j].energy == 0 {
					continue;
				}

				// Opportunistic extended edge finding (Vilím (2011), through/left): if
				// the tightest window `[min_begin, end)` seen so far cannot fit all of
				// `j`, lower its latest completion accordingly.
				if opportunistic && let Some(mb) = min_begin {
					let min_en_in = state.tasks[j].usage
						* cmp::max(
							cmp::min(state.tasks[j].ect, end) - cmp::max(mb, state.tasks[j].lst),
							0,
						);
					let full = state.tasks[j].usage
						* (cmp::min(state.tasks[j].lct, end) - cmp::max(mb, state.tasks[j].lst));
					if min_en_avail + min_en_in < full {
						let dur_avail = (min_en_avail + min_en_in) / state.tasks[j].usage;
						let lct_new = mb + dur_avail;
						if lct_new < new_lct[j] {
							updates.push(EdgeFindingUpdate {
								task: j,
								begin: mb,
								end,
								is_lb: false,
							});
							new_lct[j] = lct_new;
						}
					}
				}

				if state.tasks[j].lct <= end {
					en_req_free += state.tasks[j].free_energy;
				} else {
					// The free part of `j` is forced into the window from the right.
					let dur_shift = cmp::max(end - state.tasks[j].lst_ef, 0);
					en_req_free += state.tasks[j].usage * dur_shift;
					// Extra energy `j` would need in the window if started at est_j.
					let en_req_start = cmp::min(
						state.tasks[j].free_energy,
						state.tasks[j].usage * (end - state.tasks[j].est),
					) - state.tasks[j].usage * dur_shift;
					if en_req_start > max_en_req_start {
						max_en_req_start = en_req_start;
						iota = Some(j);
					}
				}
				let en_req =
					en_req_free + state.tasks[j].tt_after_est - state.tasks[i].tt_after_lct;
				let en_avail = state.capacity * (end - begin) - en_req;
				if en_avail < 0 && Self::window_overloaded(state, begin, end) {
					return Some((begin, end));
				}
				if min_en_avail > en_avail {
					min_en_avail = en_avail;
					min_begin = Some(begin);
				}
				if let Some(u) = iota
					&& en_avail < max_en_req_start
				{
					// Energy of `u` already counted as inside the window.
					let dur_mand =
						cmp::max(cmp::min(state.tasks[u].ect, end) - state.tasks[u].lst, 0);
					let dur_shift = if begin <= state.tasks[u].est {
						cmp::max(end - state.tasks[u].lst - dur_mand, 0)
					} else {
						0
					};
					let en_in = state.tasks[u].usage * (dur_mand + dur_shift);
					// Only `dur_avail` of `u` can fit before `end`, so it must start at
					// `end - dur_avail` at the earliest.
					let dur_avail = (en_avail + en_in) / state.tasks[u].usage;
					let start_new = end - dur_avail;
					if start_new > new_est[u] {
						updates.push(EdgeFindingUpdate {
							task: u,
							begin,
							end,
							is_lb: true,
						});
						new_est[u] = start_new;
					}
				}
			}
		}
		None
	}

	/// Builds the reason for a resource overload in `[begin, end)`: every
	/// contributing task pinned to its start-time bounds, plus its duration and
	/// usage lower bounds and the capacity upper bound.
	fn explain_edge_finding_overload<'a, Ctx>(
		&'a self,
		state: &'a EdgeFindingState,
		begin: IntVal,
		end: IntVal,
	) -> impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>) + 'a
	where
		Ctx: PropagationContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx, reason| {
			for (i, task) in state.tasks.iter().enumerate() {
				if Self::contributes(task, begin, end) {
					reason.push(self.start_times[i].min_lit(ctx));
					reason.push(self.start_times[i].max_lit(ctx));
					reason.push(self.durations[i].min_lit(ctx));
					reason.push(self.usages[i].min_lit(ctx));
				}
			}
			reason.push(self.capacity.max_lit(ctx));
		}
	}

	/// Builds the reason for a bounds-filtering update of task `u` from window
	/// `[begin, end)`: the other contributing tasks pinned to their start-time
	/// bounds, `u` pinned on the side opposite the update, plus the duration
	/// and usage lower bounds and the capacity upper bound.
	fn explain_edge_finding_update<'a, Ctx>(
		&'a self,
		state: &'a EdgeFindingState,
		u: usize,
		begin: IntVal,
		end: IntVal,
		is_lb: bool,
	) -> impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>) + 'a
	where
		Ctx: PropagationContext + ?Sized,
		I1: IntDecisionActions<Ctx>,
		I2: IntDecisionActions<Ctx>,
		I3: IntDecisionActions<Ctx>,
		I4: IntDecisionActions<Ctx>,
	{
		move |ctx, reason| {
			for (i, task) in state.tasks.iter().enumerate() {
				if i == u || !Self::contributes(task, begin, end) {
					continue;
				}
				reason.push(self.start_times[i].min_lit(ctx));
				reason.push(self.start_times[i].max_lit(ctx));
				reason.push(self.durations[i].min_lit(ctx));
				reason.push(self.usages[i].min_lit(ctx));
			}
			// The updated task contributes only the bound on the side from which it
			// is being pushed (its previous earliest start for a lower-bound update,
			// or its previous latest start for an upper-bound update).
			if is_lb {
				reason.push(self.start_times[u].min_lit(ctx));
			} else {
				reason.push(self.start_times[u].max_lit(ctx));
			}
			reason.push(self.durations[u].min_lit(ctx));
			reason.push(self.usages[u].min_lit(ctx));
			reason.push(self.capacity.max_lit(ctx));
		}
	}

	/// Minimum energy `task` is forced to place inside `[begin, end)` over
	/// every placement allowed by its bounds.
	fn forced_energy(task: &EdgeFindingData, begin: IntVal, end: IntVal) -> IntVal {
		let overlap = |s: IntVal| cmp::max(cmp::min(s + task.dur, end) - cmp::max(s, begin), 0);
		task.usage * cmp::min(overlap(task.est), overlap(task.lst))
	}

	/// Latest-completion-time filtering: for each task interval `[begin, end)`
	/// lowers the latest completion of the task overlapping it on the left
	/// that cannot fit, appending the updates.
	fn lct_filtering(
		state: &EdgeFindingState,
		opportunistic: bool,
		updates: &mut Vec<EdgeFindingUpdate>,
	) -> Option<(IntVal, IntVal)> {
		let mut new_est: Vec<IntVal> = state.tasks.iter().map(|t| t.est).collect();
		let mut new_lct: Vec<IntVal> = state.tasks.iter().map(|t| t.lct).collect();
		let horizon_energy = state.capacity
			* (state.tasks[*state.by_lct.last().unwrap()].lct - state.tasks[state.by_est[0]].est);
		let mut prev_begin: Option<IntVal> = None;
		for &i in state.by_est.iter() {
			if state.tasks[i].energy == 0 {
				continue;
			}
			let begin = state.tasks[i].est;
			if prev_begin == Some(begin) {
				continue;
			}
			prev_begin = Some(begin);

			let mut en_req_free = 0;
			let mut max_en_req_end = -1;
			let mut iota: Option<usize> = None;
			// Minimum available energy and the end achieving it, for the
			// opportunistic extended-edge-finding lower-bound update.
			let mut min_en_avail = horizon_energy;
			let mut min_end: Option<IntVal> = None;
			for &j in state.by_lct.iter() {
				let end = state.tasks[j].lct;
				if end <= begin || state.tasks[j].energy == 0 {
					continue;
				}

				// Opportunistic extended edge finding (Vilím (2011), through/left): if
				// the tightest window `[begin, min_end)` seen so far cannot fit all of
				// `j`, raise its earliest start accordingly.
				if opportunistic && let Some(me) = min_end {
					let min_en_in = state.tasks[j].usage
						* cmp::max(
							cmp::min(me, state.tasks[j].ect) - cmp::max(begin, state.tasks[j].lst),
							0,
						);
					let full = state.tasks[j].usage
						* (cmp::min(me, state.tasks[j].ect) - cmp::max(begin, state.tasks[j].est));
					if min_en_avail + min_en_in < full {
						let dur_avail = (min_en_avail + min_en_in) / state.tasks[j].usage;
						let est_new = me - dur_avail;
						if est_new > new_est[j] {
							updates.push(EdgeFindingUpdate {
								task: j,
								begin,
								end: me,
								is_lb: true,
							});
							new_est[j] = est_new;
						}
					}
				}

				if begin <= state.tasks[j].est {
					en_req_free += state.tasks[j].free_energy;
				} else {
					// The free part of `j` is forced into the window from the left.
					let dur_shift = if end >= state.tasks[j].lct {
						cmp::max(state.tasks[j].ect - begin - state.tasks[j].fixed_dur, 0)
					} else {
						0
					};
					en_req_free += state.tasks[j].usage * dur_shift;
					let en_req_end = cmp::min(
						state.tasks[j].free_energy,
						state.tasks[j].usage * (state.tasks[j].lct - begin),
					) - state.tasks[j].usage * dur_shift;
					if en_req_end > max_en_req_end {
						max_en_req_end = en_req_end;
						iota = Some(j);
					}
				}
				let en_req =
					en_req_free + state.tasks[i].tt_after_est - state.tasks[j].tt_after_lct;
				let en_avail = state.capacity * (end - begin) - en_req;
				if en_avail < 0 && Self::window_overloaded(state, begin, end) {
					return Some((begin, end));
				}
				if min_en_avail > en_avail {
					min_en_avail = en_avail;
					min_end = Some(end);
				}
				if let Some(u) = iota
					&& en_avail < max_en_req_end
				{
					let dur_mand =
						cmp::max(state.tasks[u].ect - cmp::max(begin, state.tasks[u].lst), 0);
					let dur_shift = if end >= state.tasks[u].lct {
						cmp::max(state.tasks[u].ect - begin - dur_mand, 0)
					} else {
						0
					};
					let en_in = state.tasks[u].usage * (dur_mand + dur_shift);
					let dur_avail = (en_avail + en_in) / state.tasks[u].usage;
					let end_new = begin + dur_avail;
					if end_new < new_lct[u] {
						updates.push(EdgeFindingUpdate {
							task: u,
							begin,
							end,
							is_lb: false,
						});
						new_lct[u] = end_new;
					}
				}
			}
		}
		None
	}

	/// The energy of the time-table profile in `[tau, +inf)`, looked up in the
	/// table that [`Self::build_profile_energy`] built for the current profile.
	fn profile_energy_after(&self, profile_energy: &[IntVal], tau: IntVal) -> IntVal {
		// Index of the profile segment `[bounds[i], bounds[i + 1])` that holds
		// `tau`; the profile carries no energy before its first bound.
		let Some(i) = self.bounds.partition_point(|&b| b <= tau).checked_sub(1) else {
			return profile_energy.first().copied().unwrap_or(0);
		};
		if i + 1 == self.bounds.len() {
			// The profile ends at its last bound, and so carries no energy there.
			return 0;
		}
		profile_energy[i] - self.heights[i] * (tau - self.bounds[i])
	}

	/// Runs the enabled edge-finding phases (overload check, bounds
	/// filtering, and opportunistic edge finding) on top of the time-table
	/// profile. Returns `Ok(true)` if a bound was updated.
	pub(super) fn propagate_edge_finding<E>(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<bool, E::Conflict>
	where
		E: ReasoningEngine,
		I1: IntSolverActions<E>,
		I2: IntSolverActions<E>,
		I3: IntSolverActions<E>,
		I4: IntSolverActions<E>,
	{
		if self.start_times.len() < 2 {
			return Ok(false);
		}
		let profile_energy = self.build_profile_energy();
		let state = self.edge_finding_data::<E>(ctx, &profile_energy);

		// Bounds filtering subsuming the consistency check: its sweeps also detect
		// resource overloads. When only the check is enabled, run the cheaper
		// consistency check on its own.
		if self.edge_finding_propagation_enabled {
			let opp = self.opportunistic_edge_finding_propagation_enabled;
			let mut updates = Vec::new();
			if let Some((begin, end)) = Self::est_filtering(&state, opp, &mut updates) {
				trace!(target: "cumulative", window =? (begin, end), "edge-finding resource overload");
				return Err(
					ctx.declare_conflict(self.explain_edge_finding_overload(&state, begin, end))
				);
			}
			if let Some((begin, end)) = Self::lct_filtering(&state, opp, &mut updates) {
				trace!(target: "cumulative", window =? (begin, end), "edge-finding resource overload");
				return Err(
					ctx.declare_conflict(self.explain_edge_finding_overload(&state, begin, end))
				);
			}
			let mut propagated = false;
			for upd in &updates {
				// Re-derive the bound from the forced energy of the other tasks the
				// reason pins, so the naive edge-finding explanation provably entails it.
				let Some(bound) =
					Self::sound_update_bound(&state, upd.task, upd.begin, upd.end, upd.is_lb)
				else {
					continue;
				};
				let reason = self
					.explain_edge_finding_update(&state, upd.task, upd.begin, upd.end, upd.is_lb);
				if upd.is_lb {
					self.start_times[upd.task].tighten_min(ctx, bound, reason)?;
				} else {
					self.start_times[upd.task].tighten_max(ctx, bound, reason)?;
				}
				propagated = true;
			}
			return Ok(propagated);
		}

		// Consistency check: detect a task interval whose required energy
		// exceeds the available resource energy.
		if self.energy_overload_check_enabled
			&& let Some((begin, end)) = Self::consistency_check(&state)
		{
			trace!(target: "cumulative", window =? (begin, end), "edge-finding resource overload");
			return Err(
				ctx.declare_conflict(self.explain_edge_finding_overload(&state, begin, end))
			);
		}

		Ok(false)
	}

	/// Re-derives a sound start-time bound for a queued update of task `u` from
	/// the forced energy of the other contributing tasks and the capacity.
	/// Returns the new earliest start (`is_lb`) or latest start, or `None` when
	/// the pinned energy justifies no tighter bound.
	fn sound_update_bound(
		state: &EdgeFindingState,
		u: usize,
		begin: IntVal,
		end: IntVal,
		is_lb: bool,
	) -> Option<IntVal> {
		let mut en_others = 0;
		for (i, task) in state.tasks.iter().enumerate() {
			if i != u && Self::contributes(task, begin, end) {
				en_others += Self::forced_energy(task, begin, end);
			}
		}
		let en_avail = state.capacity * (end - begin) - en_others;
		if en_avail < 0 {
			return None;
		}
		let task = &state.tasks[u];
		let dur_avail = en_avail / task.usage;
		let overlap = |s: IntVal| cmp::max(cmp::min(s + task.dur, end) - cmp::max(s, begin), 0);
		if is_lb {
			// `u` placed at its earliest start cannot fit in the energy left for
			// it, so any feasible start lies at or after `end - dur_avail`.
			if overlap(task.est) <= dur_avail {
				return None;
			}
			let start_new = end - dur_avail;
			(start_new > task.est).then_some(start_new)
		} else {
			// Symmetric: `u` placed at its latest start cannot fit, so its latest
			// completion is at most `begin + dur_avail`, bounding its latest start.
			if overlap(task.lst) <= dur_avail {
				return None;
			}
			let start_new = begin + dur_avail - task.dur;
			(start_new < task.lst).then_some(start_new)
		}
	}

	/// Whether the energy all tasks are forced to place inside `[begin, end)`
	/// exceeds the available resource energy `R * (end - begin)`.
	fn window_overloaded(state: &EdgeFindingState, begin: IntVal, end: IntVal) -> bool {
		let forced: IntVal = state
			.tasks
			.iter()
			.map(|task| Self::forced_energy(task, begin, end))
			.sum();
		forced > state.capacity * (end - begin)
	}
}

#[cfg(test)]
mod tests {
	use std::cmp;

	use expect_test::expect;
	use itertools::Itertools;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		actions::IntInspectionActions,
		constraints::cumulative::CumulativePropagator,
		solver::{LiteralStrategy, Solver, View},
	};

	/// Every edge-finding configuration.
	const ALL_CONFIGS: [EdgeFindingConfig; 4] = [TT, CHECK_ONLY, FILTER, FILTER_OPP];
	/// Only the consistency check.
	const CHECK_ONLY: EdgeFindingConfig = (true, false, false);
	/// The consistency check and bounds filtering.
	const FILTER: EdgeFindingConfig = (true, true, false);
	/// All phases including the opportunistic extended edge finding.
	const FILTER_OPP: EdgeFindingConfig = (true, true, true);
	/// No edge-finding phases: pure time-table propagation.
	const TT: EdgeFindingConfig = (false, false, false);

	/// An edge-finding configuration as `(check, filtering, opportunistic)`.
	type EdgeFindingConfig = (bool, bool, bool);

	/// Cross-configuration soundness oracle: every edge-finding
	/// configuration must enumerate the identical solution set (sound
	/// propagation changes search speed, not solutions). Instance: the two
	/// overlapping resources from `test_cumulative_val_sat`.
	#[test]
	#[traced_test]
	fn test_edge_finding_cross_config_solution_set() {
		for (check, filtering, opportunistic) in ALL_CONFIGS {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let c = slv
				.new_int_decision(0..=4)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let durations: Vec<View<IntVal>> = [2, 3, 1].into_iter().map_into().collect();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, c],
				durations.clone(),
				vec![1, 2, 3],
				3,
				check,
				filtering,
				opportunistic,
			);
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, c],
				durations,
				vec![2, 2, 1],
				2,
				check,
				filtering,
				opportunistic,
			);

			slv.expect_solutions(
				&[a, b, c],
				expect![[r#"
    0, 3, 2
    0, 4, 2
    0, 4, 3
    1, 3, 0
    1, 4, 0
    1, 4, 3
    2, 4, 0
    2, 4, 1
    4, 0, 3
    4, 1, 0"#]],
			);
		}
	}

	/// The edge-finding consistency check detects an energy overload
	/// that pure time-tabling misses.
	#[test]
	#[traced_test]
	fn test_edge_finding_energy_overload_check() {
		let make = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut slv = Solver::default();
			let starts = (0..3)
				.map(|_| {
					slv.new_int_decision(0..=2)
						.order_literals(LiteralStrategy::Eager)
						.view()
				})
				.collect_vec();
			CumulativePropagator::post(
				&mut slv,
				starts,
				vec![2, 2, 2],
				vec![1, 1, 1],
				1,
				check,
				filtering,
				opportunistic,
			);
			slv
		};

		let mut tt = make(TT);
		assert!(tt.propagate_next().is_ok());

		let mut checked = make(CHECK_ONLY);
		assert!(checked.propagate_next().is_err());
	}

	/// Edge-finding bounds filtering lifts an earliest start that
	/// time-tabling cannot.
	#[test]
	#[traced_test]
	fn test_edge_finding_filtering_lifts_earliest_start() {
		let make = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=2)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=2)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(0..=8)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![2, 2, 2],
				vec![2, 2, 2],
				2,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};

		let (mut tt, u) = make(TT);
		let _ = tt.propagate_next();
		assert!(u.in_domain(&tt, 0));

		let (mut filtered, u) = make(FILTER);
		let _ = filtered.propagate_next();
		assert!(!u.in_domain(&filtered, 3));
		assert!(u.in_domain(&filtered, 4));
	}

	/// Edge-finding bounds filtering lowers a latest completion time that
	/// time-tabling cannot.
	#[test]
	#[traced_test]
	fn test_edge_finding_filtering_lowers_latest_completion() {
		let make = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(4..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(4..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![2, 2, 2],
				vec![2, 2, 2],
				2,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};

		let (mut tt, u) = make(TT);
		let _ = tt.propagate_next();
		assert!(u.in_domain(&tt, 6));

		let (mut filtered, u) = make(FILTER);
		let _ = filtered.propagate_next();
		assert!(!u.in_domain(&filtered, 3));
		assert!(u.in_domain(&filtered, 2));
	}

	/// The opportunistic phase is at least as strong as plain edge finding
	/// and stays sound.
	#[test]
	#[traced_test]
	fn test_edge_finding_opportunistic_extended_edge_finding() {
		let make = |(check, filtering, opportunistic): EdgeFindingConfig| {
			let mut slv = Solver::default();
			let a = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=6)
				.order_literals(LiteralStrategy::Eager)
				.view();
			let u = slv
				.new_int_decision(1..=5)
				.order_literals(LiteralStrategy::Eager)
				.view();
			CumulativePropagator::post(
				&mut slv,
				vec![a, b, u],
				vec![4, 4, 4],
				vec![2, 2, 1],
				3,
				check,
				filtering,
				opportunistic,
			);
			(slv, u)
		};

		let (mut filtered, u1) = make(FILTER);
		let _ = filtered.propagate_next();
		let (mut opportunistic, u2) = make(FILTER_OPP);
		let _ = opportunistic.propagate_next();
		for v in 0..=5 {
			if !u1.in_domain(&filtered, v) {
				assert!(
					!u2.in_domain(&opportunistic, v),
					"the opportunistic phase must remove every value plain edge finding removed (value {v})"
				);
			}
		}
	}

	/// The lookup must agree with a direct scan over the profile at every time
	/// point, including the segment borders and the ends of the profile.
	#[test]
	fn test_edge_finding_profile_energy_after() {
		let mut prop: CumulativePropagator<View<IntVal>, View<IntVal>, View<IntVal>, View<IntVal>> =
			CumulativePropagator::new(
				Vec::new(),
				Vec::new(),
				Vec::new(),
				0.into(),
				false,
				false,
				false,
			);
		// Segments `[0, 2)`, `[2, 5)`, and `[5, 9)` carrying 3, 1, and 2 units of
		// the resource, and the closing bound of the profile.
		prop.bounds = vec![0, 2, 5, 9];
		prop.heights = vec![3, 1, 2, 0];
		let profile_energy = prop.build_profile_energy();

		// The direct scan the lookup replaces.
		let scan = |tau: IntVal| -> IntVal {
			(0..prop.bounds.len() - 1)
				.map(|i| {
					prop.heights[i]
						* cmp::max(prop.bounds[i + 1] - cmp::max(prop.bounds[i], tau), 0)
				})
				.sum()
		};
		for tau in -2..=12 {
			assert_eq!(
				prop.profile_energy_after(&profile_energy, tau),
				scan(tau),
				"at {tau}"
			);
		}
		assert_eq!(prop.profile_energy_after(&profile_energy, 0), 17);
		assert_eq!(prop.profile_energy_after(&profile_energy, 9), 0);

		// An empty profile carries no energy anywhere.
		prop.bounds.clear();
		prop.heights.clear();
		let profile_energy = prop.build_profile_energy();
		assert_eq!(prop.profile_energy_after(&profile_energy, 0), 0);
	}
}
