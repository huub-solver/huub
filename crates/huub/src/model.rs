//! The modelling layer for constructing, simplifying, and lowering problem
//! instances.

pub(crate) mod decision;
pub mod deserialize;
pub mod expressions;
pub(crate) mod initilization_context;
pub(crate) mod resolved;
pub(crate) mod view;

use std::{
	fmt::Debug,
	hash::Hash,
	iter::{repeat_n, repeat_with},
	marker::PhantomData,
	mem,
};

use pindakaas::{ClauseDatabaseTools, Cnf};
use rangelist::IntervalIterator;
use rustc_hash::FxHashMap;

pub use crate::model::{
	decision::{Decision, DecisionReference},
	view::{DefaultView, View},
};
use crate::{
	IntSet, IntVal,
	actions::{
		ConstructionActions, DecisionActions, DeferReasonActions, IntEvent, IntInspectionActions,
		PropagationActions, PropagationContext, ReasonActions, ReasoningContext, ReasoningEngine,
		SimplificationActions, Trailed, TrailingActions,
	},
	constraints::{
		BoxedConstraint, Conflict, ConflictInner, Constraint, Nogood, SimplificationStatus,
	},
	helpers::bytes::Bytes,
	lower::{Lowerer, LowererComplete},
	model::{
		decision::{PolarityScore, Tier, boolean::BoolDecision, integer::IntDecision},
		initilization_context::ModelInitContext,
		view::{boolean::BoolView, integer::IntView},
	},
	solver::{
		IntLitMeaning, Polarity,
		activation_list::ActivationAction,
		proof::ConstraintSource,
		queue::{PropagatorInfo, PropagatorQueue},
	},
};

/// Identifies an advisor in the [`Model`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AdvRef(u32);

/// Definition of how a constraint has requested to be advised at the model
/// level.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Advisor {
	/// Reference to the constraint that has requested to be advised.
	con: ConRef,
	/// The data associated by the constraint with the advisor.
	data: u64,
	/// Whether lower and upper bound events must be swapped.
	negated: bool,
	/// Whether advice on a Boolean view must be converted to an integer event.
	bool2int: bool,
	/// The condition on the integer decision variable that must be decided
	/// before the constraint is advised.
	condition: Option<IntLitMeaning>,
}

/// Identifies a constraint in the [`Model`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ConRef(u32);

/// A formulation of a problem instance in terms of decisions and constraints.
///
/// A [`Model`] is the construction and simplification layer of Huub. It stores
/// decision variables, constraints, aliases, and simplifications, but it does
/// not perform search itself. Search starts after the model is converted to a
/// [`Solver`](crate::solver::Solver) with [`Self::lower`].
///
/// After lowering, values in a solution should be queried through the solver
/// views returned by the [`LoweringMap`](crate::lower::LoweringMap).
///
/// ```
/// # use huub::{
/// # 	model::Model,
/// # 	solver::{Solver, Status, Valuation},
/// # };
/// let mut model = Model::default();
/// let x = model.new_int_decision(1..=3);
/// let y = model.new_int_decision(1..=3);
///
/// model.linear(x + y).eq(4).post();
///
/// let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
/// # let x = map.get(&mut solver, x);
/// # let y = map.get(&mut solver, y);
/// # let mut pair = None;
/// # let status = solver
/// # 	.solve()
/// # 	.on_solution(|solution| {
/// # 		pair = Some((x.val(solution), y.val(solution)));
/// # 	})
/// # 	.satisfy();
/// # assert_eq!(status, Status::Satisfied);
/// # let (x, y) = pair.unwrap();
/// # assert_eq!(x + y, 4);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug, Default)]
pub struct Model {
	/// A base [`Cnf`] object that contains pure Boolean parts of the problem.
	pub(crate) cnf: Cnf,
	/// A list of constraints that have been added to the model.
	pub(crate) constraints: Vec<Option<BoxedConstraint>>,
	/// The provenance of each constraint in [`Self::constraints`], used to
	/// label clauses when proof logging is enabled.
	///
	/// This storage is kept in lockstep with [`Self::constraints`].
	pub(crate) provenance: Vec<Option<ConstraintSource>>,
	/// The provenance that will be attached to the next constraint posted to
	/// the model.
	///
	/// This register is sticky: it is read (but not consumed) when a constraint
	/// is posted, allowing a batch of constraints stemming from the same source
	/// to be labelled by setting the register once.
	next_provenance: Option<ConstraintSource>,
	/// The definitions of the Boolean decision variables that have been
	/// created.
	pub(crate) bool_vars: Vec<BoolDecision>,
	/// The definitions of the integer decision variables that have been
	/// created.
	pub(crate) int_vars: Vec<IntDecision>,
	/// A queue of constraints that need to be propagated.
	propagator_queue: PropagatorQueue,
	/// Fake trailed storage
	pub(crate) trail: Vec<[u8; 8]>,
	/// Reference for the current propagator being executed.
	cur_prop: Option<ConRef>,
	/// Integer variable changes that occurred during the execution of the
	/// current propagator.
	int_events: FxHashMap<u32, IntEvent>,
	/// Boolean variable changes that occurred during the execution of the
	/// current propagator.
	bool_events: Vec<Decision<bool>>,

	/// Definitions of the advisors that are listening to selected changes.
	advisors: Vec<Advisor>,
}

/// The engine-internal [`PropagationContext`] used while simplifying a
/// [`Model`]'s constraints.
#[derive(Debug)]
pub struct SimplificationContext<'a>(pub(crate) &'a mut Model);

/// The reason-build sink for a [`SimplificationContext`]: a reason closure
/// either collects the reason atoms into `conditions`, or defers the reason to
/// the current propagator via [`DeferReasonActions::defer`].
///
/// Unlike the user-facing [`Model`] reason sink, this sink implements
/// [`DeferReasonActions`], so only constraint reasons can defer.
#[derive(Debug, Default)]
pub struct SimplificationReasonSink {
	/// The reason atoms pushed so far.
	pub(crate) conditions: Vec<View<bool>>,
	/// `Some(data)` once the reason has been deferred; the propagator index is
	/// folded in by the caller.
	pub(crate) deferred: Option<u64>,
}

impl AdvRef {
	/// Recreate the advisor reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the advisor vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new advisor reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index < i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the advisor reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}

impl ConRef {
	/// Recreate the constraint reference from a raw value.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Get the index into the constraint vector.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new constraint reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index < i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the constraint reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}

impl Model {
	/// Adapt a reason closure written against the user-facing [`Model`] into
	/// one usable within a [`SimplificationContext`]. The model closure cannot
	/// defer, so nothing is lost.
	pub(crate) fn adapt_reason<'a>(
		reason: impl FnOnce(&mut Model, &mut Vec<View<bool>>),
	) -> impl FnOnce(&mut SimplificationContext<'a>, &mut SimplificationReasonSink) {
		move |ctx, sink| reason(&mut *ctx.0, &mut sink.conditions)
	}

	/// Notify a single boolean advisor or propagator.
	fn advise_of_bool_change(&mut self, con: ConRef, data: u64) -> bool {
		if let Some(mut c) = self.constraints[con.index()].take() {
			let ret = c.advise_of_bool_change(self, data);
			self.constraints[con.index()] = Some(c);
			ret
		} else {
			false
		}
	}

	/// Notify a single integer advisor or propagator.
	fn advise_of_int_change(&mut self, con: ConRef, data: u64, event: IntEvent) -> bool {
		if let Some(mut c) = self.constraints[con.index()].take() {
			let ret = c.advise_of_int_change(self, data, event);
			self.constraints[con.index()] = Some(c);
			ret
		} else {
			false
		}
	}

	/// Initialize a constraint and register its subscriptions without
	/// propagating it yet.
	///
	/// This is used by [`Model::post_constraint`] and by internal rewriting
	/// paths that need to add a constraint before deciding whether to
	/// propagate it immediately.
	fn initialize_constraint<C: Constraint<Self>>(&mut self, constraint: C) -> (ConRef, bool) {
		// Determine the provenance of the new constraint: either the current
		// `next_provenance` register, or — when a constraint is rewritten during
		// propagation — the provenance of the constraint that posted it.
		let provenance = self.next_provenance.or_else(|| {
			self.cur_prop
				.and_then(|c| self.provenance.get(c.index()).copied().flatten())
		});
		let con = ConRef::new(self.constraints.len());
		let mut ctx = ModelInitContext::new(self, con);
		let mut constraint = constraint;
		constraint.initialize(&mut ctx);
		let priority = ctx.priority;
		let enqueue = ctx.enqueue();
		self.constraints.push(Some(Box::new(constraint)));
		self.provenance.push(provenance);
		debug_assert_eq!(self.constraints.len(), self.provenance.len());
		let r = ConRef::new(self.constraints.len() - 1);
		debug_assert_eq!(r, con);
		self.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(r.index(), self.propagator_queue.info.len() - 1);
		(con, enqueue)
	}

	/// Returns a builder that can be used to lower the [`Model`] to a
	/// [`Solver`](crate::solver::Solver) (via
	/// [`to_solver()`](Lowerer::to_solver)).
	///
	/// The builder allows configuring various SAT solver options and
	/// preprocessing techniques before starting the lowering process.
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// # let x = model.new_int_decision(1..=3);
	/// let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	/// let x = map.get(&mut solver, x);
	///
	/// solver.solve().satisfy();
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
	pub fn lower(&mut self) -> Lowerer<&'_ mut Model> {
		LowererComplete::builder_internal(self)
	}

	/// Create a new Boolean variable.
	pub fn new_bool_decision(&mut self) -> View<bool> {
		let var: Decision<bool> = Decision(self.cnf.new_lit());
		self.bool_vars.push(BoolDecision {
			alias: None,
			constraints: Vec::new(),
			polarity: PolarityScore::default(),
		});
		debug_assert_eq!(var.idx(), self.bool_vars.len() - 1);
		var.into()
	}

	/// Create `len` new Boolean decision variables.
	pub fn new_bool_decisions(&mut self, len: usize) -> Vec<View<bool>> {
		repeat_with(|| self.new_bool_decision()).take(len).collect()
	}

	/// Create a new integer decision variable with the given domain.
	///
	/// The domain describes the values the decision variable may take before
	/// propagation and search. If the domain contains exactly one value, Huub
	/// returns a constant view instead of allocating a solver decision.
	///
	/// ```
	/// # use huub::model::Model;
	/// # let mut model = Model::default();
	/// let digit = model.new_int_decision(0..=9);
	/// let non_zero_digit = model.new_int_decision(1..=9);
	///
	/// model.linear(digit + non_zero_digit).le(18).post();
	/// ```
	pub fn new_int_decision(&mut self, domain: impl Into<IntSet>) -> View<IntVal> {
		let domain = domain.into();
		match domain.card() {
			Some(0) => {
				panic!("integer decision must have at least 1 value in their domain")
			}
			Some(1) => (*domain.min().unwrap()).into(),
			_ => {
				self.int_vars.push(IntDecision::with_domain(domain));
				let idx = self.int_vars.len() - 1;
				Decision(idx as u32).into()
			}
		}
	}

	/// Create `len` new integer variables with the given domain.
	pub fn new_int_decisions(
		&mut self,
		len: usize,
		domain: impl Into<IntSet>,
	) -> Vec<View<IntVal>> {
		let domain = domain.into();
		repeat_n(IntDecision::with_domain(domain), len)
			.map(|v| {
				self.int_vars.push(v);
				let idx = self.int_vars.len() - 1;
				Decision(idx as u32).into()
			})
			.collect()
	}

	/// Notify propagators of the changes that happened since the last call to
	/// this method.
	pub(crate) fn notify_advisors(&mut self) {
		let mut int_events = mem::take(&mut self.int_events);
		for (i, event) in int_events.drain() {
			self.notify_int_event(i, event);
		}
		self.int_events = int_events;
		let mut bool_events = mem::take(&mut self.bool_events);
		for bv in bool_events.drain(..) {
			self.notify_bool_event(bv);
		}
		self.bool_events = bool_events;
	}

	/// Notify the propagators interested in a single boolean event.
	pub(crate) fn notify_bool_event(&mut self, bv: Decision<bool>) {
		debug_assert!(!bv.is_negated());
		for &act in self.bool_vars[bv.idx()].constraints.clone().iter() {
			match act.into() {
				ActivationAction::Advise::<AdvRef, _>(adv) => {
					let x: &Advisor = &self.advisors[adv.index()];
					let Advisor {
						con,
						data,
						bool2int,
						..
					} = x.clone();
					let enqueue = if bool2int {
						self.advise_of_int_change(con, data, IntEvent::Fixed)
					} else {
						self.advise_of_bool_change(con, data)
					};
					if enqueue {
						self.propagator_queue.enqueue_propagator(con.raw());
					}
				}
				ActivationAction::Enqueue(c) => {
					self.propagator_queue.enqueue_propagator(c.raw());
				}
			}
		}
	}

	/// Notify the propagators interested in a single integer event.
	pub(crate) fn notify_int_event(&mut self, i: u32, event: IntEvent) {
		let constraints = mem::take(&mut self.int_vars[i as usize].constraints);
		let iv = Decision(i);
		constraints.for_each_activated_by(event, |act| match act {
			ActivationAction::Advise::<AdvRef, _>(adv) => {
				let x: &Advisor = &self.advisors[adv.index()];
				let Advisor {
					con,
					data,
					negated,
					bool2int,
					condition,
				} = x.clone();
				let event = match event {
					IntEvent::LowerBound if negated => IntEvent::UpperBound,
					IntEvent::UpperBound if negated => IntEvent::LowerBound,
					_ => event,
				};
				let enqueue = if let Some(cond) = condition {
					let triggered = match cond {
						IntLitMeaning::Eq(_) | IntLitMeaning::NotEq(_) => iv.val(self).is_some(),
						IntLitMeaning::GreaterEq(v) | IntLitMeaning::Less(v) => {
							let (min, max) = iv.bounds(self);
							v <= min || v > max
						}
					};
					if triggered {
						if bool2int {
							self.advise_of_int_change(con, data, IntEvent::Fixed)
						} else {
							self.advise_of_bool_change(con, data)
						}
					} else {
						false
					}
				} else {
					self.advise_of_int_change(con, data, event)
				};
				if enqueue {
					self.propagator_queue.enqueue_propagator(con.raw());
				}
			}
			ActivationAction::Enqueue(c) => self.propagator_queue.enqueue_propagator(c.raw()),
		});
		self.int_vars[i as usize].constraints = constraints;
	}

	/// Record one unit of polarity evidence at the given `tier` stating that
	/// the Boolean `view` should be pushed in direction `polarity` (where
	/// [`Positive`](Polarity::Positive) means "prefer true").
	///
	/// Evidence is only recorded for views backed by a pure Boolean decision;
	/// the literal's negation is folded into the sign.
	pub(crate) fn observe_bool_polarity(
		&mut self,
		view: View<bool>,
		tier: Tier,
		polarity: Polarity,
	) {
		if let BoolView::Decision(l) = view.resolve_alias(self).into_inner().0 {
			// A negated literal flips the desired direction onto the variable.
			let polarity = if l.is_negated() { !polarity } else { polarity };
			self.bool_vars[l.idx()].polarity.observe(tier, polarity);
		}
	}

	/// Record one unit of polarity evidence at the given `tier` stating that
	/// the integer `view` should be pushed in direction `polarity`. The view's
	/// scale sign (and any Boolean negation) is folded onto the underlying
	/// decision.
	pub(crate) fn observe_int_polarity(
		&mut self,
		view: View<IntVal>,
		tier: Tier,
		polarity: Polarity,
	) {
		match view.resolve_alias(self).into_inner().0 {
			IntView::Linear(lin) => {
				let polarity = if lin.scale.get() < 0 {
					!polarity
				} else {
					polarity
				};
				self.int_vars[lin.var.idx()]
					.polarity
					.observe(tier, polarity);
			}
			IntView::Bool(lin) => {
				let polarity = if lin.scale.get() < 0 {
					!polarity
				} else {
					polarity
				};
				self.observe_bool_polarity(lin.var, tier, polarity);
			}
			IntView::Const(_) => {}
		}
	}

	/// Post a constraint to the model.
	///
	/// The constraint is added to the model. It will be enforced during
	/// simplification and in any subsequent solving method.
	pub fn post_constraint<C: Constraint<Self>>(
		&mut self,
		constraint: C,
	) -> Result<(), Nogood<View<bool>>> {
		let (con, enqueue) = self.initialize_constraint(constraint);
		if enqueue {
			self.propagate_single(con)?;
		}
		Ok(())
	}

	/// Internal implementation of [`Model::post_constraint`] that does not yet
	/// propagate.
	///
	/// This function is used internally by [`Model::post_constraint`] and when
	/// rewriting constraints within the propagation loop.
	pub(crate) fn post_constraint_internal<C: Constraint<Self>>(&mut self, constraint: C) {
		let (con, enqueue) = self.initialize_constraint(constraint);
		if enqueue {
			self.propagator_queue.enqueue_propagator(con.raw());
		}
	}

	/// Propagate all constraints until the propagator queue is empty.
	///
	/// This method performs fixed-point iteration of all constraints currently
	/// in the propagator queue. It will continue to propagate until no more
	/// changes can be made to the domains of the decision variables, or until
	/// an inconsistency is found.
	///
	/// Note that Huub performs propagation automatically during the lowering
	/// process (see [`Self::lower`]). You generally only need to call this
	/// method manually if you want to inspect the results of propagation
	/// (e.g. decision variable domains) during the modeling process.
	pub fn propagate(&mut self) -> Result<(), Nogood<View<bool>>> {
		self.notify_advisors();
		while let Some(con) = self.propagator_queue.pop() {
			self.propagate_single(ConRef::from_raw(con))?;
		}
		Ok(())
	}

	/// Propagate the constraint at index `con`, updating the domains of the
	/// variables and rewriting the constraint if necessary.
	pub(crate) fn propagate_single(&mut self, con: ConRef) -> Result<(), Nogood<View<bool>>> {
		let Some(mut con_obj) = self.constraints[con.index()].take() else {
			return Ok(());
		};
		self.cur_prop = Some(con);
		let mut status = con_obj.simplify(&mut SimplificationContext(&mut *self));
		self.cur_prop = None;

		// Resolve a deferred conflict's clause while the propagator is available.
		if let Err(Conflict(ConflictInner::Deferred {
			subject,
			propagator,
			data,
		})) = status
		{
			debug_assert_eq!(ConRef::new(propagator as usize), con);
			let mut conj = Vec::new();
			con_obj.explain(self, subject.unwrap_or(false.into()), data, &mut conj);
			// Fold the subject in as the clause head.
			if let Some(subject) = subject {
				conj.push(subject);
			}
			status = Err(Conflict(ConflictInner::Clause(conj.into_boxed_slice())));
		};

		match status.map_err(Conflict::into_nogood)? {
			SimplificationStatus::Subsumed => {
				// Constraint is known to be satisfied, no need to place back.
			}
			SimplificationStatus::NoFixpoint => {
				self.constraints[con.index()] = Some(con_obj);
			}
		}
		self.notify_advisors();
		Ok(())
	}

	/// Set the [`ConstraintSource`] that will be attached to the constraints
	/// subsequently posted to the model.
	///
	/// The register is sticky: it remains in effect until it is overwritten or
	/// cleared by setting it to `None`.
	#[cfg_attr(
		not(feature = "flatzinc"),
		expect(dead_code, reason = "only used by the `flatzinc` deserializer")
	)]
	pub(crate) fn set_next_provenance(&mut self, provenance: Option<ConstraintSource>) {
		self.next_provenance = provenance;
	}

	/// Invoke `f` with a [`ConRef`] for each constraint that the given integer
	/// decision is subscribed to (i.e. that may involve it). The same
	/// constraint may be reported more than once.
	pub(crate) fn subscribed_constraints(&self, dec: Decision<IntVal>, mut f: impl FnMut(ConRef)) {
		self.int_vars[dec.idx()].constraints.for_each_activated_by(
			IntEvent::Fixed,
			|act: ActivationAction<AdvRef, ConRef>| {
				let con = match act {
					ActivationAction::Enqueue(con) => con,
					ActivationAction::Advise(adv) => self.advisors[adv.index()].con,
				};
				f(con);
			},
		);
	}
}

impl ConstructionActions for Model {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		self.trail.push(init.to_bytes());
		Trailed {
			index: (self.trail.len() - 1) as u32,
			ty: PhantomData,
		}
	}
}

impl DecisionActions for Model {
	fn num_conflicts(&self) -> u64 {
		0
	}
}

impl PropagationActions for Model {
	fn declare_conflict(
		&mut self,
		reason: impl FnOnce(&mut Self, &mut Self::ReasonSink<'_>),
	) -> Nogood<View<bool>> {
		let mut sink = Vec::new();
		reason(&mut *self, &mut sink);
		Nogood(sink.into())
	}
}

impl PropagationContext for Model {
	type Conflict = Nogood<View<bool>>;
	type ReasonSink<'a> = Vec<View<bool>>;
}

impl ReasoningContext for Model {
	type Atom = <Self as ReasoningEngine>::Atom;
}

impl ReasoningEngine for Model {
	type Atom = View<bool>;

	type Conflict = Conflict<View<bool>>;
	type ExplanationContext<'a> = Self;
	type InitializationContext<'a> = ModelInitContext<'a>;
	type NotificationContext<'a> = Self;
	type PropagationContext<'a> = SimplificationContext<'a>;
	type ReasonSink<'a> = Vec<View<bool>>;
}

impl SimplificationActions for Model {
	type Target = Model;

	fn post_constraint<C: Constraint<Model>>(&mut self, constraint: C) {
		self.post_constraint_internal(constraint);
	}
}

impl TrailingActions for Model {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		T::from_bytes(mem::replace(
			&mut self.trail[i.index as usize],
			v.to_bytes(),
		))
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		T::from_bytes(self.trail[i.index as usize])
	}
}

impl SimplificationContext<'_> {
	/// Create a conflict from the failure to set `subject` (folded in as the
	/// clause head), required by `reason`.
	pub(crate) fn create_conflict(
		&mut self,
		subject: View<bool>,
		reason: impl FnOnce(&mut Self, &mut SimplificationReasonSink),
	) -> Conflict<View<bool>> {
		let mut sink = SimplificationReasonSink::default();
		reason(&mut *self, &mut sink);
		match sink.deferred {
			Some(data) => Conflict(ConflictInner::Deferred {
				subject: Some(subject),
				propagator: self.0.cur_prop.unwrap().index() as u32,
				data,
			}),
			None => {
				// Fold the subject in as the clause head.
				sink.conditions.push(subject);
				Conflict(ConflictInner::Clause(sink.conditions.into_boxed_slice()))
			}
		}
	}
}

impl ConstructionActions for SimplificationContext<'_> {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		self.0.new_trailed(init)
	}
}

impl DecisionActions for SimplificationContext<'_> {
	fn num_conflicts(&self) -> u64 {
		self.0.num_conflicts()
	}
}

impl PropagationActions for SimplificationContext<'_> {
	fn declare_conflict(
		&mut self,
		reason: impl FnOnce(&mut Self, &mut Self::ReasonSink<'_>),
	) -> Conflict<View<bool>> {
		let mut sink = SimplificationReasonSink::default();
		reason(&mut *self, &mut sink);
		match sink.deferred {
			Some(data) => Conflict(ConflictInner::Deferred {
				subject: None,
				propagator: self.0.cur_prop.unwrap().index() as u32,
				data,
			}),
			None => Conflict(ConflictInner::Clause(sink.conditions.into_boxed_slice())),
		}
	}
}

impl PropagationContext for SimplificationContext<'_> {
	type Conflict = Conflict<View<bool>>;
	type ReasonSink<'a> = SimplificationReasonSink;
}

impl ReasoningContext for SimplificationContext<'_> {
	type Atom = View<bool>;
}

impl SimplificationActions for SimplificationContext<'_> {
	type Target = Model;

	fn post_constraint<C: Constraint<Model>>(&mut self, constraint: C) {
		self.0.post_constraint_internal(constraint);
	}
}

impl TrailingActions for SimplificationContext<'_> {
	fn set_trailed<T: Bytes>(&mut self, i: Trailed<T>, v: T) -> T {
		self.0.set_trailed(i, v)
	}

	fn trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		self.0.trailed(i)
	}
}

impl DeferReasonActions<View<bool>> for SimplificationReasonSink {
	fn defer(&mut self, data: u64) {
		self.deferred = Some(data);
	}
}

impl Extend<View<bool>> for SimplificationReasonSink {
	fn extend<T: IntoIterator<Item = View<bool>>>(&mut self, iter: T) {
		self.conditions.extend(iter);
	}
}

impl ReasonActions<View<bool>> for SimplificationReasonSink {
	fn push(&mut self, atom: View<bool>) {
		self.conditions.push(atom);
	}

	fn reserve(&mut self, additional: usize) {
		self.conditions.reserve(additional);
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		IntVal,
		actions::{
			BoolInitActions, BoolInspectionActions, ConstructionActions, IntEvent, IntInitActions,
			IntInspectionActions, IntPropCond, IntPropagationActions, IntSimplificationActions,
			ReasoningEngine, Trailed, TrailingActions,
		},
		constraints::{
			BoolModelActions, Constraint, IntModelActions, NO_REASON, Propagator,
			SimplificationStatus,
		},
		lower::{LoweringContext, LoweringError},
		model::{Model, View, deserialize::AnyView},
		solver::Solver,
	};

	#[derive(Clone, Debug)]
	struct TestModel {
		b: View<bool>,
		i: View<IntVal>,
		bool_check: Trailed<IntVal>,
		int_check: Trailed<IntVal>,
	}

	#[test]
	#[traced_test]
	fn test_inverted_bool() {
		let mut prb = Model::default();
		let b = prb.new_bool_decision();
		let i1 = prb.new_int_decision(-1..=0);
		i1.unify(&mut prb, !b - 1).expect("unify failed");

		let (mut slv, map): (Solver, _) = prb.lower().to_solver().expect("to_solver failed");
		let b_slv = map.get_any(&mut slv, AnyView::from(b));
		let i1_slv = map.get_any(&mut slv, AnyView::from(i1));
		slv.expect_solutions(
			&[b_slv, i1_slv],
			expect![[r#"
			false, 0
			true, -1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_model_advisor_bool_call() {
		let mut prb = Model::default();
		let i = prb.new_int_decision(0..=3);
		let b = i.geq(2);
		let bool_check = prb.new_trailed(0);
		let int_check = prb.new_trailed(0);
		let t = TestModel {
			b,
			i,
			bool_check,
			int_check,
		};
		prb.post_constraint(t).unwrap();
		i.tighten_min(&mut prb, 2, NO_REASON)
			.expect("tighten_min failed");
		let (_, _): (Solver, _) = prb.lower().to_solver().expect("to_solver failed");
		assert_eq!(prb.trailed(bool_check), 1);
	}

	#[test]
	#[traced_test]
	fn test_model_advisor_bool_no_call() {
		let mut prb = Model::default();
		let i = prb.new_int_decision(0..=3);
		let b = i.geq(2);
		let bool_check = prb.new_trailed(0);
		let int_check = prb.new_trailed(0);
		let t = TestModel {
			b,
			i,
			bool_check,
			int_check,
		};
		prb.post_constraint(t).unwrap();
		i.tighten_min(&mut prb, 1, NO_REASON)
			.expect("tighten_min failed");
		let (_, _): (Solver, _) = prb.lower().to_solver().expect("to_solver failed");
		assert_eq!(prb.trailed(bool_check), 0);
	}

	#[test]
	#[traced_test]
	fn test_model_advisor_int_call() {
		let mut prb = Model::default();
		let i = prb.new_int_decision(0..=3);
		let b = prb.new_bool_decision();
		let bool_check = prb.new_trailed(0);
		let int_check = prb.new_trailed(0);
		let t = TestModel {
			b,
			i,
			bool_check,
			int_check,
		};
		prb.post_constraint(t).unwrap();
		i.tighten_min(&mut prb, 1, NO_REASON)
			.expect("tighten_min failed");
		i.tighten_max(&mut prb, 2, NO_REASON)
			.expect("tighten_max failed");
		let (mut slv, map): (Solver, _) = prb.lower().to_solver().expect("to_solver failed");
		assert_eq!(prb.trailed(int_check), 1);
		let i_slv = map.get(&mut slv, i);
		let (min, max) = i_slv.bounds(&slv);
		assert_eq!(min, 1);
		assert_eq!(max, 2);
	}

	impl<E> Constraint<E> for TestModel
	where
		E: ReasoningEngine,
		View<IntVal>: IntModelActions<E>,
		View<bool>: BoolModelActions<E>,
	{
		fn simplify(
			&mut self,
			_context: &mut E::PropagationContext<'_>,
		) -> Result<SimplificationStatus, E::Conflict> {
			Ok(SimplificationStatus::NoFixpoint)
		}

		fn to_solver(&self, _context: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
			Ok(())
		}
	}

	impl<E> Propagator<E> for TestModel
	where
		E: ReasoningEngine,
		View<IntVal>: IntModelActions<E>,
		View<bool>: BoolModelActions<E>,
	{
		fn advise_of_bool_change(
			&mut self,
			context: &mut E::NotificationContext<'_>,
			_data: u64,
		) -> bool {
			assert!(self.b.val(context).is_some());
			context.set_trailed(self.bool_check, context.trailed(self.bool_check) + 1);
			true
		}

		fn advise_of_int_change(
			&mut self,
			context: &mut E::NotificationContext<'_>,
			_data: u64,
			_event: IntEvent,
		) -> bool {
			context.set_trailed(self.int_check, context.trailed(self.int_check) + 1);
			true
		}

		fn initialize(&mut self, context: &mut E::InitializationContext<'_>) {
			self.b.advise_when_fixed(context, 0);
			self.i.advise_when(context, IntPropCond::Bounds, 0);
		}

		fn propagate(
			&mut self,
			_context: &mut E::PropagationContext<'_>,
		) -> Result<(), E::Conflict> {
			Ok(())
		}
	}
}
