//! Module containing the modelling layer for the Huub solver.

pub(crate) mod decision;
pub mod deserialize;
pub mod expressions;
mod initilization_context;
pub(crate) mod view;

use std::{
	any::Any,
	fmt::Debug,
	hash::Hash,
	iter::{repeat_n, repeat_with},
	marker::PhantomData,
	mem,
	num::NonZeroI32,
};

use pindakaas::{
	ClauseDatabaseTools, Cnf, Lit as RawLit,
	solver::{cadical::Cadical, propagation::ExternalPropagation},
};
use rangelist::IntervalIterator;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::warn;

pub use crate::model::{
	decision::{Decision, DecisionReference},
	view::{DefaultView, View},
};
use crate::{
	IntSet, IntVal,
	actions::{
		ConstructionActions, DecisionActions, IntInspectionActions, PropagationActions,
		ReasoningContext, ReasoningEngine, SimplificationActions, Trailed, TrailingActions,
	},
	constraints::{
		BoxedConstraint, Conflict, Constraint, DeferredReason, Reason, ReasonBuilder,
		SimplificationStatus,
		bool_array_element::BoolDecisionArrayElement,
		int_array_element::{IntArrayElementBounds, IntValArrayElement},
		int_table::IntTable,
		int_unique::IntUnique,
	},
	helpers::bytes::Bytes,
	lower::{InitConfig, LoweringContext, LoweringError, LoweringMap, LoweringMapBuilder},
	model::{
		decision::{
			boolean::BoolDecision,
			integer::{Domain, IntDecision},
		},
		initilization_context::ModelInitContext,
		view::integer::IntView,
	},
	solver::{
		IntLitMeaning, Solver,
		activation_list::{ActivationAction, IntEvent},
		queue::{PropagatorInfo, PropagatorQueue},
	},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// Identifies an advisor in the [`Model`]
pub(crate) struct AdvRef(u32);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Definition of how a constraint has requested to be advised at the model
/// level.
struct Advisor {
	/// Reference to the constraint that has requested to be advised.
	con: ConRef,
	/// The data associated by the constraint with the advisor.
	data: u64,
	/// Whether lower and upper bound events must be swapped.
	negated: bool,
	/// Whether the advise on a Boolean must be advised as an integer event.
	bool2int: bool,
	/// The condition on the integer decision variable that must be decided
	/// before the constraint is advised.
	condition: Option<IntLitMeaning>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// Identifies an constraint in the [`Model`]
pub(crate) struct ConRef(u32);

#[derive(Clone, Debug, Default)]
/// A formulation of a problem instance in terms of decisions and constraints.
pub struct Model {
	/// A base [`Cnf`] object that contains pure Boolean parts of the problem.
	pub(crate) cnf: Cnf,
	/// A list of constraints that have been added to the model.
	constraints: Vec<Option<BoxedConstraint>>,
	/// The definitions of the Boolean variables that have been created.
	pub(crate) bool_vars: Vec<BoolDecision>,
	/// The definitions of the integer variables that have been created.
	pub(crate) int_vars: Vec<IntDecision>,
	/// A queue of constraints that need to be propagated.
	propagator_queue: PropagatorQueue,
	/// Fake trailed storage
	trail: Vec<[u8; 8]>,
	/// Reference for the current propagator being executed.
	cur_prop: Option<ConRef>,
	/// Integer variable changes that occurred during the execution of the
	/// current propagator.
	int_events: FxHashMap<u32, IntEvent>,
	/// Boolean variable changes that occurred during the execution of the
	/// current propagator.
	bool_events: Vec<Decision<bool>>,

	/// Definitions of the advisors that are listening to the certain changes.
	advisors: Vec<Advisor>,
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
	/// Access the raw value of the constraint reference.
	pub(crate) fn from_raw(raw: u32) -> Self {
		debug_assert!(raw <= i32::MAX as u32);
		Self(raw)
	}

	/// Recreate the constraint reference from a raw value.
	pub(crate) fn index(&self) -> usize {
		self.0 as usize
	}

	/// Create a new constraint reference from an index.
	pub(crate) fn new(index: usize) -> Self {
		debug_assert!(index < i32::MAX as usize);
		Self(index as u32)
	}

	/// Access the raw value of the advisor reference.
	pub(crate) fn raw(&self) -> u32 {
		self.0
	}
}

impl Model {
	/// Create a [`ReasoningEngine::Conflict`] instance based on the failure to
	/// set `subject`, that must be set because of `reason`.
	fn create_conflict(
		&mut self,
		subject: View<bool>,
		reason: impl ReasonBuilder<Self>,
	) -> <Self as ReasoningEngine>::Conflict {
		match reason.build_reason(self) {
			Ok(reason) => Conflict {
				subject: Some(subject),
				reason,
			},
			Err(true) => Conflict {
				subject: None,
				reason: Reason::Simple(!subject),
			},
			Err(false) => unreachable!("invalid reason"),
		}
	}

	/// Create a new Boolean variable.
	pub fn new_bool_decision(&mut self) -> View<bool> {
		let var: Decision<bool> = Decision(self.cnf.new_lit());
		self.bool_vars.push(BoolDecision {
			alias: None,
			constraints: Vec::new(),
		});
		debug_assert_eq!(var.idx(), self.bool_vars.len() - 1);
		var.into()
	}

	/// Create `len` new Boolean variables.
	pub fn new_bool_decisions(&mut self, len: usize) -> Vec<View<bool>> {
		repeat_with(|| self.new_bool_decision()).take(len).collect()
	}

	/// Create a new integer variable with the given domain.
	pub fn new_int_decision(&mut self, domain: impl Into<IntSet>) -> View<IntVal> {
		let domain = domain.into();
		match domain.card() {
			Some(0) => {
				unimplemented!("integer decision must have at least 1 value in their domain")
			}
			Some(1) => (*domain.lower_bound().unwrap()).into(),
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

	/// Post a constraint to the model.
	///
	/// The constraint is added to the model. It will be enforced during
	/// simplification and in any subsequent solving method.
	pub fn post_constraint<C: Constraint<Self>>(&mut self, mut constraint: C) {
		let con = ConRef::new(self.constraints.len());
		let mut ctx = ModelInitContext::new(self, con);
		constraint.initialize(&mut ctx);
		let priority = ctx.priority;
		let enqueue = ctx.enqueue();
		self.constraints.push(Some(Box::new(constraint)));
		let r = ConRef::new(self.constraints.len() - 1);
		debug_assert_eq!(r, con);
		self.propagator_queue.info.push(PropagatorInfo {
			enqueued: false,
			priority,
		});
		debug_assert_eq!(r.index(), self.propagator_queue.info.len() - 1);
		if enqueue {
			self.propagator_queue.enqueue_propagator(con.raw());
		}
	}

	/// Propagate the constraint at index `con`, updating the domains of the
	/// variables and rewriting the constraint if necessary.
	pub(crate) fn propagate(&mut self, con: ConRef) -> Result<(), LoweringError> {
		let Some(mut con_obj) = self.constraints[con.index()].take() else {
			return Ok(());
		};
		self.cur_prop = Some(con);
		let mut status = con_obj.simplify(self);
		self.cur_prop = None;

		// Resolve lazy explanation if it is required.
		if let Err(Conflict {
			subject,
			reason: Reason::Lazy(r),
		}) = status
		{
			debug_assert_eq!(ConRef::new(r.propagator as usize), con);
			let conj = con_obj.explain(self, subject.unwrap_or(false.into()), r.data);
			status = Err(Conflict {
				subject,
				reason: Reason::Eager(conj.into_boxed_slice()),
			});
		};

		match status? {
			SimplificationStatus::Subsumed => {
				// Constraint is known to be satisfied, no need to place back.
			}
			SimplificationStatus::NoFixpoint => {
				self.constraints[con.index()] = Some(con_obj);
			}
		}
		// Notify propagators about all events that occurred
		let advise_of_int_change = |model: &mut Model, con: ConRef, data: u64, event| {
			if let Some(mut c) = model.constraints[con.index()].take() {
				let ret = c.advise_of_int_change(model, data, event);
				model.constraints[con.index()] = Some(c);
				ret
			} else {
				false
			}
		};
		let advise_of_bool_change = |model: &mut Model, con: ConRef, data: u64| {
			if let Some(mut c) = model.constraints[con.index()].take() {
				let ret = c.advise_of_bool_change(model, data);
				model.constraints[con.index()] = Some(c);
				ret
			} else {
				false
			}
		};
		let mut int_events = mem::take(&mut self.int_events);
		for (i, event) in int_events.drain() {
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
							IntLitMeaning::Eq(_) | IntLitMeaning::NotEq(_) => {
								iv.val(self).is_some()
							}
							IntLitMeaning::GreaterEq(v) | IntLitMeaning::Less(v) => {
								let (min, max) = iv.bounds(self);
								v >= min || v < max
							}
						};
						if triggered {
							if bool2int {
								advise_of_int_change(self, con, data, IntEvent::Fixed)
							} else {
								advise_of_bool_change(self, con, data)
							}
						} else {
							false
						}
					} else {
						advise_of_int_change(self, con, data, event)
					};
					if enqueue {
						self.propagator_queue.enqueue_propagator(con.raw());
					}
				}
				ActivationAction::Enqueue(c) => self.propagator_queue.enqueue_propagator(c.raw()),
			});
			self.int_vars[i as usize].constraints = constraints;
		}
		self.int_events = int_events;
		let mut bool_events = mem::take(&mut self.bool_events);
		for bv in bool_events.drain(..) {
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
							advise_of_int_change(self, con, data, IntEvent::Fixed)
						} else {
							advise_of_bool_change(self, con, data)
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
		self.bool_events = bool_events;
		Ok(())
	}

	/// Process the model to create a [`Solver`] instance that can be used to
	/// solve it.
	///
	/// This method will return a [`Solver`] instance in addition to a
	/// [`LoweringMap`], which can be used to map from [`model::View`](View)
	/// to [`solver::View`](crate::solver::View). If an error occurs during the
	/// reformulation process, or if it is found to be trivially unsatisfiable,
	/// then an error will be returned.
	pub fn to_solver<Sat>(
		&mut self,
		config: &InitConfig,
	) -> Result<(Solver<Sat>, LoweringMap), LoweringError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
	{
		let mut slv = Solver::<Sat>::default();
		let any_slv: &mut dyn Any = &mut slv.sat;
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			// Set the solver options for preprocessing/inprocessing
			r.set_option("condition", config.conditioning() as i32);
			r.set_option("elim", config.variable_elimination() as i32);
			r.set_option("exteagerreasons", config.reason_eager() as i32);
			r.set_option("inprocessing", config.inprocessing() as i32);
			r.set_limit("preprocessing", config.preprocessing() as i32);
			r.set_option("probe", config.probing() as i32);
			r.set_option("subsume", config.subsumption() as i32);
			r.set_option("vivify", config.vivification() as i32);

			// Set the solver options for search configurations
			// Enable restart if the config is set to true or if there are no
			// user search heuristics are provided
			r.set_option("restart", config.restart() as i32);
		} else {
			warn!("unknown solver: vivification and restart options are ignored");
		}

		while let Some(con) = self.propagator_queue.pop() {
			self.propagate(ConRef::from_raw(con))?;
		}

		// Determine encoding types for integer variables
		let mut int_eager_direct = FxHashSet::<Decision<IntVal>>::default();
		let int_eager_order = FxHashSet::<Decision<IntVal>>::default();

		for c in self.constraints.iter().flatten() {
			let c: &dyn Constraint<Model> = c.as_ref();
			let c: &dyn Any = c;
			if let Some(c) = c.downcast_ref::<BoolDecisionArrayElement>() {
				let index = c.index.resolve_alias(self);
				if let IntView::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			} else if let Some(c) = c.downcast_ref::<IntUnique>() {
				for v in &c.prop.var {
					let v = v.resolve_alias(self);
					if let IntView::Linear(lin) = v.0 {
						let Domain::Domain(dom) = &self.int_vars[lin.var.idx()].domain else {
							unreachable!()
						};
						if dom.card() <= Some(c.prop.var.len() * 100 / 80) {
							int_eager_direct.insert(lin.var);
						}
					}
				}
			} else if let Some(c) =
				c.downcast_ref::<IntArrayElementBounds<View<IntVal>, View<IntVal>, View<IntVal>>>()
			{
				let index = c.index.resolve_alias(self);
				if let IntView::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			} else if let Some(c) = c.downcast_ref::<IntTable>() {
				for &v in &c.vars {
					let v = v.resolve_alias(self);
					if let IntView::Linear(lin) = v.0 {
						int_eager_direct.insert(lin.var);
					}
				}
			} else if let Some(c) =
				c.downcast_ref::<IntValArrayElement<View<IntVal>, View<IntVal>>>()
			{
				let index = c.0.index.resolve_alias(self);
				if let IntView::Linear(lin) = index.0 {
					int_eager_direct.insert(lin.var);
				}
			}
		}

		// Create the mapping between model decisions and solver views.
		let mut map_builder = LoweringMapBuilder {
			bool_map: vec![None; self.bool_vars.len()],
			int_eager_direct,
			int_eager_limit: config.int_eager_limit(),
			int_eager_order,
			int_map: vec![None; self.int_vars.len()],
		};

		// Ensure the creation of all integer variables.
		for (idx, _) in self.int_vars.iter().enumerate() {
			map_builder.get_or_create_int(self, &mut slv, Decision(idx as u32));
		}

		// Ensure the creation of all Boolean variables.
		for var in 1..=self.bool_vars.len() as u32 {
			let raw = RawLit::from_raw(NonZeroI32::new(var as i32).unwrap());
			map_builder.get_or_create_bool(self, &mut slv, Decision(raw).into());
		}

		// Finalize the reformulation map (all variables must be created by now)
		let map = map_builder.finalize();

		// Create constraint data structures within the solver
		let mut ctx = LoweringContext::new(&mut slv, &map, &self.trail);
		for c in self.constraints.iter().flatten() {
			c.to_solver(&mut ctx)?;
		}

		Ok((slv, map))
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
	fn declare_conflict(&mut self, reason: impl ReasonBuilder<Self>) -> Conflict<View<bool>> {
		match reason.build_reason(self) {
			Ok(reason) => Conflict {
				subject: None,
				reason,
			},
			Err(false) => panic!("invalid reason"),
			Err(true) => Conflict {
				subject: None,
				reason: Reason::Eager(Box::new([])),
			},
		}
	}

	fn deferred_reason(&self, data: u64) -> DeferredReason {
		DeferredReason {
			propagator: self.cur_prop.unwrap().index() as u32,
			data,
		}
	}
}

impl ReasoningContext for Model {
	type Atom = <Self as ReasoningEngine>::Atom;
	type Conflict = <Self as ReasoningEngine>::Conflict;
}

impl ReasoningEngine for Model {
	type Atom = View<bool>;

	type Conflict = Conflict<View<bool>>;
	type ExplanationCtx<'a> = Self;
	type InitializationCtx<'a> = ModelInitContext<'a>;
	type NotificationCtx<'a> = Self;
	type PropagationCtx<'a> = Self;
}

impl SimplificationActions for Model {
	type Target = Model;

	fn post_constraint<C: Constraint<Model>>(&mut self, constraint: C) {
		self.post_constraint(constraint);
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
