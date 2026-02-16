//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use std::{
	any::Any,
	error::Error,
	fmt::{self, Debug, Display},
	marker::PhantomData,
};

use itertools::Itertools;
use pindakaas::{
	ClauseDatabase, Lit as RawLit, Unsatisfiable, solver::propagation::ExternalPropagation,
};
use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;

use crate::{
	IntSet, IntVal, Model,
	actions::{
		BoolInspectionActions, ConstructionActions, IntDecisionActions, IntInspectionActions,
		PostingActions, ReasoningContext, ReasoningEngine, Trailed,
	},
	constraints::{BoxedPropagator, Conflict, ReasonBuilder},
	helpers::bytes::Bytes,
	model::{self, decision::integer::Domain},
	solver::{
		self, IntLitMeaning, Solver,
		decision::integer::{EncodingType, IntDecision},
		engine::Engine,
		view::boolean::BoolView,
	},
	views::LinearBoolView,
};

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
/// Configuration object for the reformulation process of creating a [`Solver`]
/// object from a [`Model`].
pub struct InitConfig {
	/// Whether to enable the globally blocked clause elimination (conditioning)
	conditioning: bool,
	/// Whether to enable inprocessing in the SAT solver.
	inprocessing: bool,
	/// The maximum cardinality of the domain of an integer variable before its
	/// order encoding is created lazily.
	int_eager_limit: Option<usize>,
	/// The number of preprocessing rounds in the SAT solver
	preprocessing: Option<usize>,
	/// Whether to enable the failed literal probing in the SAT solver.
	probing: bool,
	/// Whether to enable restarts in the SAT solver.
	restart: bool,
	/// Whether to enable the global forward subsumption in the SAT solver.
	subsumption: bool,
	/// Whether to enable asking reason eagerly in the SAT solver.
	reason_eager: bool,
	/// Whether to enable the bounded variable elimination in the SAT solver.
	variable_elimination: bool,
	/// Whether to enable the vivification in the SAT solver.
	vivification: bool,
}

/// Actions that can be performed when reformulating a [`Model`] object into a
/// [`Solver`] object.
trait LoweringActions {
	/// Add a clause over Boolean views to the SAT solver.
	fn add_clause(
		&mut self,
		clause: Vec<solver::View<bool>>,
	) -> Result<(), <Engine as ReasoningEngine>::Conflict>;

	/// Add a propagator to the solver.
	fn add_propagator(&mut self, propagator: BoxedPropagator);

	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn bool_val(&self, bv: solver::Decision<bool>) -> Option<bool>;

	/// Get the set of values from which the integer view is guaranteed to take
	/// a value.
	fn int_domain(&self, var: solver::Decision<IntVal>) -> IntSet;

	/// Check whether a given integer view can take a given value
	fn int_in_domain(&self, var: solver::Decision<IntVal>, val: IntVal) -> bool;

	/// Get (or create) a literal for the given integer view with the given
	/// meaning.
	fn int_lit(
		&mut self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> solver::View<bool>;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` it has no direct meaning.
	fn int_lit_meaning(
		&self,
		var: solver::Decision<IntVal>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning>;

	/// Get the maximum value that an integer view is guaranteed to take.
	fn int_max(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn int_max_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool>;

	/// Get the minimum value that an integer view is guaranteed to take.
	fn int_min(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn int_min_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool>;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn int_try_lit(
		&self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>>;

	/// Create a new trailed integer value that will be usable in the
	/// [`Solver`].
	fn new_trailed(&mut self, init: u64) -> Trailed<u64>;

	/// Create a fresh range of Boolean variables in the underlying SAT solver.
	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange;
}

/// Context object used during the lowering process that creates a
/// [`Solver`] object from a [`Model`].
pub struct LoweringContext<'a> {
	/// Actions that can be performed by the [`Solver`] object we are
	/// creating.
	///
	/// Note that this is not a [`Solver`] object itself, but rather a
	/// [`LoweringActions`] trait object to avoid generic parameters.
	slv: &'a mut dyn LoweringActions,
	/// The mapping from decision variables in the [`Model`] to the
	/// corresponding view in the [`Solver`].
	map: &'a LoweringMap,
	/// Error that captures the clause that caused methods to return
	/// [`Unsatisfiable`].
	pub(crate) error: Option<LoweringError>,
	/// The state of the trailed values in the source [`Model`] object.
	trail: &'a [[u8; 8]],
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`Model`].
pub enum LoweringError {
	/// Error used when a conflict is found during the simplification process of
	/// the model.
	Simplification(<Model as ReasoningEngine>::Conflict),
	/// Error used when a conflict is found by the SAT solver when lowering the
	/// problem.
	Lowering(<Engine as ReasoningEngine>::Conflict),
}

/// A reformulation helper that maps decisions in a [`Model`] objects to the
/// [`solver::View`] that is used to represent it in a [`Solver`] object.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct LoweringMap {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<solver::View<bool>>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<solver::View<IntVal>>,
}

/// Helper type to create a [`ReformulationMap`] object.
///
/// This type is primarily meant to resolve the order of creation issue when
/// dealing with aliased variables.
pub(crate) struct LoweringMapBuilder {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<Option<solver::View<bool>>>,
	/// Set of integer decision for which the direct encoding should be created
	/// eagerly.
	pub(crate) int_eager_direct: FxHashSet<model::Decision<IntVal>>,
	/// The (default) maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub(crate) int_eager_limit: usize,
	/// Set of integer decision for which the order encoding should be created
	/// eagerly.
	pub(crate) int_eager_order: FxHashSet<model::Decision<IntVal>>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<Option<solver::View<IntVal>>>,
}

impl InitConfig {
	/// The default maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;

	/// Get the default number of preprocessing rounds in the SAT solver.
	pub const DEFAULT_PREPROCESSING: usize = 0;

	/// Get whether to enable the globally blocked clause elimination
	/// (conditioning) in the SAT solver.
	pub fn conditioning(&self) -> bool {
		self.conditioning
	}

	/// Get whether to enable inprocessing in the SAT solver.
	pub fn inprocessing(&self) -> bool {
		self.inprocessing
	}

	/// Get the maximum cardinality of the domain of an integer variable before
	/// its order encoding is created lazily.
	pub fn int_eager_limit(&self) -> usize {
		self.int_eager_limit
			.unwrap_or(Self::DEFAULT_INT_EAGER_LIMIT)
	}

	/// Get whether to enable preprocessing in the SAT solver.
	pub fn preprocessing(&self) -> usize {
		self.preprocessing.unwrap_or(Self::DEFAULT_PREPROCESSING)
	}

	/// Get whether to enable the failed literal probing in the SAT solver.
	pub fn probing(&self) -> bool {
		self.probing
	}

	/// Get whether to enable asking for explanation clauses for all literals
	/// propagated on the level of a conflict.
	pub fn reason_eager(&self) -> bool {
		self.reason_eager
	}

	/// Get whether to enable restarts in the SAT solver.
	pub fn restart(&self) -> bool {
		self.restart
	}

	/// Get whether to enable the global forward subsumption in the SAT
	/// solver.
	pub fn subsumption(&self) -> bool {
		self.subsumption
	}

	/// Get whether to enable the bounded variable elimination in the SAT
	/// solver.
	pub fn variable_elimination(&self) -> bool {
		self.variable_elimination
	}

	/// Get whether to enable the vivification in the SAT solver.
	pub fn vivification(&self) -> bool {
		self.vivification
	}

	/// Change whether to enable the globally blocked clause elimination
	/// (conditioning) in the SAT solver.
	pub fn with_conditioning(mut self, conditioning: bool) -> Self {
		self.conditioning = conditioning;
		self
	}

	/// Change whether to enable inprocessing in the SAT solver.
	pub fn with_inprocessing(mut self, inprocessing: bool) -> Self {
		self.inprocessing = inprocessing;
		self
	}

	/// Change the maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub fn with_int_eager_limit(mut self, limit: usize) -> Self {
		self.int_eager_limit = Some(limit);
		self
	}

	/// Change the number of preprocessing rounds in the SAT solver.
	pub fn with_preprocessing(mut self, preprocessing: usize) -> Self {
		self.preprocessing = Some(preprocessing);
		self
	}

	/// Change whether to enable the failed literal probing in the SAT
	/// solver.
	pub fn with_probing(mut self, probing: bool) -> Self {
		self.probing = probing;
		self
	}

	/// Change whether to enable asking reason eagerly in the SAT solver.
	pub fn with_reason_eager(mut self, reason_eager: bool) -> Self {
		self.reason_eager = reason_eager;
		self
	}

	/// Change whether to enable restarts in the SAT solver.
	pub fn with_restart(mut self, restart: bool) -> Self {
		self.restart = restart;
		self
	}

	/// Change whether to enable the global forward subsumption in the SAT
	/// solver.
	pub fn with_subsumption(mut self, subsumption: bool) -> Self {
		self.subsumption = subsumption;
		self
	}

	/// Change whether to enable the bounded variable elimination in the SAT
	/// solver.
	pub fn with_variable_elimination(mut self, variable_elimination: bool) -> Self {
		self.variable_elimination = variable_elimination;
		self
	}

	/// Change whether to enable the vivification in the oracle solver.
	pub fn with_vivification(mut self, vivification: bool) -> Self {
		self.vivification = vivification;
		self
	}
}

impl<'a> LoweringContext<'a> {
	/// Add a new clause to the resulting [`Solver`].
	pub fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = impl Into<solver::View<bool>>>,
	) -> Result<(), LoweringError> {
		let clause: Result<Vec<_>, bool> = clause
			.into_iter()
			.filter_map(|lit| match lit.into().0 {
				BoolView::Lit(lit) => Some(Ok(lit.0)),
				BoolView::Const(true) => Some(Err(true)),
				BoolView::Const(false) => None,
			})
			.collect();
		let clause = match clause {
			Err(false) => unreachable!(),
			Err(true) => return Ok(()),
			Ok(clause) if clause.is_empty() => {
				return Err(self.declare_conflict([]).into());
			}
			Ok(clause) => clause,
		};
		debug_assert!(self.error.is_none());
		match self.add_clause_from_slice(&clause) {
			Err(Unsatisfiable) => Err(self.error.take().unwrap()),
			Ok(()) => Ok(()),
		}
	}

	/// Encode the given constraint into conjunctive normal form (CNF) using the
	/// given encoder, and add it to the resulting [`Solver`].
	pub fn cnf_encode<C, E>(&mut self, constraint: &C, encoder: &E) -> Result<(), LoweringError>
	where
		C: ?Sized,
		E: pindakaas::Encoder<Self, C> + ?Sized,
	{
		debug_assert!(self.error.is_none());
		let res = pindakaas::Encoder::encode(encoder, self, constraint);
		match res {
			Ok(()) => Ok(()),
			Err(Unsatisfiable) => Err(self.error.take().unwrap()),
		}
	}

	/// Declare a conflict with the given reason that was encountered during
	/// lowering.
	pub fn declare_conflict(
		&mut self,
		reason: impl ReasonBuilder<Self>,
	) -> <Self as ReasoningContext>::Conflict {
		Conflict::new(self, None, reason)
	}

	/// Read a trailed value from the [`Model`] trail.
	pub fn model_trailed<T: Bytes>(&self, i: Trailed<T>) -> T {
		T::from_bytes(self.trail[i.index as usize])
	}

	/// Create a lowering context for a solver, a mapping, and a trail snapshot.
	pub(crate) fn new<O: ExternalPropagation>(
		slv: &'a mut Solver<O>,
		map: &'a LoweringMap,
		trail: &'a [[u8; 8]],
	) -> Self {
		Self {
			slv,
			map,
			error: None,
			trail,
		}
	}

	/// Create a new Boolean decision for the [`Solver`].
	pub fn new_bool_decision(&mut self) -> solver::View<bool> {
		solver::Decision(self.slv.new_var_range(1).start().into()).into()
	}

	/// Map a [`model::View`] to its corresponding [`solver::View`].
	pub fn solver_view<T: solver::DefaultView + model::DefaultView>(
		&mut self,
		view: model::View<T>,
	) -> solver::View<T> {
		self.map.get(self.slv, view)
	}
}

impl ClauseDatabase for LoweringContext<'_> {
	fn add_clause_from_slice(&mut self, clause: &[RawLit]) -> Result<(), Unsatisfiable> {
		let clause = clause
			.iter()
			.map(|&l| solver::Decision(l).into())
			.collect_vec();

		match self.slv.add_clause(clause) {
			Ok(()) => Ok(()),
			Err(err) => {
				self.error = Some(err.into());
				Err(Unsatisfiable)
			}
		}
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.slv.new_var_range(len)
	}
}

impl ConstructionActions for LoweringContext<'_> {
	fn new_trailed<T: Bytes>(&mut self, init: T) -> Trailed<T> {
		let bytes = init.to_bytes();
		let i = u64::from_bytes(bytes);
		let t = LoweringActions::new_trailed(self.slv, i);
		Trailed {
			index: t.index,
			ty: PhantomData,
		}
	}
}

impl Debug for LoweringContext<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let ptr: *const _ = &self.slv;
		f.debug_struct("LoweringContext")
			.field("slv", &ptr)
			.field("map", &self.map)
			.field("error", &self.error)
			.field("trail", &self.trail)
			.finish()
	}
}

impl PostingActions for LoweringContext<'_> {
	fn add_clause(
		&mut self,
		clause: impl IntoIterator<Item = Self::Atom>,
	) -> Result<(), Self::Conflict> {
		let clause = clause.into_iter().collect::<Vec<_>>();
		self.slv.add_clause(clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.slv.add_propagator(propagator);
	}
}

impl ReasoningContext for LoweringContext<'_> {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl Display for LoweringError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Simplification(c) => {
				write!(f, "A conflict occurred during simplification: {c:?}")
			}
			Self::Lowering(e) => {
				write!(f, "An error occurred during solver conversion: {e:?}")
			}
		}
	}
}

impl Error for LoweringError {}

impl From<<Engine as ReasoningEngine>::Conflict> for LoweringError {
	fn from(value: <Engine as ReasoningEngine>::Conflict) -> Self {
		Self::Lowering(value)
	}
}

impl From<<Model as ReasoningEngine>::Conflict> for LoweringError {
	fn from(value: <Model as ReasoningEngine>::Conflict) -> Self {
		Self::Simplification(value)
	}
}

impl LoweringMap {
	/// Lookup the [`solver::View`] to which the given model [`model::View`]
	/// maps.
	pub fn get<Ctx, T>(&self, ctx: &mut Ctx, view: model::View<T>) -> solver::View<T>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
		T: solver::DefaultView + model::DefaultView,
	{
		let any: &dyn Any = &view;
		if let Some(view) = any.downcast_ref::<model::View<bool>>() {
			let res: Box<dyn Any> = Box::new(self.get_bool(ctx, *view));
			let Ok(res) = res.downcast::<solver::View<T>>() else {
				unreachable!()
			};
			*res
		} else if let Some(view) = any.downcast_ref::<model::View<IntVal>>() {
			let res: Box<dyn Any> = Box::new(self.get_int(ctx, *view));
			let Ok(res) = res.downcast::<solver::View<T>>() else {
				unreachable!()
			};
			*res
		} else {
			unreachable!()
		}
	}

	/// Perform [`Self::get`] in for the more general
	/// [`model::deserialize::AnyView`], resulting in a [`solver::AnyView`].
	///
	/// Note that it is generally recommended to use [`Self::get`] when
	/// possible. This method is generally only used when writing general
	/// purpose methods or in combination with deserialization.
	pub fn get_any<Ctx>(&self, ctx: &mut Ctx, view: model::deserialize::AnyView) -> solver::AnyView
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		match view {
			model::deserialize::AnyView::Bool(bv) => self.get_bool(ctx, bv).into(),
			model::deserialize::AnyView::Int(iv) => self.get_int(ctx, iv).into(),
		}
	}

	/// Internal method to which mapping `bool` variant views is dispatched.
	fn get_bool<Ctx>(&self, ctx: &mut Ctx, bv: model::View<bool>) -> solver::View<bool>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		use crate::model::view::boolean::BoolView::*;

		let int_lit = |slv: &mut Ctx, iv: model::Decision<IntVal>, lit_meaning: IntLitMeaning| {
			let iv = self.get_int(
				slv,
				model::View(model::view::integer::IntView::Linear(iv.into())),
			);
			iv.lit(slv, lit_meaning)
		};

		match bv.0 {
			Decision(l) => {
				let bv: solver::View<bool> = self.bool_map[l.idx()];
				if l.is_negated() { !bv } else { bv }
			}
			Const(c) => c.into(),
			IntEq(v, i) => int_lit(ctx, v, IntLitMeaning::Eq(i)),
			IntGreaterEq(v, i) => int_lit(ctx, v, IntLitMeaning::GreaterEq(i)),
			IntLess(v, i) => int_lit(ctx, v, IntLitMeaning::Less(i)),
			IntNotEq(v, i) => int_lit(ctx, v, IntLitMeaning::NotEq(i)),
		}
	}

	/// Lookup the solver [`IntView`] to which the given model [`int::IntView`]
	/// maps.
	fn get_int<Ctx>(&self, ctx: &mut Ctx, iv: model::View<IntVal>) -> solver::View<IntVal>
	where
		Ctx: ReasoningContext<Atom = solver::View<bool>> + ?Sized,
		solver::View<IntVal>: IntDecisionActions<Ctx>,
	{
		use crate::model::view::integer::IntView::*;

		match iv.0 {
			Const(c) => (c).into(),
			Linear(lin) => self.int_map[lin.var.idx()] * lin.scale + lin.offset,
			Bool(lin) => {
				let bv = self.get_bool(ctx, lin.var);
				match bv.0 {
					BoolView::Lit(lit) => LinearBoolView::new(lin.scale, lin.offset, lit).into(),
					BoolView::Const(b) => lin.transform_val(b as IntVal).into(),
				}
			}
		}
	}
}

impl LoweringMapBuilder {
	/// Create the [`ReformulationMap`] object ensuring that all variables have
	/// a representation in the [`Solver`].
	pub(crate) fn finalize(self) -> LoweringMap {
		LoweringMap {
			bool_map: self
				.bool_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
			int_map: self
				.int_map
				.into_iter()
				.map(|v| v.expect("variable should be resolved before finalize()"))
				.collect(),
		}
	}

	/// Get the representation of a Boolean decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (together with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_bool<Sat: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Sat>,
		bv: model::View<bool>,
	) -> solver::View<bool> {
		use crate::model::view::boolean::BoolView::*;

		match bv.0 {
			Decision(lit) => {
				let idx = lit.idx();
				if let Some(v) = self.bool_map[idx] {
					return if lit.is_negated() { !v } else { v };
				}
				let def = &model.bool_vars[idx];
				let view = match def.alias {
					Some(alias) => self.get_or_create_bool(model, slv, alias),
					None => slv.new_bool_decision().into(),
				};
				self.bool_map[idx] = Some(view);
				view
			}
			Const(b) => b.into(),
			IntEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::Eq(val))
			}
			IntGreaterEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::GreaterEq(val))
			}
			IntLess(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::Less(val))
			}
			IntNotEq(idx, val) => {
				let iv = self.get_or_create_int(model, slv, idx);
				iv.lit(slv, IntLitMeaning::NotEq(val))
			}
		}
	}

	/// Get the representation of a Integer decision variable in the [`Solver`]
	/// or create it if it does not yet exist.
	///
	/// Note that this method will function recursively (together with
	/// [`Self::get_or_create_bool`]) to resolve aliased variables.
	pub(crate) fn get_or_create_int<Sat: ExternalPropagation>(
		&mut self,
		model: &Model,
		slv: &mut Solver<Sat>,
		iv: model::Decision<IntVal>,
	) -> solver::View<IntVal> {
		use crate::model::view::integer::IntView::*;

		if let Some(v) = self.int_map[iv.idx()] {
			return v;
		}

		let def = &model.int_vars[iv.idx()];
		let view = match &def.domain {
			Domain::Domain(dom) => {
				let direct_enc = if self.int_eager_direct.contains(&iv) {
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				let card = dom.card();
				let order_enc = if self.int_eager_order.contains(&iv)
					|| self.int_eager_direct.contains(&iv)
					|| card.is_some() && card.unwrap() <= self.int_eager_limit
				{
					EncodingType::Eager
				} else {
					EncodingType::Lazy
				};
				IntDecision::new_in(slv, dom.clone(), order_enc, direct_enc)
			}
			Domain::Alias(alias) => match alias.0 {
				Const(c) => c.into(),
				Linear(lin) => {
					let iv = self.get_or_create_int(model, slv, lin.var);
					iv * lin.scale + lin.offset
				}
				Bool(lin) => {
					let bv = self.get_or_create_bool(model, slv, lin.var);
					bv * lin.scale + lin.offset
				}
			},
		};

		self.int_map[iv.idx()] = Some(view);
		view
	}
}

impl<Sat: ExternalPropagation> LoweringActions for Solver<Sat> {
	fn add_clause(
		&mut self,
		clause: Vec<solver::View<bool>>,
	) -> Result<(), <Engine as ReasoningEngine>::Conflict> {
		Solver::add_clause(self, clause)
	}

	fn add_propagator(&mut self, propagator: BoxedPropagator) {
		self.add_propagator(propagator, true);
	}

	fn bool_val(&self, bv: solver::Decision<bool>) -> Option<bool> {
		bv.val(self)
	}

	fn int_domain(&self, var: solver::Decision<IntVal>) -> IntSet {
		var.domain(self)
	}

	fn int_in_domain(&self, var: solver::Decision<IntVal>, val: IntVal) -> bool {
		var.in_domain(self, val)
	}

	fn int_lit(
		&mut self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> solver::View<bool> {
		var.lit(self, meaning)
	}

	fn int_lit_meaning(
		&self,
		var: solver::Decision<IntVal>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		var.lit_meaning(self, lit)
	}

	fn int_max(&self, var: solver::Decision<IntVal>) -> IntVal {
		var.max(self)
	}

	fn int_max_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool> {
		var.max_lit(self)
	}

	fn int_min(&self, var: solver::Decision<IntVal>) -> IntVal {
		var.min(self)
	}

	fn int_min_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool> {
		var.min_lit(self)
	}

	fn int_try_lit(
		&self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		var.try_lit(self, meaning)
	}

	fn new_trailed(&mut self, init: u64) -> Trailed<u64> {
		ConstructionActions::new_trailed(self, init)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.sat.new_var_range(len)
	}
}

impl ReasoningContext for dyn LoweringActions + '_ {
	type Atom = <Engine as ReasoningEngine>::Atom;
	type Conflict = <Engine as ReasoningEngine>::Conflict;
}

impl BoolInspectionActions<LoweringContext<'_>> for solver::Decision<bool> {
	fn val(&self, ctx: &LoweringContext<'_>) -> Option<bool> {
		ctx.slv.bool_val(*self)
	}
}

impl BoolInspectionActions<dyn LoweringActions + '_> for solver::Decision<bool> {
	fn val(&self, ctx: &dyn LoweringActions) -> Option<bool> {
		ctx.bool_val(*self)
	}
}

impl IntDecisionActions<LoweringContext<'_>> for solver::Decision<IntVal> {
	fn lit(&self, ctx: &mut LoweringContext<'_>, meaning: IntLitMeaning) -> solver::View<bool> {
		ctx.slv.int_lit(*self, meaning)
	}
}

impl IntDecisionActions<dyn LoweringActions + '_> for solver::Decision<IntVal> {
	fn lit(
		&self,
		ctx: &mut (dyn LoweringActions + '_),
		meaning: IntLitMeaning,
	) -> solver::View<bool> {
		ctx.int_lit(*self, meaning)
	}
}

impl IntInspectionActions<LoweringContext<'_>> for solver::Decision<IntVal> {
	fn bounds(&self, ctx: &LoweringContext<'_>) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &LoweringContext<'_>) -> IntSet {
		ctx.slv.int_domain(*self)
	}

	fn in_domain(&self, ctx: &LoweringContext<'_>, val: IntVal) -> bool {
		ctx.slv.int_in_domain(*self, val)
	}

	fn lit_meaning(
		&self,
		ctx: &LoweringContext<'_>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		ctx.slv.int_lit_meaning(*self, lit)
	}

	fn max(&self, ctx: &LoweringContext<'_>) -> IntVal {
		ctx.slv.int_max(*self)
	}

	fn max_lit(&self, ctx: &LoweringContext<'_>) -> solver::View<bool> {
		ctx.slv.int_max_lit(*self)
	}

	fn min(&self, ctx: &LoweringContext<'_>) -> IntVal {
		ctx.slv.int_min(*self)
	}

	fn min_lit(&self, ctx: &LoweringContext<'_>) -> solver::View<bool> {
		ctx.slv.int_min_lit(*self)
	}

	fn try_lit(
		&self,
		ctx: &LoweringContext<'_>,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		ctx.slv.int_try_lit(*self, meaning)
	}

	fn val(&self, ctx: &LoweringContext<'_>) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}

impl IntInspectionActions<dyn LoweringActions + '_> for solver::Decision<IntVal> {
	fn bounds(&self, ctx: &dyn LoweringActions) -> (IntVal, IntVal) {
		let lb = self.min(ctx);
		let ub = self.max(ctx);
		(lb, ub)
	}

	fn domain(&self, ctx: &dyn LoweringActions) -> IntSet {
		ctx.int_domain(*self)
	}

	fn in_domain(&self, ctx: &dyn LoweringActions, val: IntVal) -> bool {
		ctx.int_in_domain(*self, val)
	}

	fn lit_meaning(
		&self,
		ctx: &dyn LoweringActions,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning> {
		ctx.int_lit_meaning(*self, lit)
	}

	fn max(&self, ctx: &dyn LoweringActions) -> IntVal {
		ctx.int_max(*self)
	}

	fn max_lit(&self, ctx: &dyn LoweringActions) -> solver::View<bool> {
		ctx.int_max_lit(*self)
	}

	fn min(&self, ctx: &dyn LoweringActions) -> IntVal {
		ctx.int_min(*self)
	}

	fn min_lit(&self, ctx: &dyn LoweringActions) -> solver::View<bool> {
		ctx.int_min_lit(*self)
	}

	fn try_lit(
		&self,
		ctx: &dyn LoweringActions,
		meaning: IntLitMeaning,
	) -> Option<solver::View<bool>> {
		ctx.int_try_lit(*self, meaning)
	}

	fn val(&self, ctx: &dyn LoweringActions) -> Option<IntVal> {
		let (lb, ub) = self.bounds(ctx);
		if lb == ub { Some(lb) } else { None }
	}
}
