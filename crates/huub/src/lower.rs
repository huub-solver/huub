//! Data structures to store [`Model`] parts for analyses and for the
//! reformulation process of creating a [`Solver`] object from a [`Model`].

use std::{
	any::Any,
	error::Error,
	fmt::{self, Debug, Display},
	marker::PhantomData,
	num::NonZeroI32,
};

use bon::Builder;
use itertools::Itertools;
use pindakaas::{
	ClauseDatabase, Lit as RawLit, Unsatisfiable,
	solver::{cadical::Cadical, propagation::ExternalPropagation},
};
use rangelist::IntervalIterator;
use rustc_hash::FxHashSet;
use tracing::warn;

#[cfg(feature = "flatzinc")]
use crate::model::deserialize::{
	Goal,
	flatzinc::{FlatZincError, FlatZincLowerData, FlatZincModelMeta, FlatZincSolverMeta},
};
use crate::{
	IntSet, IntVal,
	actions::{
		BoolInspectionActions, ConstructionActions, IntDecisionActions, IntInspectionActions,
		PostingActions, ReasoningContext, ReasoningEngine, Trailed,
	},
	constraints::{
		BoxedPropagator, Conflict, Constraint, ReasonBuilder,
		bool_array_element::BoolDecisionArrayElement,
		int_array_element::{IntArrayElementBounds, IntValArrayElement},
		int_table::IntTable,
		int_unique::IntUnique,
	},
	helpers::bytes::Bytes,
	model::{self, Model, decision::integer::Domain, resolved::Resolved},
	solver::{
		self, IntLitMeaning, LiteralStrategy, Solver, engine::Engine, view::boolean::BoolView,
	},
	views::LinearBoolView,
};

/// Internal type to represent a complete [`Lowerer`] builder.
#[derive(Builder)]
#[builder(
	builder_type(
		name = Lowerer,
		vis = "pub",
		doc {
			/// A builder for the lowering process, which converts a high-level
			/// [`Model`] or a `FlatZinc` instance into a lower-level representation
			/// (typically a [`Solver`]).
			///
			/// This builder allows configuring various SAT solver options and preprocessing
			/// techniques before starting the lowering process.
		},
	),
	start_fn(name = builder_internal, vis = "pub(crate)"),
	finish_fn(name = finish_internal, vis = "")
)]
#[allow(
	clippy::missing_docs_in_private_items,
	reason = "cargo clippy triggers on origin for unknown reason"
)]
pub(crate) struct LowererComplete<Origin = ()> {
	/// A origin source from which the model was created, used to define wrapper
	/// methods for the lowering process.
	#[builder(start_fn)]
	origin: Origin,
	/// Whether to enable the globally blocked clause elimination (conditioning)
	#[builder(default = Lowerer::DEFAULT_CONDITIONING)]
	conditioning: bool,
	/// Whether to enable inprocessing in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_INPROCESSING)]
	inprocessing: bool,
	/// The maximum cardinality of the domain of an integer variable before its
	/// order encoding is created lazily.
	#[builder(default = Lowerer::DEFAULT_INT_EAGER_LIMIT)]
	int_eager_limit: usize,
	/// The number of preprocessing rounds in the SAT solver
	#[builder(default = Lowerer::DEFAULT_PREPROCESSING)]
	preprocessing: usize,
	/// Whether to enable CaDiCaL's light preprocessing.
	#[builder(default = Lowerer::DEFAULT_PREPROCESSING_LIGHT)]
	preprocessing_light: bool,
	/// Whether to enable the failed literal probing in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_PROBING)]
	probing: bool,
	/// The interval in terms of conflicts with the given `reduce_type` between
	/// clause-database reductions in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REDUCE_INTERVAL)]
	reduce_interval: usize,
	/// Type of method to compute the next size of the learned clause-database
	/// to trigger reduction in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REDUCE_TYPE)]
	reduce_type: ReduceType,
	/// Whether to enable restarts in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_RESTART)]
	restart: bool,
	/// Whether to enable the global forward subsumption in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_SUBSUMPTION)]
	subsumption: bool,
	/// Whether to enable asking reason eagerly in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_REASON_EAGER)]
	reason_eager: bool,
	/// Whether to enable the bounded variable elimination in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_VARIABLE_ELIMINATION)]
	variable_elimination: bool,
	/// Whether to enable the vivification in the SAT solver.
	#[builder(default = Lowerer::DEFAULT_VIVIFICATION)]
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

	/// Check whether a given integer view can take a given value.
	fn int_in_domain(&self, var: solver::Decision<IntVal>, val: IntVal) -> bool;

	/// Get (or create) a literal for the given integer view with the given
	/// meaning.
	fn int_lit(
		&mut self,
		var: solver::Decision<IntVal>,
		meaning: IntLitMeaning,
	) -> solver::View<bool>;

	/// Get the meaning of the given literal with respect to the given integer
	/// view, or `None` if it has no direct meaning.
	fn int_lit_meaning(
		&self,
		var: solver::Decision<IntVal>,
		lit: solver::View<bool>,
	) -> Option<IntLitMeaning>;

	/// Get the maximum value that an integer view is guaranteed to take.
	fn int_max(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less than or equal to its current upper bound.
	fn int_max_lit(&self, var: solver::Decision<IntVal>) -> solver::View<bool>;

	/// Get the minimum value that an integer view is guaranteed to take.
	fn int_min(&self, var: solver::Decision<IntVal>) -> IntVal;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater than or equal to its current lower bound.
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

/// Error type used during the reformulation process of creating a [`Solver`],
/// e.g. when creating a [`Solver`] from a [`Model`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringError {
	/// Error used when a conflict is found during the simplification process of
	/// the model.
	Simplification(<Model as ReasoningEngine>::Conflict),
	/// Error used when a conflict is found by the SAT solver when lowering the
	/// problem.
	Lowering(<Engine as ReasoningEngine>::Conflict),
}

/// A lowering helper that maps decisions in a [`Model`] object to the
/// [`solver::View`] that is used to represent it in a [`Solver`] object.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LoweringMap {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<solver::View<bool>>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<solver::View<IntVal>>,
}

/// Helper type to create a [`LoweringMap`] object.
///
/// This type is primarily meant to resolve the order of creation issue when
/// dealing with aliased variables.
pub(crate) struct LoweringMapBuilder {
	/// Map of Boolean decisions to Boolean views.
	pub(crate) bool_map: Vec<Option<solver::View<bool>>>,
	/// Set of integer decisions for which the direct encoding should be created
	/// eagerly.
	pub(crate) int_eager_direct: FxHashSet<Resolved<model::Decision<IntVal>>>,
	/// The (default) maximum cardinality of the domain of an integer variable
	/// before its order encoding is created lazily.
	pub(crate) int_eager_limit: usize,
	/// Set of integer decisions for which the order encoding should be created
	/// eagerly.
	pub(crate) int_eager_order: FxHashSet<Resolved<model::Decision<IntVal>>>,
	/// Map of integer decisions to integer views.
	pub(crate) int_map: Vec<Option<solver::View<IntVal>>>,
}

/// The function CaDiCaL uses to compute the target size of the learned clause
/// database when it is reduced.
///
/// Each variant's discriminant is the integer value that is passed to CaDiCaL's
/// `reduceopt` option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReduceType {
	/// Percentage-based reduction target (CaDiCaL `reduceopt` value `0`).
	Percent = 0,
	/// Square-root-based reduction target (CaDiCaL `reduceopt` value `1`).
	Sqrt = 1,
	/// Logarithmic reduction target (CaDiCaL `reduceopt` value `2`).
	Log = 2,
}

impl Lowerer {
	/// The default value when [`conditioning`](Lowerer::conditioning) is not
	/// explicitly set.
	pub const DEFAULT_CONDITIONING: bool = false;
	/// The default value when [`inprocessing`](Lowerer::inprocessing) is not
	/// explicitly set.
	pub const DEFAULT_INPROCESSING: bool = false;
	/// The default value when [`int_eager_limit`](Lowerer::int_eager_limit) is
	/// not explicitly set.
	pub const DEFAULT_INT_EAGER_LIMIT: usize = 255;
	/// The default value when [`preprocessing`](Lowerer::preprocessing) is not
	/// explicitly set.
	pub const DEFAULT_PREPROCESSING: usize = 0;
	/// The default value when
	/// [`preprocessing_light`](Lowerer::preprocessing_light) is not explicitly
	/// set.
	pub const DEFAULT_PREPROCESSING_LIGHT: bool = false;
	/// The default value when [`probing`](Lowerer::probing) is not explicitly
	/// set.
	pub const DEFAULT_PROBING: bool = false;
	/// The default value when [`reason_eager`](Lowerer::reason_eager) is not
	/// explicitly set.
	pub const DEFAULT_REASON_EAGER: bool = false;
	/// The default value when [`reduce_interval`](Lowerer::reduce_interval) is
	/// not explicitly set.
	pub const DEFAULT_REDUCE_INTERVAL: usize = 100;
	/// The default value when [`reduce_type`](Lowerer::reduce_type) is not
	/// explicitly set.
	pub const DEFAULT_REDUCE_TYPE: ReduceType = ReduceType::Sqrt;
	/// The default value when [`restart`](Lowerer::restart) is not explicitly
	/// set.
	pub const DEFAULT_RESTART: bool = false;
	/// The default value when [`subsumption`](Lowerer::subsumption) is not
	/// explicitly set.
	pub const DEFAULT_SUBSUMPTION: bool = false;
	/// The default value when
	/// [`variable_elimination`](Lowerer::variable_elimination) is not
	/// explicitly set.
	pub const DEFAULT_VARIABLE_ELIMINATION: bool = false;
	/// The default value when [`vivification`](Lowerer::vivification) is not
	/// explicitly set.
	pub const DEFAULT_VIVIFICATION: bool = false;
}

impl<State: lowerer::State> Lowerer<&mut Model, State> {
	/// Lower the [`Model`] to a [`Solver`].
	///
	/// This method will simplify the model, create the mapping between model
	/// decisions and solver views, and then create the constraint data
	/// structures within the solver.
	pub fn to_solver<Sat>(self) -> Result<(Solver<Sat>, LoweringMap), LoweringError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
		State: lowerer::IsComplete,
	{
		self.finish_internal().into_solver_internal()
	}
}

#[cfg(feature = "flatzinc")]
impl<State: lowerer::State> Lowerer<Result<FlatZincLowerData, FlatZincError>, State> {
	/// Lower the [`FlatZinc`](flatzinc_serde::FlatZinc) instance to a
	/// [`Solver`].
	///
	/// This method will internally create a [`Model`] from the FlatZinc data
	/// and then lower that model to a [`Solver`].
	pub fn to_solver<Sat>(self) -> Result<(Solver<Sat>, FlatZincSolverMeta), FlatZincError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
	{
		let complete = self.finish_internal();
		let FlatZincLowerData { meta, mut model } = complete.origin?;

		let (mut slv, map) = LowererComplete {
			origin: &mut model,
			conditioning: complete.conditioning,
			inprocessing: complete.inprocessing,
			int_eager_limit: complete.int_eager_limit,
			preprocessing: complete.preprocessing,
			preprocessing_light: complete.preprocessing_light,
			probing: complete.probing,
			reduce_interval: complete.reduce_interval,
			reduce_type: complete.reduce_type,
			restart: complete.restart,
			subsumption: complete.subsumption,
			reason_eager: complete.reason_eager,
			variable_elimination: complete.variable_elimination,
			vivification: complete.vivification,
		}
		.into_solver_internal()?;
		if let Some(branching) = meta.branching {
			branching.to_solver(&mut slv, &map);
		}
		let names = meta
			.names
			.into_iter()
			.map(|(k, v)| (k, map.get_any(&mut slv, v)))
			.collect();
		let goal = meta.goal.map(|g| match g {
			Goal::Minimize(v) => Goal::Minimize(map.get(&mut slv, v)),
			Goal::Maximize(v) => Goal::Maximize(map.get(&mut slv, v)),
		});
		let assumptions = meta
			.assumptions
			.into_iter()
			.map(|(label, view)| (label, map.get(&mut slv, view)))
			.collect();
		Ok((
			slv,
			FlatZincSolverMeta {
				names,
				stats: meta.stats,
				goal,
				assumptions,
			},
		))
	}
}

#[cfg(feature = "flatzinc")]
impl Lowerer<Result<FlatZincLowerData, FlatZincError>, lowerer::Empty> {
	/// Lower the [`FlatZinc`](flatzinc_serde::FlatZinc) instance to a
	/// [`Model`] with accompanying [`FlatZincModelMeta`] data.
	pub fn to_model(self) -> Result<(Model, FlatZincModelMeta), FlatZincError> {
		self.origin.map(|data| (data.model, data.meta))
	}
}

impl LowererComplete<&mut Model> {
	/// Internal implementation for lowering a model to a solver.
	fn into_solver_internal<Sat>(self) -> Result<(Solver<Sat>, LoweringMap), LoweringError>
	where
		Solver<Sat>: Default,
		Sat: ExternalPropagation + 'static,
	{
		let LowererComplete {
			origin: model,
			conditioning,
			inprocessing,
			int_eager_limit,
			preprocessing,
			preprocessing_light,
			probing,
			reduce_interval,
			reduce_type,
			restart,
			subsumption,
			reason_eager,
			variable_elimination,
			vivification,
		} = self;

		let mut slv = Solver::<Sat>::default();
		let any_slv: &mut dyn Any = &mut slv.sat;
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			// Set the solver options for preprocessing/inprocessing
			r.set_option("condition", conditioning as i32);
			r.set_option("elim", variable_elimination as i32);
			r.set_option("exteagerreasons", reason_eager as i32);
			r.set_option("inprocessing", inprocessing as i32);
			r.set_limit("preprocessing", preprocessing as i32);
			r.set_option("preprocesslight", preprocessing_light as i32);
			r.set_option("probe", probing as i32);
			r.set_option("reduceint", reduce_interval as i32);
			r.set_option("reduceopt", reduce_type as i32);
			r.set_option("subsume", subsumption as i32);
			r.set_option("vivify", vivification as i32);

			// Set the solver options for search configurations
			// Enable restart if the config is set to true or if there are no
			// user search heuristics are provided
			r.set_option("restart", restart as i32);
		} else {
			warn!(
				target: "solver",
				"ignore vivification and restart options for unknown solver"
			);
		}

		model.propagate()?;

		// Determine encoding types for integer variables
		let mut int_eager_direct = FxHashSet::<Resolved<model::Decision<IntVal>>>::default();
		let int_eager_order = FxHashSet::<Resolved<model::Decision<IntVal>>>::default();

		for c in model.constraints.iter().flatten() {
			let c: &dyn Constraint<Model> = c.as_ref();
			let c: &dyn Any = c;
			if let Some(c) = c.downcast_ref::<BoolDecisionArrayElement>() {
				let index = c.index.resolve_alias(model);
				if let Some(var) = index.integer_decision() {
					int_eager_direct.insert(var);
				}
			} else if let Some(c) = c.downcast_ref::<IntUnique>() {
				for v in &c.bounds_prop.vars {
					let v = v.resolve_alias(model);
					if let Some(var) = v.integer_decision() {
						let Domain::Domain(dom) = &model.int_vars[var.idx()].domain else {
							unreachable!()
						};
						if dom.card() <= Some(c.bounds_prop.vars.len() * 100 / 80) {
							int_eager_direct.insert(var);
						}
					}
				}
			} else if let Some(c) = c.downcast_ref::<IntArrayElementBounds<
				model::View<IntVal>,
				model::View<IntVal>,
				model::View<IntVal>,
			>>() {
				let index = c.index.resolve_alias(model);
				if let Some(var) = index.integer_decision() {
					int_eager_direct.insert(var);
				}
			} else if let Some(c) = c.downcast_ref::<IntTable>() {
				for &v in &c.vars {
					let v = v.resolve_alias(model);
					if let Some(var) = v.integer_decision() {
						int_eager_direct.insert(var);
					}
				}
			} else if let Some(c) =
				c.downcast_ref::<IntValArrayElement<model::View<IntVal>, model::View<IntVal>>>()
			{
				let index = c.0.index.resolve_alias(model);
				if let Some(var) = index.integer_decision() {
					int_eager_direct.insert(var);
				}
			}
		}

		// Create the mapping between model decisions and solver views.
		let mut map_builder = LoweringMapBuilder {
			bool_map: vec![None; model.bool_vars.len()],
			int_eager_direct,
			int_eager_limit,
			int_eager_order,
			int_map: vec![None; model.int_vars.len()],
		};

		// Ensure the creation of all integer variables.
		for (idx, _) in model.int_vars.iter().enumerate() {
			map_builder.get_or_create_int(model, &mut slv, model::Decision(idx as u32));
		}

		// Ensure the creation of all Boolean variables.
		for var in 1..=model.bool_vars.len() as u32 {
			let raw = RawLit::from_raw(NonZeroI32::new(var as i32).unwrap());
			map_builder.get_or_create_bool(model, &mut slv, model::Decision(raw).into());
		}

		// Finalize the reformulation map (all variables must be created by now)
		let map = map_builder.finalize();

		// Create constraint data structures within the solver
		let mut ctx = LoweringContext::new(&mut slv, &map, &model.trail);
		for c in model.constraints.iter().flatten() {
			c.to_solver(&mut ctx)?;
		}

		Ok((slv, map))
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
	///
	/// Model views belong to the modelling layer. Use this method after
	/// [`Model::lower`](crate::model::Model::lower) to obtain the
	/// corresponding solver view before querying solution values.
	///
	/// ```
	/// # use huub::{
	/// # 	model::Model,
	/// # 	solver::{Solver, Status, Valuation},
	/// # };
	/// # let mut model = Model::default();
	/// let model_x = model.new_int_decision(1..=3);
	/// let (mut solver, map): (Solver, _) = model.lower().to_solver()?;
	///
	/// let solver_x = map.get(&mut solver, model_x);
	/// let status = solver
	/// 	.solve()
	/// 	.on_solution(|solution| {
	/// 		assert!((1..=3).contains(&solver_x.val(solution)));
	/// 	})
	/// 	.satisfy();
	/// assert_eq!(status, Status::Satisfied);
	/// # Ok::<(), Box<dyn std::error::Error>>(())
	/// ```
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

	/// Perform [`Self::get`] for the more general
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
	/// Create the [`LoweringMap`] object ensuring that all variables have
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
				if lit.is_negated() { !view } else { view }
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

	/// Get the representation of an integer decision variable in the [`Solver`]
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

		let r = iv.resolve_alias(model);
		let view = match r.into_inner().0 {
			Const(c) => c.into(),
			Linear(lin) => {
				let var = Resolved(lin.var);
				let base = match self.int_map[var.idx()] {
					Some(v) => v,
					None => {
						let def = &model.int_vars[var.idx()];
						let Domain::Domain(dom) = &def.domain else {
							unreachable!()
						};
						let direct_enc = if self.int_eager_direct.contains(&var) {
							LiteralStrategy::Eager
						} else {
							LiteralStrategy::Lazy
						};
						let card = dom.card();
						let order_enc = if self.int_eager_order.contains(&var)
							|| self.int_eager_direct.contains(&var)
							|| card.is_some() && card.unwrap() <= self.int_eager_limit
						{
							LiteralStrategy::Eager
						} else {
							LiteralStrategy::Lazy
						};
						let view = slv
							.new_int_decision(dom.clone())
							.order_literals(order_enc)
							.direct_literals(direct_enc)
							.view();
						self.int_map[var.idx()] = Some(view);
						view
					}
				};
				base * lin.scale + lin.offset
			}
			Bool(lin) => {
				let bv = self.get_or_create_bool(model, slv, lin.var);
				bv * lin.scale + lin.offset
			}
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
