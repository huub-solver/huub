//! Module that contains the implementation of a custom [`tracing::Subscriber`]
//! for `huub`.

use std::{
	fmt::{self, Display},
	fs::OpenOptions,
	io::{self, Write},
	num::NonZeroI32,
	str::FromStr,
	sync::{Arc, Mutex},
};

use anstream::AutoStream;
use clap::ColorChoice;
use flatzinc_serde::{FlatZinc, Type, Variable};
use huub::{model::deserialize::flatzinc::FznIdent, solver::IntLitMeaning};
use rustc_hash::FxHashMap;
use tracing::{
	Event, Level, Subscriber,
	field::{Field, Visit},
	level_filters::LevelFilter,
};
use tracing_subscriber::{
	Layer,
	field::{MakeVisitor, RecordFields, VisitOutput},
	filter::Targets,
	fmt::{
		FormatFields, MakeWriter,
		format::{DefaultFields, Writer},
		time::uptime,
		writer::BoxMakeWriter,
	},
	layer::{Context, SubscriberExt},
};

use crate::cli::Cli;

/// A [`tracing_subscriber::FormatFields`] implementation that attempts to
/// format literals and integer variables according to their FlatZinc names,
/// formatting all other fields using a `DefaultFields` formatter.
struct FmtLitFields {
	/// The inner formatter that will be used to format fields that are not
	/// literals or integer variables.
	fmt: DefaultFields,
	/// The reverse map used to resolve the names of literals and integer
	/// variables.
	map: Arc<Mutex<ReverseMap>>,
}

/// Type alias of an integer type that can be used to represent literals.
type LitInt = NonZeroI32;

/// Definition of how a literal should be named.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitName {
	/// The literal represents a Boolean variable in the FlatZinc model.
	///
	/// The tuple contains the variable and whether the literal is the positive
	/// or negative version of the variable.
	BoolVar(VarRef, bool),
	/// The literal represents a condition on an integer variable.
	///
	/// The tuple contains the FlatZinc variable and the [`IntLitMeaning`] of
	/// the literal.
	IntLit(VarRef, IntLitMeaning),
}

/// A visitor wrapper that ensures any fields containing literals are renamed
/// to use their FlatZinc names
#[derive(Clone, Debug)]
struct LitNames<'a, V> {
	/// Inner visitor that will be used to format the fields.
	inner: V,
	/// The reverse map used to resolve the names of literals and integer
	/// variables.
	map: &'a ReverseMap,
}

/// Visitor that collects the fields of a `"reverse_map"`-target registration
/// message, which the subscriber uses to build the reverse mappings.
///
/// The solver emits, before any literal is used in a clause: the FlatZinc
/// identifier of each model decision, the mapping from a model integer decision
/// to its solver integer variable, the eager literals of an integer variable, a
/// Boolean-backed integer, a Boolean decision, and, during solving, lazily
/// created literals.
#[derive(Debug, Default)]
struct RegistrationEvent {
	/// The kind of registration, classified from the event's message
	/// ([`None`] if the message is not a known registration).
	message: Option<RegistrationKind>,
	/// The index of the FlatZinc variable.
	fzn: Option<u32>,
	/// The index of the model decision.
	model: Option<u32>,
	/// The index of the solver integer variable.
	int_var: Option<u32>,
	/// The first code of the eager order-literal range (`0` when absent).
	order: Option<i32>,
	/// The first code of the eager equality-literal range (`0` when absent).
	eq: Option<i32>,
	/// The domain of an integer variable, as a flat list of inclusive range
	/// bounds (`[lb0, ub0, lb1, ub1, ...]`).
	dom: Option<Vec<i64>>,
	/// A single literal code.
	lit: Option<i32>,
	/// The value for a Boolean-backed integer's `>=` order literal.
	geq: Option<i64>,
	/// Whether a lazily created literal is an equality (`true`) or order
	/// (`false`) literal.
	is_eq: Option<bool>,
	/// The value of a lazily created literal.
	val: Option<i64>,
}

/// The kind of registration described by a `"reverse_map"` event, classified
/// from its message so that dispatch is a match on a [`Copy`] discriminant
/// rather than a string comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RegistrationKind {
	/// `register model decision`: a model decision and its FlatZinc variable.
	ModelDecision,
	/// `register solver bool`: a solver Boolean literal for a model Boolean
	/// decision.
	SolverBool,
	/// `register solver bool-backed int`: a solver Boolean literal representing
	/// a model integer decision.
	SolverBoolAsInt,
	/// `register solver int`: a model integer decision and its solver integer
	/// variable.
	SolverInt,
	/// `register solver int eager lits`: the eager literals of a solver integer
	/// variable.
	SolverIntEager,
	/// `register solver int lazy lit`: a lazily created literal of an integer
	/// variable.
	SolverIntLazy,
}

/// The reverse mappings from the solver's (and model's) representation of
/// decisions and literals back to the FlatZinc decision variables.
///
/// Shared as an `Arc<Mutex<ReverseMap>>`, so that all of the mappings are
/// guarded together by a single lock: a registration event, which may touch
/// several of them, is applied atomically. It is populated by a
/// [`ReverseMapLayer`] and read by the formatter through
/// the model-level ([`ReverseMap::model_int`], [`ReverseMap::model_bool`]) and
/// solver-level ([`ReverseMap::solver_int`], [`ReverseMap::solver_lit`]) lookup
/// methods.
#[derive(Debug, Default)]
pub(crate) struct ReverseMap {
	/// The FlatZinc variable of each model integer decision, keyed by its model
	/// index.
	model_int_names: FxHashMap<u32, VarRef>,
	/// The FlatZinc variable of each model Boolean decision, keyed by its model
	/// index.
	model_bool_names: FxHashMap<u32, VarRef>,
	/// The FlatZinc variable of each solver integer variable, indexed by the
	/// solver's integer-variable index.
	solver_int_names: Vec<Option<VarRef>>,
	/// The name and meaning of each solver literal, keyed by its (signed) code.
	solver_lits: FxHashMap<LitInt, LitName>,
}

/// A [`tracing_subscriber::Layer`] that builds the reverse mappings from the
/// registration messages emitted on the `"reverse_map"` target.
///
/// The layer owns the parsed FlatZinc instance (kept out of the shared
/// [`ReverseMap`]) and writes the resolved names into it.
pub(crate) struct ReverseMapLayer {
	/// The parsed FlatZinc instance, shared (rather than copied) so that its
	/// decision variables are resolved using the indexes as in
	/// [`FlatZinc::variables`](flatzinc_serde::FlatZinc::variables).
	fzn: Arc<FlatZinc<FznIdent>>,
	/// The shared reverse map that this layer populates.
	map: Arc<Mutex<ReverseMap>>,
}

/// Type alias for a shared reference to a FlatZinc decision variable, reused
/// from the parsed [`FlatZinc`](flatzinc_serde::FlatZinc) instance so that its
/// name is not re-allocated when building the reverse mappings.
pub(crate) type VarRef = Arc<Variable<FznIdent>>;

/// Create a [`tracing_subscriber::Subscriber`] specialized for `huub`.
///
/// The given subscriber additionally formats literals and integer variables
/// using the name mappings provided by `map`. A [`ReverseMapLayer`] is
/// registered to build those mappings from the registration messages emitted on
/// the `"reverse_map"` target, reusing the decision variables of the shared
/// `fzn` instance to resolve them without re-allocating names.
pub(crate) fn create_subscriber<W>(
	verbose: u8,
	trace_targets: &[String],
	make_writer: W,
	ansi: bool,
	map: &Arc<Mutex<ReverseMap>>,
	fzn: Arc<FlatZinc<FznIdent>>,
) -> impl Subscriber
where
	W: for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
{
	let selected_level = match verbose {
		0 => Level::INFO,
		1 => Level::DEBUG,
		_ => Level::TRACE, // 2 or more
	};
	let mut filter = Targets::new();
	for target in trace_targets {
		filter = filter.with_target(target.as_str(), selected_level);
	}

	// Builder for the formatting subscriber
	let fmt_layer = tracing_subscriber::fmt::layer()
		.with_writer(make_writer)
		.with_ansi(ansi)
		.with_timer(uptime())
		.map_fmt_fields(|fmt| FmtLitFields::new(fmt, Arc::clone(map)))
		.with_filter(filter);

	tracing_subscriber::registry()
		.with(
			ReverseMapLayer::new(fzn, Arc::clone(map)).with_filter(Targets::new().with_target(
				"reverse_map",
				if verbose > 0 {
					Level::TRACE.into()
				} else {
					LevelFilter::OFF
				},
			)),
		)
		.with(fmt_layer)
}

/// Parse a [`Debug`]-formatted list of integers, e.g. `[1, -2, 3]`, as produced
/// by recording a slice of integers on a tracing event with the `?` sigil.
///
/// Returns [`None`] when the formatted value is not a bracketed list whose
/// elements all parse as `T`. This lets callers distinguish an integer list
/// from an unrelated value that merely shares a field-name prefix (e.g. a
/// `reason` field whose `Debug` is `false` or `lazy` rather than `[1, 2]`).
///
/// [`Debug`]: fmt::Debug
pub(crate) fn parse_int_list<T: FromStr>(value: &dyn fmt::Debug) -> Option<Vec<T>> {
	let formatted = format!("{value:?}");
	let inner = formatted.strip_prefix('[')?.strip_suffix(']')?.trim();
	if inner.is_empty() {
		return Some(Vec::new());
	}
	inner
		.split(',')
		.map(|item| item.trim().parse().ok())
		.collect()
}

impl Cli<'_> {
	/// Collect the active tracing targets after applying user overrides.
	pub(crate) fn trace_targets(&self) -> Vec<String> {
		let mut trace_targets = vec!["solver".to_owned(), "flatzinc".to_owned()];
		trace_targets.extend(self.trace_target.iter().cloned());
		for target in &self.no_trace_target {
			trace_targets.retain(|value| value != target);
		}
		trace_targets
	}

	/// Build the tracing writer and whether ANSI colors should be enabled.
	pub(crate) fn trace_writer(&self) -> Result<(BoxMakeWriter, bool), String> {
		match &self.log_file {
			Some(path) => {
				let file = OpenOptions::new()
					.create(true)
					.write(true)
					.truncate(true)
					.open(path)
					.map_err(|err| {
						format!("Unable to open log file “{}”: {err}", path.display())
					})?;
				Ok((BoxMakeWriter::new(Arc::new(file)), false))
			}
			None => Ok((
				BoxMakeWriter::new(io::stderr),
				match self.color {
					ColorChoice::Always => true,
					ColorChoice::Never => false,
					ColorChoice::Auto => !matches!(
						AutoStream::choice(&io::stderr()),
						anstream::ColorChoice::Never
					),
				},
			)),
		}
	}
}

impl FmtLitFields {
	/// Create a new [`FmtLitField`] formatter based on the given `fmt`, using
	/// names for literals and integer variables based on the given `map`.
	fn new(fmt: DefaultFields, map: Arc<Mutex<ReverseMap>>) -> Self {
		Self { fmt, map }
	}
}

impl<'writer> FormatFields<'writer> for FmtLitFields {
	fn format_fields<R: RecordFields>(&self, writer: Writer<'writer>, fields: R) -> fmt::Result {
		let map = self.map.lock().unwrap();
		let mut v = LitNames::new(self.fmt.make_visitor(writer), &map);
		fields.record(&mut v);
		v.finish()
	}
}

impl Display for LitName {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			LitName::BoolVar(var, pos) => {
				write!(f, "{}{}", if *pos { "" } else { "not " }, var.name)
			}
			LitName::IntLit(var, meaning) => match meaning {
				IntLitMeaning::Eq(val) => write!(f, "{}={val}", var.name),
				IntLitMeaning::NotEq(val) => write!(f, "{}≠{val}", var.name),
				IntLitMeaning::GreaterEq(val) => write!(f, "{}≥{val}", var.name),
				IntLitMeaning::Less(val) => write!(f, "{}<{val}", var.name),
			},
		}
	}
}

impl<V: Visit> LitNames<'_, V> {
	/// Check if the field should and can be formatted as a clause or a list of
	/// literals.
	#[inline]
	fn check_clause(&mut self, field: &Field, value: &dyn fmt::Debug) -> bool {
		if (field.name().starts_with("clause")
			|| field.name().starts_with("conj")
			|| field.name().starts_with("lits")
			|| field.name().starts_with("reason"))
			&& let Some(clause) = parse_int_list::<i32>(value)
		{
			let mut v: Vec<String> = Vec::with_capacity(clause.len());
			for i in clause {
				if let Some(l) = self.map.solver_lit(NonZeroI32::new(i).unwrap()) {
					v.push(l.to_string());
				} else {
					v.push(format!("Lit({i})"));
				}
			}
			self.inner.record_str(
				field,
				&v.join(if field.name().starts_with("clause") {
					" ∨ "
				} else if field.name().starts_with("conj") || field.name().starts_with("reason") {
					" ∧ "
				} else {
					", "
				}),
			);
			return true;
		}
		false
	}

	/// Check if the field should and can be formatted as an integer variable.
	#[inline]
	fn check_int_var(&mut self, field: &Field, value: u64) -> bool {
		if field.name().starts_with("int_var")
			&& let Some(var) = self.map.solver_int(value as usize)
		{
			self.inner.record_str(field, &var.name);
			return true;
		}
		false
	}

	/// Check whether the field should and can be formatted as a list of integer
	/// variables.
	#[inline]
	fn check_int_vars(&mut self, field: &Field, value: &dyn fmt::Debug) -> bool {
		if field.name().starts_with("int_vars")
			&& let Some(vars) = parse_int_list::<usize>(value)
		{
			let mut v: Vec<String> = Vec::with_capacity(vars.len());
			for i in vars {
				if let Some(var) = self.map.solver_int(i) {
					v.push(var.name.clone());
				} else {
					v.push(format!("IntVar({i})"));
				}
			}
			self.inner.record_str(field, &v.join(", "));
			return true;
		}
		false
	}
	/// Check if the field should and can be formatted as a literal.
	#[inline]
	fn check_lit(&mut self, field: &Field, value: i64) -> bool {
		if field.name().starts_with("lit") | field.name().starts_with("bool_var") {
			if value == 0 || value < i32::MIN as i64 || value > i32::MAX as i64 {
				return false;
			}
			if let Some(name) = self.map.solver_lit(NonZeroI32::new(value as i32).unwrap()) {
				self.inner.record_str(field, &name.to_string());
				return true;
			}
		}
		false
	}
}

impl<'a, V> LitNames<'a, V> {
	/// Returns a new [`MakeVisitor`] implementation that will wrap `inner` so
	/// that any fields containing literals are renamed to use their FlatZinc
	/// names.
	///
	/// [`MakeVisitor`]: tracing_subscriber::field::MakeVisitor
	fn new(inner: V, map: &'a ReverseMap) -> Self {
		LitNames { inner, map }
	}
}

impl<V: Visit> Visit for LitNames<'_, V> {
	#[inline]
	fn record_bool(&mut self, field: &Field, value: bool) {
		self.inner.record_bool(field, value);
	}

	#[inline]
	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		if self.check_clause(field, value) {
			return;
		}
		if self.check_int_vars(field, value) {
			return;
		}
		self.inner.record_debug(field, value);
	}
	#[inline]
	fn record_f64(&mut self, field: &Field, value: f64) {
		self.inner.record_f64(field, value);
	}

	#[inline]
	fn record_i64(&mut self, field: &Field, value: i64) {
		if self.check_lit(field, value) {
			return;
		}
		self.inner.record_i64(field, value);
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		self.inner.record_str(field, value);
	}

	#[inline]
	fn record_u64(&mut self, field: &Field, value: u64) {
		if self.check_int_var(field, value) || self.check_lit(field, value as i64) {
			return;
		}
		self.inner.record_u64(field, value);
	}
}

impl<T, V: VisitOutput<T>> VisitOutput<T> for LitNames<'_, V> {
	fn finish(self) -> T {
		self.inner.finish()
	}
}

impl Visit for RegistrationEvent {
	fn record_bool(&mut self, field: &Field, value: bool) {
		if field.name() == "is_eq" {
			self.is_eq = Some(value);
		}
	}

	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		match field.name() {
			"message" => {
				// Write message on the stack to avoid heap allocation, and immediately
				// convert it to a `RegistrationKind`.
				const CAP: usize = "register solver bool-backed int".len();
				let mut buf = [0_u8; CAP];
				let mut tail: &mut [u8] = &mut buf;
				if write!(tail, "{value:?}").is_ok() {
					let len = CAP - tail.len();
					self.message = RegistrationKind::from_message(&buf[..len]);
				}
			}
			"dom" => self.dom = parse_int_list(value),
			_ => {}
		}
	}

	fn record_i64(&mut self, field: &Field, value: i64) {
		match field.name() {
			"order" => self.order = i32::try_from(value).ok(),
			"eq" => self.eq = i32::try_from(value).ok(),
			"lit" => self.lit = i32::try_from(value).ok().filter(|&c| c != 0),
			"geq" => self.geq = Some(value),
			"val" => self.val = Some(value),
			_ => {}
		}
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		match field.name() {
			"fzn" => self.fzn = u32::try_from(value).ok(),
			"model" => self.model = u32::try_from(value).ok(),
			"int_var" => self.int_var = u32::try_from(value).ok(),
			_ => self.record_i64(field, value as i64),
		}
	}
}

impl RegistrationKind {
	/// Classify a `"reverse_map"` message into its kind, or [`None`] when the
	/// message is not a known registration.
	fn from_message(message: &[u8]) -> Option<Self> {
		Some(match message {
			b"register model decision" => Self::ModelDecision,
			b"register solver bool" => Self::SolverBool,
			b"register solver bool-backed int" => Self::SolverBoolAsInt,
			b"register solver int eager lits" => Self::SolverIntEager,
			b"register solver int lazy lit" => Self::SolverIntLazy,
			b"register solver int" => Self::SolverInt,
			_ => return None,
		})
	}
}

impl ReverseMap {
	/// Register the integer literal `lit` (and its negation) as the given
	/// meaning of `var`.
	fn insert_int_lit(&mut self, lit: i32, var: &VarRef, m: IntLitMeaning) {
		let lit = NonZeroI32::new(lit).unwrap();
		let _ = self
			.solver_lits
			.insert(lit, LitName::IntLit(Arc::clone(var), m));
		let _ = self
			.solver_lits
			.insert(-lit, LitName::IntLit(Arc::clone(var), !m));
	}

	/// Look up the FlatZinc variable of the model Boolean decision at `index`.
	pub(crate) fn model_bool(&self, index: u32) -> Option<&VarRef> {
		self.model_bool_names.get(&index)
	}

	/// Look up the FlatZinc variable of the model integer decision at `index`.
	pub(crate) fn model_int(&self, index: u32) -> Option<&VarRef> {
		self.model_int_names.get(&index)
	}

	/// Create a new, empty shared reverse map.
	pub(crate) fn new() -> Arc<Mutex<Self>> {
		Arc::default()
	}

	/// Update the reverse mappings according to a single registration event,
	/// using `fzn` to resolve the events into their shared decision variables.
	fn register(&mut self, fzn: &FlatZinc<FznIdent>, event: RegistrationEvent) {
		match event.message {
			Some(RegistrationKind::ModelDecision) => {
				let (Some(idx), Some(model)) = (event.fzn, event.model) else {
					return;
				};
				// Reuse the shared FlatZinc variable rather than allocating a
				// fresh copy of its name. Its type determines whether the model
				// decision is an integer or a Boolean one.
				let Some(var) = fzn.variables.get(idx as usize).cloned() else {
					return;
				};
				match var.ty {
					Type::Bool => {
						let _ = self.model_bool_names.insert(model, var);
					}
					Type::Int(_) => {
						let _ = self.model_int_names.insert(model, var);
					}
					// Other variable types do not emit a name registration.
					_ => {}
				}
			}
			Some(RegistrationKind::SolverInt) => {
				let (Some(model), Some(int_var)) = (event.model, event.int_var) else {
					return;
				};
				let Some(var) = self.model_int(model).cloned() else {
					return;
				};
				if int_var as usize >= self.solver_int_names.len() {
					self.solver_int_names.resize(int_var as usize + 1, None);
				}
				self.solver_int_names[int_var as usize] = Some(var);
			}
			Some(RegistrationKind::SolverIntEager) => {
				let (Some(int_var), Some(dom)) = (event.int_var, event.dom) else {
					return;
				};
				let Some(var) = self.solver_int(int_var as usize).cloned() else {
					return;
				};
				// `dom` is a flat list of inclusive range bounds; the domain values
				// in ascending order are the concatenation of those ranges.
				let values = || dom.as_chunks::<2>().0.iter().flat_map(|c| c[0]..=c[1]);
				// The order literal at `order + k` means `< values[k + 1]`, so one is
				// created for every domain value except the first.
				if let Some(order) = event.order.filter(|&o| o != 0) {
					for (k, val) in values().skip(1).enumerate() {
						self.insert_int_lit(order + k as i32, &var, IntLitMeaning::Less(val));
					}
				}
				// The equality literal at `eq + k` means `== values[k + 1]`, so one is
				// created for every domain value except the first and the last.
				if let Some(eq) = event.eq.filter(|&e| e != 0) {
					let mut it = values();
					it.next_back();
					for (k, val) in it.skip(1).enumerate() {
						self.insert_int_lit(eq + k as i32, &var, IntLitMeaning::Eq(val));
					}
				}
			}
			Some(RegistrationKind::SolverBoolAsInt) => {
				let (Some(model), Some(lit), Some(geq)) = (event.model, event.lit, event.geq)
				else {
					return;
				};
				let Some(var) = self.model_int(model).cloned() else {
					return;
				};
				self.insert_int_lit(lit, &var, IntLitMeaning::GreaterEq(geq));
			}
			Some(RegistrationKind::SolverBool) => {
				let (Some(model), Some(lit)) = (event.model, event.lit) else {
					return;
				};
				let Some(var) = self.model_bool(model).cloned() else {
					return;
				};
				let lit = NonZeroI32::new(lit).unwrap();
				let _ = self
					.solver_lits
					.insert(lit, LitName::BoolVar(Arc::clone(&var), true));
				let _ = self.solver_lits.insert(-lit, LitName::BoolVar(var, false));
			}
			Some(RegistrationKind::SolverIntLazy) => {
				let (Some(int_var), Some(is_eq), Some(val), Some(lit)) =
					(event.int_var, event.is_eq, event.val, event.lit)
				else {
					return;
				};
				let Some(var) = self.solver_int(int_var as usize).cloned() else {
					return;
				};
				let meaning = if is_eq {
					IntLitMeaning::Eq
				} else {
					IntLitMeaning::Less
				}(val);
				self.insert_int_lit(lit, &var, meaning);
			}
			None => {}
		}
	}

	/// Look up the FlatZinc variable of the solver integer variable at `index`.
	pub(crate) fn solver_int(&self, index: usize) -> Option<&VarRef> {
		self.solver_int_names.get(index).and_then(Option::as_ref)
	}

	/// Look up the name and meaning of the solver literal with the given
	/// `code`.
	pub(crate) fn solver_lit(&self, code: LitInt) -> Option<&LitName> {
		self.solver_lits.get(&code)
	}
}

impl ReverseMapLayer {
	/// Create a new [`ReverseMapLayer`] that reuses the decision variables of
	/// the given FlatZinc instance to resolve registration events into `map`.
	pub(crate) fn new(fzn: Arc<FlatZinc<FznIdent>>, map: Arc<Mutex<ReverseMap>>) -> Self {
		Self { fzn, map }
	}
}

impl<S: Subscriber> Layer<S> for ReverseMapLayer {
	fn on_event(&self, event: &Event<'_>, _: Context<'_, S>) {
		let mut rec = RegistrationEvent::default();
		event.record(&mut rec);
		self.map.lock().unwrap().register(&self.fzn, rec);
	}
}

#[cfg(test)]
mod tests {
	use crate::cli::Cli;

	#[test]
	fn trace_target_overrides() {
		let cli = Cli::try_parse_from([
			"huub",
			"--trace-target",
			"brancher",
			"--no-trace-target",
			"solver",
			"instance.fzn.json",
		])
		.unwrap();

		assert_eq!(
			cli.trace_targets(),
			vec!["flatzinc".to_owned(), "brancher".to_owned()]
		);
	}
}
