//! Module that contains the implementation of a custom [`tracing::Subscriber`]
//! for `fzn-huub`.

use std::{
	collections::HashMap,
	fmt::{self, Display},
	num::NonZeroI32,
	sync::{Arc, Mutex},
};

use huub::{solver::IntLitMeaning, IntVal};
use tracing::{
	field::{Field, Visit},
	Event, Level, Subscriber,
};
use tracing_subscriber::{
	field::{MakeVisitor, RecordFields, VisitOutput},
	fmt::{
		format::{DefaultFields, Writer},
		time::uptime,
		FormatFields, MakeWriter,
	},
	layer::{Context, SubscriberExt},
	Layer,
};
use ustr::Ustr;

/// A [`tracing_subscriber::FormatFields`] implementation that attempts to
/// format literals and integer variables according to their FlatZinc names,
/// formatting all other fields using a `DefaultFields` formatter.
struct FmtLitFields {
	/// The inner formatter that will be used to format fields that are not
	/// literals or integer variables.
	fmt: DefaultFields,
	/// The mapping from integers representing literals to the definitions of
	/// their names.
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
	/// The mapping from indexes of integer variables to their names.
	int_reverse_map: Arc<Mutex<Vec<Ustr>>>,
}

/// Type alias of an integer type that can be used to represent literals.
type LitInt = NonZeroI32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Definition of how a literal should be named.
pub(crate) enum LitName {
	/// The literal represents a Boolean variable in the FlatZinc model.
	///
	/// The tuple constrains the name of the variable and whether the literal is
	/// the positive of negative version of the variable.
	BoolVar(Ustr, bool),
	/// The literal represents a condition of an integer variable.
	///
	/// The tuple contains the index of the variable in the FlatZinc model (which
	/// is used as the key in [`FmtLitFields::int_reverse_map`]), and
	/// [`LitMeaning`] of the literal.
	IntLit(usize, IntLitMeaning),
}

/// A visitor wrapper that ensures any fields containing literals are renamed
/// to use their FlatZinc names
#[derive(Debug, Clone)]
struct LitNames<'a, V> {
	/// Inner visitor that will be used to format the fields.
	inner: V,
	/// The mapping from integers representing literals to the definitions of
	/// their names.
	lit_reverse_map: &'a HashMap<LitInt, LitName>,
	/// The mapping from indexes of integer variables to their names.
	int_reverse_map: &'a Vec<Ustr>,
}

#[derive(Debug, Default, PartialEq, Eq)]
/// Structure used to parse log messages informing the subscriber about a new
/// literal that has been created.
struct RecordLazyLits {
	/// Whether the log message had the "register new literal" message.
	lazy_lit_message: bool,
	/// The the `int_var` field of the log message, if any.
	int_var: Option<usize>,
	/// The `is_eq` field of the log message, if any.
	eq_lit: Option<bool>,
	/// The `val` field of the log message, if any.
	val: Option<IntVal>,
	/// The `lit` field of the log message, if any.
	lit: Option<LitInt>,
	/// Whether the log message contains any unexpected fields.
	other_values: bool,
}

/// A [`tracing_subscriber::Layer`] that registers the names of lazily created
/// literals for any future log messages.
struct RegisterLazyLits {
	/// A mapping from the literals to a definition of a literal name.
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
}

/// Create a [`tracing_subscriber::Subscriber`] specialized for `fzn-huub`.
///
/// The given subscriber additionally formats literals and integer variables
/// using the name mapping provided by `lit_reverse_map` and `int_reverse_map`.
pub(crate) fn create_subscriber<W>(
	verbose: u8,
	make_writer: W,
	ansi: bool,
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
	int_reverse_map: Arc<Mutex<Vec<Ustr>>>,
) -> impl Subscriber
where
	W: for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
{
	// Builder for the formatting subscriber
	let builder = tracing_subscriber::fmt()
		.with_max_level(match verbose {
			0 => Level::INFO,
			1 => Level::DEBUG,
			_ => Level::TRACE, // 2 or more
		})
		.with_writer(make_writer)
		.with_ansi(ansi)
		.with_timer(uptime())
		.map_fmt_fields(|fmt| {
			FmtLitFields::new(fmt, Arc::clone(&lit_reverse_map), int_reverse_map)
		});

	// Create final subscriber and add the layer that will register new lazily created literals
	builder
		.finish()
		.with(RegisterLazyLits::new(lit_reverse_map))
}

impl FmtLitFields {
	/// Create a new [`FmtLitField`] formatter based on the given `fmt`, using
	/// names for literals based on the given `lit_reverse_map` and
	/// `int_reverse_map`.
	fn new(
		fmt: DefaultFields,
		lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
		int_reverse_map: Arc<Mutex<Vec<Ustr>>>,
	) -> Self {
		Self {
			fmt,
			lit_reverse_map,
			int_reverse_map,
		}
	}
}

impl<'writer> FormatFields<'writer> for FmtLitFields {
	fn format_fields<R: RecordFields>(&self, writer: Writer<'writer>, fields: R) -> fmt::Result {
		let lit_map = self.lit_reverse_map.lock().unwrap();
		let int_map = self.int_reverse_map.lock().unwrap();
		let mut v = LitNames::new(self.fmt.make_visitor(writer), &lit_map, &int_map);
		fields.record(&mut v);
		v.finish()
	}
}

impl LitName {
	/// Returns a string representation of the literal using the FlatZinc names.
	fn to_string(&self, int_map: &[Ustr]) -> String {
		match self {
			LitName::BoolVar(name, pos) => {
				format!("{}{name}", if *pos { "" } else { "not " })
			}
			LitName::IntLit(var, meaning) => {
				let var: &dyn Display = if int_map.len() > *var {
					&int_map[*var]
				} else {
					&format!("int_var[{var}]")
				};
				match meaning {
					IntLitMeaning::Eq(val) => format!("{var}={val}"),
					IntLitMeaning::NotEq(val) => format!("{var}≠{val}"),
					IntLitMeaning::GreaterEq(val) => format!("{var}≥{val}"),
					IntLitMeaning::Less(val) => format!("{var}<{val}"),
				}
			}
		}
	}
}

impl<'a, V> LitNames<'a, V> {
	/// Returns a new [`MakeVisitor`] implementation that will wrap `inner` so
	/// that any fields containing literals are renamed to use their FlatZinc
	/// names.
	///
	/// [`MakeVisitor`]: tracing_subscriber::field::MakeVisitor
	fn new(
		inner: V,
		lit_reverse_map: &'a HashMap<LitInt, LitName>,
		int_reverse_map: &'a Vec<Ustr>,
	) -> Self {
		LitNames {
			inner,
			lit_reverse_map,
			int_reverse_map,
		}
	}
}

impl<V: Visit> LitNames<'_, V> {
	#[inline]
	/// Check if the field should and can be formatted as a clause or a list of
	/// literals.
	fn check_clause(&mut self, field: &Field, value: &dyn fmt::Debug) -> bool {
		if field.name().starts_with("clause") || field.name().starts_with("lits") {
			let res: Result<Vec<i32>, _> = serde_json::from_str(&format!("{:?}", value));
			if let Ok(clause) = res {
				let mut v: Vec<String> = Vec::with_capacity(clause.len());
				for i in clause {
					if let Some(l) = self.lit_reverse_map.get(&NonZeroI32::new(i).unwrap()) {
						v.push(l.to_string(self.int_reverse_map));
					} else {
						v.push(format!("Lit({})", i));
					}
				}
				if field.name() == "clause" {
					self.inner.record_str(field, &v.join(" ∨ "));
				} else {
					self.inner.record_str(field, &v.join(", "));
				}
				return true;
			}
		}
		false
	}

	#[inline]
	/// Check if the field should and can be formatted as an integer variable.
	fn check_int_var(&mut self, field: &Field, value: u64) -> bool {
		if field.name().starts_with("int_var") {
			if let Some(name) = self.int_reverse_map.get(value as usize) {
				self.inner.record_str(field, name);
				return true;
			}
		}
		false
	}

	#[inline]
	/// Check whether the field should and can be formatted as a list of integer
	/// variables.
	fn check_int_vars(&mut self, field: &Field, value: &dyn fmt::Debug) -> bool {
		if field.name().starts_with("int_vars") {
			let res: Result<Vec<usize>, _> = serde_json::from_str(&format!("{:?}", value));
			if let Ok(vars) = res {
				let mut v: Vec<String> = Vec::with_capacity(vars.len());
				for i in vars {
					if let Some(name) = self.int_reverse_map.get(i) {
						v.push(name.to_string());
					} else {
						v.push(format!("IntVar({})", i));
					}
				}
				self.inner.record_str(field, &v.join(", "));
				return true;
			}
		}
		false
	}
	#[inline]
	/// Check if the field should and can be formatted as a literal.
	fn check_lit(&mut self, field: &Field, value: i64) -> bool {
		if field.name().starts_with("lit") | field.name().starts_with("bool_var") {
			if let Some(name) = self
				.lit_reverse_map
				.get(&NonZeroI32::new(value as i32).unwrap())
			{
				self.inner
					.record_str(field, &name.to_string(self.int_reverse_map));
				return true;
			}
		}
		false
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

impl RecordLazyLits {
	/// This method is called when the [`Visit`] implementation has been called.
	/// If the visited fields match the expected fields of log message for a new
	/// literal, then the method will register the literal in the
	/// `lit_reverse_map` and return `true`. Otherwise, it will return `false`.
	fn finish(self, lit_reverse_map: &Arc<Mutex<HashMap<LitInt, LitName>>>) -> bool {
		if self.other_values {
			return false;
		}
		if let (true, Some(iv), Some(is_eq), Some(val), Some(lit)) = (
			self.lazy_lit_message,
			self.int_var,
			self.eq_lit,
			self.val,
			self.lit,
		) {
			let meaning = if is_eq {
				IntLitMeaning::Eq
			} else {
				IntLitMeaning::Less
			}(val);
			let mut guard = lit_reverse_map.lock().unwrap();
			let _ = guard.insert(lit, LitName::IntLit(iv, meaning.clone()));
			let _ = guard.insert(-lit, LitName::IntLit(iv, !meaning));
			true
		} else {
			false
		}
	}
}

impl Visit for RecordLazyLits {
	fn record_bool(&mut self, field: &Field, value: bool) {
		match field.name() {
			"is_eq" => self.eq_lit = Some(value),
			_ => self.other_values = true,
		}
	}

	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		match field.name() {
			"message" => self.lazy_lit_message = format!("{value:?}") == "register new literal",
			_ => self.other_values = true,
		}
	}

	fn record_i64(&mut self, field: &Field, value: i64) {
		match field.name() {
			"lit" => self.lit = Some(NonZeroI32::new(value as i32).unwrap()),
			"val" => self.val = Some(value),
			_ => self.other_values = true,
		}
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		match field.name() {
			"lit" => self.lit = Some(NonZeroI32::new(value as i32).unwrap()),
			"int_var" => self.int_var = Some(value as usize),
			"val" => self.val = Some(value as i64),
			_ => self.other_values = true,
		}
	}
}

impl RegisterLazyLits {
	/// Create a new instance of the [`RegisterLazyLits`] layer.
	fn new(lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>) -> Self {
		Self { lit_reverse_map }
	}
}

impl<S: Subscriber> Layer<S> for RegisterLazyLits {
	fn event_enabled(&self, event: &Event<'_>, _: Context<'_, S>) -> bool {
		let mut rec = RecordLazyLits::default();
		event.record(&mut rec);
		!rec.finish(&self.lit_reverse_map)
	}
}
