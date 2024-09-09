use std::{
	collections::HashMap,
	fmt::{self, Display},
	num::NonZeroI32,
	sync::{Arc, Mutex},
};

use huub::{IntVal, LitMeaning};
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

struct FmtLitFields {
	fmt: DefaultFields,
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
	int_reverse_map: Arc<Mutex<Vec<Ustr>>>,
}

type LitInt = NonZeroI32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LitName {
	BoolVar(Ustr, bool), // name, positive
	IntLit(usize, LitMeaning),
}

/// A visitor wrapper that ensures any fields containing literals are renamed
/// to use their FlatZinc names
#[derive(Debug, Clone)]
struct LitNames<'a, V> {
	inner: V,
	lit_reverse_map: &'a HashMap<LitInt, LitName>,
	int_reverse_map: &'a Vec<Ustr>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct RecordLazyLits {
	lazy_lit_message: bool,
	int_var: Option<usize>,
	eq_lit: Option<bool>,
	val: Option<IntVal>,
	lit: Option<LitInt>,
	other_values: bool,
}

struct RegisterLazyLits {
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
}

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
					LitMeaning::Eq(val) => format!("{var}={val}"),
					LitMeaning::NotEq(val) => format!("{var}≠{val}"),
					LitMeaning::GreaterEq(val) => format!("{var}≥{val}"),
					LitMeaning::Less(val) => format!("{var}<{val}"),
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

impl<'a, V: Visit> LitNames<'a, V> {
	#[inline]
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

	#[inline]
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
}

impl<'a, V: Visit> Visit for LitNames<'a, V> {
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

	#[inline]
	fn record_u64(&mut self, field: &Field, value: u64) {
		if self.check_int_var(field, value) || self.check_lit(field, value as i64) {
			return;
		}
		self.inner.record_u64(field, value);
	}

	#[inline]
	fn record_bool(&mut self, field: &Field, value: bool) {
		self.inner.record_bool(field, value);
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		self.inner.record_str(field, value);
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
}

impl<T, V: VisitOutput<T>> VisitOutput<T> for LitNames<'_, V> {
	fn finish(self) -> T {
		self.inner.finish()
	}
}

impl RecordLazyLits {
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
				LitMeaning::Eq
			} else {
				LitMeaning::GreaterEq
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

	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		match field.name() {
			"message" => self.lazy_lit_message = format!("{value:?}") == "register new literal",
			_ => self.other_values = true,
		}
	}
}

impl RegisterLazyLits {
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
