use std::{
	collections::HashMap,
	fmt,
	num::NonZeroI32,
	sync::{Arc, Mutex},
};

use huub::LitMeaning;
use tracing::field::{Field, Visit};
use tracing_subscriber::{
	field::{MakeVisitor, RecordFields, VisitOutput},
	fmt::{
		format::{DefaultFields, Writer},
		FormatFields,
	},
};
use ustr::Ustr;

pub type LitInt = NonZeroI32;
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LitName {
	BoolVar(Ustr, bool), // name, positive
	IntLit(usize, LitMeaning),
}

impl LitName {
	pub fn to_string(&self, int_map: &[Ustr]) -> String {
		match self {
			LitName::BoolVar(name, pos) => {
				format!("{}{name}", if *pos { "" } else { "not " })
			}
			LitName::IntLit(var, meaning) => {
				let var = int_map[*var];
				match meaning {
					LitMeaning::Eq(val) => format!("{var}={val}"),
					LitMeaning::NotEq(val) => format!("{var}!={val}"),
					LitMeaning::GreaterEq(val) => format!("{var}>={val}"),
					LitMeaning::Less(val) => format!("{var}<{val}"),
				}
			}
		}
	}
}

pub struct FmtLitFields {
	fmt: DefaultFields,
	lit_reverse_map: Arc<Mutex<HashMap<LitInt, LitName>>>,
	int_reverse_map: Arc<Mutex<Vec<Ustr>>>,
}

impl FmtLitFields {
	pub fn new(
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

/// A visitor wrapper that ensures any fields containing literals are renamed
/// to use their FlatZinc names
#[derive(Debug, Clone)]
struct LitNames<'a, V> {
	inner: V,
	lit_reverse_map: &'a HashMap<LitInt, LitName>,
	int_reverse_map: &'a Vec<Ustr>,
}

impl<'a, V> LitNames<'a, V> {
	/// Returns a new [`MakeVisitor`] implementation that will wrap `inner` so
	/// that any fields containing literals are renamed to use their FlatZinc
	/// names.
	///
	/// [`MakeVisitor`]: tracing_subscriber::field::MakeVisitor
	pub fn new(
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
		if matches!(field.name(), "lit" | "bool_var") {
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
		if matches!(field.name(), "int_var") {
			if let Some(name) = self.int_reverse_map.get(value as usize) {
				self.inner.record_str(field, name);
				return true;
			}
		}
		false
	}

	#[inline]
	fn check_clause(&mut self, field: &Field, value: &dyn fmt::Debug) -> bool {
		if matches!(field.name(), "clause") {
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
				self.inner.record_str(field, &v.join(" ∨ "));
				return true;
			}
		}
		false
	}
}

impl<'a, V: Visit> Visit for LitNames<'a, V> {
	#[inline]
	fn record_f64(&mut self, field: &Field, value: f64) {
		self.inner.record_f64(field, value)
	}

	#[inline]
	fn record_i64(&mut self, field: &Field, value: i64) {
		if self.check_lit(field, value) {
			return;
		}
		self.inner.record_i64(field, value)
	}

	#[inline]
	fn record_u64(&mut self, field: &Field, value: u64) {
		if self.check_int_var(field, value) || self.check_lit(field, value as i64) {
			return;
		}
		self.inner.record_u64(field, value)
	}

	#[inline]
	fn record_bool(&mut self, field: &Field, value: bool) {
		self.inner.record_bool(field, value)
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		self.inner.record_str(field, value)
	}

	#[inline]
	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		if self.check_clause(field, value) {
			return;
		}
		self.inner.record_debug(field, value)
	}
}

impl<T, V: VisitOutput<T>> VisitOutput<T> for LitNames<'_, V> {
	fn finish(self) -> T {
		self.inner.finish()
	}
}
