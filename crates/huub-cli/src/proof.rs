//! Module containing the [`tracing_subscriber::Layer`] implementations that
//! format the events emitted on the `"proof"` target by the `huub` solver
//! into proof files.
//!
//! Two proof formats are supported:
//!
//! - The Deletion Reverse Constraint Propagation (DRCP) format, which describes
//!   the proof in terms of atomic constraints `[x op v]` on the decision
//!   variables. This format is produced by the [`DrcpWriterLayer`].
//! - The VeriPB pseudo-Boolean (`.pbp`) format, which describes the proof in
//!   terms of pseudo-Boolean constraints over the Boolean literals created by
//!   the solver. This format is produced by the [`VeripbWriterLayer`].

use std::{
	fmt,
	fs::File,
	io::{self, BufWriter, Write},
	num::NonZeroI32,
	path::PathBuf,
	sync::{Arc, Mutex},
};

use huub::solver::IntLitMeaning;
use rustc_hash::FxHashSet;
use tracing::{
	Event, Subscriber,
	field::{Field, Visit},
};
use tracing_subscriber::layer::{Context, Layer};

use crate::{
	cli::{CliProofFormat, CliProofLiteralNames, ProofConfig},
	trace::{LitName, ReverseMap, parse_int_list},
};

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the DRCP format.
///
/// The proof steps are streamed directly to the proof file, while the atom
/// definitions are written to a companion literal-definition file (with a
/// `.lits` extension) when the proof is concluded.
pub(crate) struct DrcpWriterLayer {
	/// The literals used in the proof, together with the reverse mappings
	/// needed to resolve their meanings for the companion file.
	defs: LitDefs,
	/// Whether the atom definitions are written inline in the proof file
	/// instead of in a companion file.
	inline: bool,
	/// The path of the companion literal-definition file (unused when
	/// `inline`).
	lits_path: PathBuf,
	/// The writer of the proof steps (the proof file itself).
	out: Mutex<BufWriter<File>>,
	/// The identifiers of the literal-definition clauses that are omitted from
	/// the proof, so that they can also be dropped from the propagation hints
	/// of later derived clauses.
	skipped: Mutex<FxHashSet<i64>>,
}

/// The literals used in a proof, together with the reverse mappings needed to
/// resolve their meanings once the proof is concluded.
struct LitDefs {
	/// The reverse map used to resolve the names of literals and integer
	/// variables.
	map: Arc<Mutex<ReverseMap>>,
	/// The set of (positive) literal codes used in the proof steps.
	used: Mutex<FxHashSet<i32>>,
}

/// A visitor that collects the fields of an event emitted on the `"proof"`
/// target.
#[derive(Debug, Default)]
struct ProofEvent {
	/// The antecedent clause identifiers of a derived clause.
	antecedents: Vec<i64>,
	/// The literals of the clause, represented as non-zero integers.
	clause: Vec<i32>,
	/// The indices of the user constraints from which the clause stems.
	constraints: Vec<u32>,
	/// The name of the solver rule or constraint from which the clause stems.
	hint: String,
	/// The identifier of the clause (as given by the SAT oracle).
	id: i64,
	/// The event message, identifying the kind of proof event.
	message: String,
	/// Whether the objective of the `end proof` event was minimized.
	minimize: bool,
	/// The FlatZinc identifier of the objective decision, if any.
	obj_name: Option<String>,
	/// The objective value reported by the `end proof` event, present only when
	/// the problem is optimized and a dual bound can be concluded.
	objective: Option<i64>,
	/// The literal that is propagated by the clause, or `0` if the clause does
	/// not stem from a propagation.
	propagated: i32,
	/// The solver status given by the `end proof` event.
	status: String,
}

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the requested proof format.
pub(crate) enum ProofLayer {
	/// Write the proof in the DRCP format.
	Drcp(DrcpWriterLayer),
	/// Write the proof in the VeriPB pseudo-Boolean format.
	Veripb(VeripbWriterLayer),
}

/// A [`tracing_subscriber::Layer`] that writes the events emitted on the
/// `"proof"` target as a proof in the VeriPB pseudo-Boolean format.
pub(crate) struct VeripbWriterLayer {
	/// The literals used in the proof, together with the reverse mappings
	/// needed to resolve their meanings for the companion literal map.
	defs: LitDefs,
	/// Whether the literals are named inline (after the FlatZinc decisions they
	/// represent) rather than mapped in a companion file.
	inline: bool,
	/// The path of the companion literal-map file (with a `.lits.json`
	/// extension; unused when `inline`).
	lits_path: PathBuf,
	/// The writer to which the proof is written.
	out: Mutex<BufWriter<File>>,
}

impl DrcpWriterLayer {
	/// Conclude the proof: write the atom definitions for all used literal
	/// codes to the companion literal-definition file, and the conclusion
	/// derived from the `end proof` event to the proof file.
	fn conclude(&self, event: &ProofEvent) -> io::Result<()> {
		// In companion mode, write the atom definitions for all used literal
		// codes to the companion file.
		let mut lits = (!self.inline)
			.then(|| -> io::Result<_> {
				let mut lits = File::create(&self.lits_path).map(BufWriter::new)?;
				for (code, name) in self.defs.resolved() {
					if let Some(name) = name {
						write!(lits, "a {code} ")?;
						Self::write_atom(&mut lits, &name)?;
						writeln!(lits)?;
					}
				}
				Ok(lits)
			})
			.transpose()?;

		// Write the conclusion of the proof to the proof file.
		let mut out = self.out.lock().unwrap();
		match event.status.as_str() {
			"Unsatisfiable" => writeln!(out, "c UNSAT")?,
			"Complete" => {
				// Conclude with the proven dual bound on the objective when the
				// problem is optimized and the objective decision is named.
				if let (Some(objective), Some(name)) = (event.objective, &event.obj_name) {
					let op = if event.minimize { ">=" } else { "<=" };
					// Synthesize a final atom code for the bound, defined alongside the
					// other atoms.
					match lits.as_mut() {
						Some(lits) => writeln!(lits, "a {} [{name} {op} {objective}]", i32::MAX)?,
						None => writeln!(out, "a {} [{name} {op} {objective}]", i32::MAX)?,
					}
					writeln!(out, "c {}", i32::MAX)?;
				}
			}
			_ => {}
		}
		if let Some(mut lits) = lits {
			lits.flush()?;
		}
		out.flush()
	}

	/// Create a new [`DrcpWriterLayer`] that produces a proof file at `path`.
	///
	/// When `inline` is set, the atom definitions are written into the proof
	/// file itself; otherwise they are written to a companion
	/// literal-definition file alongside the proof. The given reverse map
	/// resolves the meanings of literals.
	fn new(path: PathBuf, map: Arc<Mutex<ReverseMap>>, inline: bool) -> io::Result<Self> {
		let out = BufWriter::new(File::create(&path)?);
		Ok(Self {
			defs: LitDefs::new(map),
			inline,
			lits_path: path.with_extension("lits"),
			out: Mutex::new(out),
			skipped: Mutex::default(),
		})
	}

	/// Record the use of the codes appearing in a step and, in inline mode,
	/// write the atom definition of each newly-seen (named) code to the proof
	/// file before the step that uses it.
	fn prepare_atoms<W: Write>(
		&self,
		out: &mut W,
		codes: impl IntoIterator<Item = i32>,
	) -> io::Result<()> {
		let mut used = self.defs.used.lock().unwrap();
		// In inline mode, the first time a code is used is exactly when its atom
		// definition must be written, so the `used` insertion doubles as the
		// write trigger; the reverse map is only needed to resolve the name.
		let map = self.inline.then(|| self.defs.map.lock().unwrap());
		for code in codes {
			let code = code.abs();
			if used.insert(code)
				&& let Some(map) = map.as_deref()
				&& let Some(name) = map.solver_lit(NonZeroI32::new(code).unwrap())
			{
				write!(out, "a {code} ")?;
				Self::write_atom(out, name)?;
				writeln!(out)?;
			}
		}
		Ok(())
	}

	/// Process a proof event, writing the corresponding DRCP step.
	fn process(&self, event: &ProofEvent) -> io::Result<()> {
		match event.message.as_str() {
			"add original clause" => {
				// Ignore literal-definition clauses
				if event.hint == "lit_def" {
					let _ = self.skipped.lock().unwrap().insert(event.id);
					return Ok(());
				}
				// A clause `(l1 ∨ ... ∨ ln)` stemming from the solver is
				// represented as an inference step: the negations of the
				// non-propagated literals form the premises, and the propagated
				// literal (if any) forms the consequent.
				let premises: Vec<i32> = event
					.clause
					.iter()
					.filter(|&&l| l != event.propagated)
					.map(|&l| -l)
					.collect();
				let consequent = (event.propagated != 0).then_some(event.propagated);
				let mut out = self.out.lock().unwrap();
				self.prepare_atoms(&mut *out, premises.iter().copied().chain(consequent))?;
				write!(out, "i {}", event.id)?;
				for code in &premises {
					write!(out, " {code}")?;
				}
				write!(out, " 0")?;
				if let Some(consequent) = consequent {
					write!(out, " {consequent}")?;
				}
				if let Some(&con) = event.constraints.first() {
					// Note that the DRCP format uses non-zero constraint
					// identifiers, while the constraint indices are zero-based.
					write!(out, " c:{}", con + 1)?;
				}
				if !event.hint.is_empty() {
					write!(out, " l:{}", event.hint)?;
				}
				writeln!(out)
			}
			"add derived clause" | "add assumption clause" => {
				// A clause `(l1 ∨ ... ∨ ln)` derived by the SAT oracle is
				// represented as a nogood (deduction) step refuting the
				// conjunction of the negations of its literals.
				let premises: Vec<i32> = event.clause.iter().map(|&l| -l).collect();
				let skipped = self.skipped.lock().unwrap();
				let mut out = self.out.lock().unwrap();
				self.prepare_atoms(&mut *out, premises.iter().copied())?;
				write!(out, "n {}", event.id)?;
				for code in &premises {
					write!(out, " {code}")?;
				}
				write!(out, " 0")?;
				for ant in event
					.antecedents
					.iter()
					.filter(|ant| !skipped.contains(ant))
				{
					write!(out, " {ant}")?;
				}
				writeln!(out)
			}
			"end proof" => self.conclude(event),
			// The DRCP format does not represent clause deletions, assumption
			// tracking, or solver status reports.
			_ => Ok(()),
		}
	}

	/// Write the DRCP atomic constraint of the given [`LitName`].
	///
	/// Note that the DRCP format does not have a strict inequality, the
	/// [`IntLitMeaning::Less`] meaning is represented using `<=`.
	fn write_atom<W: Write>(out: &mut W, name: &LitName) -> io::Result<()> {
		match name {
			LitName::BoolVar(var, pos) => {
				write!(out, "[{} == {}]", var.name, if *pos { 1 } else { 0 })
			}
			LitName::IntLit(var, meaning) => match meaning {
				IntLitMeaning::Eq(val) => write!(out, "[{} == {val}]", var.name),
				IntLitMeaning::NotEq(val) => write!(out, "[{} != {val}]", var.name),
				IntLitMeaning::GreaterEq(val) => write!(out, "[{} >= {val}]", var.name),
				IntLitMeaning::Less(val) => write!(out, "[{} <= {}]", var.name, val - 1),
			},
		}
	}
}

impl LitDefs {
	/// Lock the set of used literals and return a closure that records the use
	/// of a literal (identified by its absolute code). The lock is held for as
	/// long as the returned closure is alive, so a batch of literals can be
	/// recorded under a single lock acquisition.
	fn lock_record(&self) -> impl FnMut(&i32) + '_ {
		let mut used = self.used.lock().unwrap();
		move |&lit| {
			let _ = used.insert(lit.abs());
		}
	}

	/// Create a new [`LitDefs`] using the given reverse map.
	fn new(map: Arc<Mutex<ReverseMap>>) -> Self {
		Self {
			map,
			used: Mutex::default(),
		}
	}

	/// An iterator over the used (positive) literal codes, yielded in ascending
	/// order, each paired with its resolved name (or [`None`] when the literal
	/// has no known meaning).
	///
	/// This iterator holds the lock on `self.map` while it is alive.
	fn resolved(&self) -> impl Iterator<Item = (i32, Option<LitName>)> {
		let mut codes: Vec<i32> = self.used.lock().unwrap().iter().copied().collect();
		codes.sort_unstable();
		let map = self.map.lock().unwrap();
		codes.into_iter().map(move |code| {
			let name = map.solver_lit(NonZeroI32::new(code).unwrap()).cloned();
			(code, name)
		})
	}
}

impl Visit for ProofEvent {
	fn record_bool(&mut self, field: &Field, value: bool) {
		if field.name() == "minimize" {
			self.minimize = value;
		}
	}

	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		match field.name() {
			"message" => self.message = format!("{value:?}"),
			"clause" => self.clause = parse_int_list(value).unwrap_or_default(),
			"antecedents" => self.antecedents = parse_int_list(value).unwrap_or_default(),
			"constraints" => self.constraints = parse_int_list(value).unwrap_or_default(),
			"status" => self.status = format!("{value:?}"),
			_ => {}
		}
	}

	fn record_i64(&mut self, field: &Field, value: i64) {
		match field.name() {
			"id" => self.id = value,
			"propagated" => self.propagated = value as i32,
			"objective" => self.objective = Some(value),
			_ => {}
		}
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		match field.name() {
			"hint" => self.hint = value.to_owned(),
			"status" => self.status = value.to_owned(),
			"obj_name" => self.obj_name = Some(value.to_owned()),
			_ => {}
		}
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		self.record_i64(field, value as i64);
	}
}

impl ProofLayer {
	/// Create a new [`ProofLayer`] according to the given [`ProofConfig`],
	/// using the given reverse map to resolve the meanings of literals.
	pub(crate) fn new(config: &ProofConfig, map: Arc<Mutex<ReverseMap>>) -> io::Result<Self> {
		let inline = matches!(config.literal_names, CliProofLiteralNames::Inline);
		Ok(match config.format {
			CliProofFormat::Drcp => {
				ProofLayer::Drcp(DrcpWriterLayer::new(config.path.clone(), map, inline)?)
			}
			CliProofFormat::Veripb => {
				ProofLayer::Veripb(VeripbWriterLayer::new(config.path.clone(), map, inline)?)
			}
		})
	}
}

impl<S: Subscriber> Layer<S> for ProofLayer {
	fn on_event(&self, event: &Event<'_>, _: Context<'_, S>) {
		let mut fields = ProofEvent::default();
		event.record(&mut fields);
		let res = match self {
			ProofLayer::Drcp(layer) => layer.process(&fields),
			ProofLayer::Veripb(layer) => layer.process(&fields),
		};
		if let Err(err) = res {
			// Note that panicking within the tracing subscriber would poison
			// the solving process; the proof is invalid regardless.
			eprintln!("ERROR: unable to write proof file: {err}");
		}
	}
}

impl VeripbWriterLayer {
	/// Create a new [`VeripbWriterLayer`] that produces a proof file at `path`
	/// and a companion literal-map file alongside it, writing the header of the
	/// proof file.
	fn new(path: PathBuf, map: Arc<Mutex<ReverseMap>>, inline: bool) -> io::Result<Self> {
		let layer = Self {
			defs: LitDefs::new(map),
			inline,
			lits_path: path.with_extension("lits.json"),
			out: Mutex::new(BufWriter::new(File::create(&path)?)),
		};
		{
			let mut out = layer.out.lock().unwrap();
			writeln!(out, "pseudo-Boolean proof version 3.0")?;
			writeln!(out, "f 0 ;")?;
		}
		Ok(layer)
	}

	/// Process a proof event, writing the corresponding VeriPB proof line.
	fn process(&self, event: &ProofEvent) -> io::Result<()> {
		let mut out = self.out.lock().unwrap();
		match event.message.as_str() {
			"add assumption clause" => {
				// An assumption clause is a negated conjunction of
				// assumptions, so we need to assert the negation in the proof.
				write!(out, "@c{} a ", event.id)?;
				if self.inline {
					let map = self.defs.map.lock().unwrap();
					for &l in &event.clause {
						Self::write_clause_literal(&mut *out, &map, -l)?;
					}
				} else {
					let mut record = self.defs.lock_record();
					for &l in &event.clause {
						record(&l);
						if l >= 0 {
							write!(out, "1 ~x{l} ")?;
						} else {
							write!(out, "1 x{} ", -l)?;
						}
					}
				}
				write!(out, ">= {}", event.clause.len())?;
				// Assumptions should be annotated with the corresponding
				// huub_assumption in the input.
				if !event.hint.is_empty() {
					write!(out, " :: {}", event.hint)?;
					if !event.constraints.is_empty() {
						write!(out, "{:?}", event.constraints)?;
					}
				}
				writeln!(out, ";")
			}
			"add original clause" => {
				write!(out, "@c{} a ", event.id)?;
				if self.inline {
					let map = self.defs.map.lock().unwrap();
					for &l in &event.clause {
						Self::write_clause_literal(&mut *out, &map, l)?;
					}
				} else {
					let mut record = self.defs.lock_record();
					for &l in &event.clause {
						record(&l);
						if l >= 0 {
							write!(out, "1 x{l} ")?;
						} else {
							write!(out, "1 ~x{} ", -l)?;
						}
					}
				}
				write!(out, ">= 1")?;
				// Annotate the clause with its solver rule or constraint when
				// known.
				if !event.hint.is_empty() {
					write!(out, " :: {}", event.hint)?;
					if !event.constraints.is_empty() {
						write!(out, "{:?}", event.constraints)?;
					}
				}
				writeln!(out, ";")
			}
			"add derived clause" => {
				// Derived clauses are justified by a reverse unit propagation
				// resolution chain over their antecedents.
				write!(out, "@c{} pol ", event.id)?;
				for (i, ant) in event.antecedents.iter().rev().enumerate() {
					if i == 0 {
						write!(out, "@c{ant} ")?;
					} else {
						write!(out, "@c{ant} + s ")?;
					}
				}
				writeln!(out, ";")
			}
			"delete clause" => {
				writeln!(out, "del id @c{} ;", event.id)
			}
			"solve query" | "add assumption" | "reset assumptions" | "conclude sat"
			| "conclude unknown" | "conclude unsat" | "begin proof" => {
				// Events related to incremental solving have no VeriPB
				// representation; they are included as comments.
				writeln!(out, "% {}", event.message)
			}
			"end proof" => {
				writeln!(out, "output NONE ;")?;
				if event.status == "Unsatisfiable" {
					writeln!(out, "conclusion UNSAT ;")?;
				} else {
					writeln!(out, "conclusion NONE ;")?;
				}
				writeln!(out, "end pseudo-Boolean proof ;")?;
				out.flush()?;
				drop(out);

				if !self.inline {
					self.write_lit_map()?
				}
				Ok(())
			}
			_ => Ok(()),
		}
	}

	/// Write a single (unit-weight) VeriPB clause literal for the code `code`,
	/// which should appear with positive polarity in the clause.
	///
	/// The named pseudo-Boolean literal is used when the code has a known
	/// meaning; otherwise the raw `x<code>` variable is used (auxiliary
	/// literals introduced by an encoding have no FlatZinc meaning).
	fn write_clause_literal<W: Write>(out: &mut W, map: &ReverseMap, code: i32) -> io::Result<()> {
		write!(out, "1 ")?;
		match map.solver_lit(NonZeroI32::new(code).unwrap()) {
			Some(name) => Self::write_pb_name(out, name)?,
			None if code >= 0 => write!(out, "x{code}")?,
			None => write!(out, "~x{}", -code)?,
		}
		write!(out, " ")
	}

	/// Write the companion literal map, mapping each used `x<code>` variable to
	/// its FlatZinc meaning. Literals without a known meaning are omitted.
	fn write_lit_map(&self) -> io::Result<()> {
		let mut file = BufWriter::new(File::create(&self.lits_path)?);
		write!(file, "{{")?;
		let mut first = true;
		for (name, def) in self.defs.resolved() {
			if let Some(def) = def {
				if !first {
					write!(file, ",")?;
				}
				first = false;
				write!(file, "\n  \"x{name}\": ")?;
				match def {
					LitName::BoolVar(variable, _) => {
						write!(file, "{{ \"name\": \"{}\" }}", variable.name)?;
					}
					LitName::IntLit(variable, meaning) => {
						let (cmp, val) = match meaning {
							IntLitMeaning::Eq(val) => ("==", val),
							IntLitMeaning::NotEq(val) => ("!=", val),
							IntLitMeaning::GreaterEq(val) => (">=", val),
							IntLitMeaning::Less(val) => ("<", val),
						};
						write!(
							file,
							"{{ \"name\": \"{}\", \"cmp\": \"{cmp}\", \"val\": {val} }}",
							variable.name,
						)?;
					}
				}
			}
		}
		writeln!(file, "\n}}")
	}

	/// Write the given [`LitName`] as a VeriPB pseudo-Boolean literal, encoding
	/// the meaning in the variable name.
	///
	/// Order literals of `x` are named `i[x][geq<v>]` (with `~` for the
	/// negation `x < v`), equality literals `i[x][eq<v>]` (with `~` for `x !=
	/// v`), and a Boolean decision uses its name verbatim (with `~` when the
	/// literal represents the decision being false).
	fn write_pb_name<W: Write>(out: &mut W, name: &LitName) -> io::Result<()> {
		match name {
			LitName::BoolVar(var, pos) => {
				if *pos {
					write!(out, "{}", var.name)
				} else {
					write!(out, "~{}", var.name)
				}
			}
			LitName::IntLit(var, meaning) => match meaning {
				IntLitMeaning::GreaterEq(val) => write!(out, "i[{}][geq{val}]", var.name),
				IntLitMeaning::Less(val) => write!(out, "~i[{}][geq{val}]", var.name),
				IntLitMeaning::Eq(val) => write!(out, "i[{}][eq{val}]", var.name),
				IntLitMeaning::NotEq(val) => write!(out, "~i[{}][eq{val}]", var.name),
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{
		fs,
		num::NonZeroI32,
		sync::{
			Arc,
			atomic::{AtomicU32, Ordering},
		},
	};

	use drcp_format::{Conclusion, IntComparison, Step, reader::ProofReader};
	use expect_test::expect;
	use flatzinc_serde::{Type, Variable};
	use huub::solver::IntLitMeaning;
	use rustc_hash::FxHashMap;
	use tracing::subscriber::with_default;
	use tracing_subscriber::layer::SubscriberExt;

	use crate::{
		cli::{CliProofFormat, CliProofLiteralNames, ProofConfig},
		proof::ProofLayer,
		trace::{LitName, ReverseMap, VarRef},
	};

	/// Create the literal reverse mapping used by the formatter tests.
	///
	/// The mapping describes the following literals:
	/// - `1`: `x == 2` (and `-1`: `x != 2`)
	/// - `2`: `y >= 3` (and `-2`: `y < 3`)
	fn lit_reverse_map() -> FxHashMap<NonZeroI32, LitName> {
		let x = var("x");
		let y = var("y");
		let mut map = FxHashMap::default();
		let _ = map.insert(
			NonZeroI32::new(1).unwrap(),
			LitName::IntLit(Arc::clone(&x), IntLitMeaning::Eq(2)),
		);
		let _ = map.insert(
			NonZeroI32::new(-1).unwrap(),
			LitName::IntLit(x, IntLitMeaning::NotEq(2)),
		);
		let _ = map.insert(
			NonZeroI32::new(2).unwrap(),
			LitName::IntLit(Arc::clone(&y), IntLitMeaning::GreaterEq(3)),
		);
		let _ = map.insert(
			NonZeroI32::new(-2).unwrap(),
			LitName::IntLit(y, IntLitMeaning::Less(3)),
		);
		map
	}

	/// Emit a synthetic proof for the given format and return the produced
	/// proof file together with the companion literal-definition file (empty
	/// for formats that do not produce one).
	fn run_events(format: CliProofFormat, literal_names: CliProofLiteralNames) -> (String, String) {
		// Use a unique directory per invocation so that concurrently running
		// tests do not clobber each other's proof files.
		static COUNTER: AtomicU32 = AtomicU32::new(0);
		let id = COUNTER.fetch_add(1, Ordering::Relaxed);
		let dir = std::env::temp_dir().join(format!(
			"huub-proof-test-{}-{:?}-{id}",
			std::process::id(),
			format
		));
		let _ = fs::create_dir_all(&dir);
		let path = dir.join(match format {
			CliProofFormat::Drcp => "test.drcp",
			CliProofFormat::Veripb => "test.pbp",
		});
		let config = ProofConfig {
			format,
			literal_names,
			path: path.clone(),
		};
		let map = ReverseMap::from_solver_maps(lit_reverse_map(), Vec::new());
		let layer = ProofLayer::new(&config, map).unwrap();
		let subscriber = tracing_subscriber::registry().with(layer);
		with_default(subscriber, || {
			// An original clause from a constraint that propagates `x = 2`.
			tracing::trace!(
				target: "proof",
				id = 1_i64,
				redundant = false,
				restored = false,
				clause = ?vec![1_i32, -2_i32],
				propagated = 1_i32,
				hint = "int_lin_eq",
				constraints = ?vec![3_u32],
				"add original clause"
			);
			// A literal definition clause without a propagation or constraint.
			tracing::trace!(
				target: "proof",
				id = 2_i64,
				redundant = false,
				restored = false,
				clause = ?vec![-1_i32, 2_i32],
				propagated = 0_i32,
				hint = "lit_def",
				constraints = ?Vec::<u32>::new(),
				"add original clause"
			);
			// A derived (learned) clause.
			tracing::trace!(
				target: "proof",
				id = 3_i64,
				redundant = true,
				clause = ?vec![-1_i32],
				antecedents = ?vec![1_i64, 2_i64],
				"add derived clause"
			);
			tracing::trace!(
				target: "proof",
				status = "Unsatisfiable",
				"end proof"
			);
		});
		let proof = fs::read_to_string(&path).unwrap();
		// The companion file is only produced when the literal names are not
		// written inline.
		let lits = match (literal_names, format) {
			(CliProofLiteralNames::Inline, _) => String::new(),
			(CliProofLiteralNames::Companion, CliProofFormat::Drcp) => {
				fs::read_to_string(path.with_extension("lits")).unwrap()
			}
			(CliProofLiteralNames::Companion, CliProofFormat::Veripb) => {
				fs::read_to_string(path.with_extension("lits.json")).unwrap()
			}
		};
		(proof, lits)
	}

	#[test]
	fn test_drcp_formatter() {
		let (proof, lits) = run_events(CliProofFormat::Drcp, CliProofLiteralNames::Companion);
		// The proof file contains only the steps and the conclusion.
		expect![[r#"
    i 1 2 0 1 c:4 l:int_lin_eq
    n 3 1 0 1
    c UNSAT
"#]]
		.assert_eq(&proof);
		// The companion file defines the atoms used in the proof.
		expect![[r#"
    a 1 [x == 2]
    a 2 [y >= 3]
"#]]
		.assert_eq(&lits);

		// The companion definitions followed by the proof should be parseable by
		// the `drcp-format` reader, which reads atom definitions before steps.
		let proof = format!("{lits}{proof}");
		let mut reader = ProofReader::<_, i32>::new(proof.as_bytes());
		let mut steps = Vec::new();
		while let Some(step) = reader.next_step().expect("valid DRCP proof") {
			steps.push(step);
		}
		// One inference, one nogood, and one conclusion.
		assert_eq!(steps.len(), 3);
		assert!(matches!(steps[0], Step::Inference(_)));
		assert!(matches!(steps[1], Step::Deduction(_)));
		assert_eq!(steps[2], Step::Conclusion(Conclusion::Unsat));

		// The first inference propagates `[x == 2]` from `[y >= 3]`.
		let Step::Inference(inf) = &steps[0] else {
			unreachable!()
		};
		assert_eq!(inf.premises.len(), 1);
		assert_eq!(inf.premises[0].comparison, IntComparison::GreaterEqual);
		let consequent = inf.consequent.as_ref().unwrap();
		assert_eq!(consequent.comparison, IntComparison::Equal);
		assert_eq!(inf.generated_by, std::num::NonZero::new(4_u32));
		assert_eq!(inf.label.as_deref(), Some("int_lin_eq"));
	}

	#[test]
	fn test_drcp_inline() {
		// With inline literal names, each atom is defined in the proof file
		// itself before the first step that uses it, and no companion file is
		// written.
		let (proof, lits) = run_events(CliProofFormat::Drcp, CliProofLiteralNames::Inline);
		expect![[r#"
    a 2 [y >= 3]
    a 1 [x == 2]
    i 1 2 0 1 c:4 l:int_lin_eq
    n 3 1 0 1
    c UNSAT
"#]]
		.assert_eq(&proof);
		assert_eq!(lits, "", "inline mode writes no companion file");

		// The single file (definitions interleaved before their first use) is
		// parseable by the `drcp-format` reader.
		let mut reader = ProofReader::<_, i32>::new(proof.as_bytes());
		let mut steps = Vec::new();
		while let Some(step) = reader.next_step().expect("valid DRCP proof") {
			steps.push(step);
		}
		assert_eq!(steps.len(), 3);
		assert!(matches!(steps[0], Step::Inference(_)));
		assert!(matches!(steps[1], Step::Deduction(_)));
		assert_eq!(steps[2], Step::Conclusion(Conclusion::Unsat));
	}

	#[test]
	fn test_drcp_objective_bound() {
		// A completed optimization proof concludes with the proven dual bound on
		// the objective, naming the decision it is optimized over.
		let dir = std::env::temp_dir().join("huub-proof-test-obj-bound");
		let _ = fs::create_dir_all(&dir);
		let path = dir.join("test.drcp");
		let config = ProofConfig {
			format: CliProofFormat::Drcp,
			literal_names: CliProofLiteralNames::Companion,
			path: path.clone(),
		};
		let map = ReverseMap::from_solver_maps(lit_reverse_map(), Vec::new());
		let layer = ProofLayer::new(&config, map).unwrap();
		let subscriber = tracing_subscriber::registry().with(layer);
		with_default(subscriber, || {
			tracing::trace!(
				target: "proof",
				id = 1_i64,
				redundant = false,
				restored = false,
				clause = ?vec![1_i32],
				propagated = 0_i32,
				hint = "int_lin_le",
				constraints = ?Vec::<u32>::new(),
				"add original clause"
			);
			// A minimization that is proven complete with objective value `7`.
			tracing::trace!(
				target: "proof",
				status = "Complete",
				objective = 7_i64,
				obj_name = "obj",
				minimize = true,
				"end proof"
			);
		});
		let proof = fs::read_to_string(&path).unwrap();
		// The dual bound is concluded in the proof file, and its atom (like the
		// others) is defined in the companion file.
		expect![[r#"
    i 1 -1 0 l:int_lin_le
    c 2147483647
"#]]
		.assert_eq(&proof);
		let lits = fs::read_to_string(path.with_extension("lits")).unwrap();
		expect![[r#"
    a 1 [x == 2]
    a 2147483647 [obj >= 7]
"#]]
		.assert_eq(&lits);
	}

	#[test]
	fn test_pbp_formatter() {
		let (proof, _lits) = run_events(CliProofFormat::Veripb, CliProofLiteralNames::Companion);
		expect![[r#"
    pseudo-Boolean proof version 3.0
    f 0 ;
    @c1 a 1 x1 1 ~x2 >= 1 :: int_lin_eq[3];
    @c2 a 1 ~x1 1 x2 >= 1 :: lit_def;
    @c3 pol @c2 @c1 + s ;
    output NONE ;
    conclusion UNSAT ;
    end pseudo-Boolean proof ;
"#]]
		.assert_eq(&proof);
	}

	#[test]
	fn test_pbp_inline() {
		// With inline literal names, each literal is named after the FlatZinc
		// decision it represents, and no companion file is written. Note the
		// signed code is resolved directly, so the `~` follows the meaning
		// rather than the raw sign (e.g. `~i[y][geq3]` is `y < 3`).
		let (proof, lits) = run_events(CliProofFormat::Veripb, CliProofLiteralNames::Inline);
		expect![[r#"
    pseudo-Boolean proof version 3.0
    f 0 ;
    @c1 a 1 i[x][eq2] 1 ~i[y][geq3] >= 1 :: int_lin_eq[3];
    @c2 a 1 ~i[x][eq2] 1 i[y][geq3] >= 1 :: lit_def;
    @c3 pol @c2 @c1 + s ;
    output NONE ;
    conclusion UNSAT ;
    end pseudo-Boolean proof ;
"#]]
		.assert_eq(&proof);
		assert_eq!(lits, "", "inline mode writes no companion file");
	}

	#[test]
	fn test_pbp_lit_map() {
		let (_proof, lits) = run_events(CliProofFormat::Veripb, CliProofLiteralNames::Companion);
		// The companion literal map resolves each used Boolean code to its
		// FlatZinc meaning. Auxiliary literals without a known meaning are
		// omitted.
		expect![[r#"
    {
      "x1": { "name": "x", "cmp": "==", "val": 2 },
      "x2": { "name": "y", "cmp": ">=", "val": 3 }
    }
"#]]
		.assert_eq(&lits);
	}

	/// Create a [`VarRef`] for a variable with the given name.
	fn var(name: &str) -> VarRef {
		Arc::new(Variable {
			name: name.to_owned(),
			ty: Type::Bool,
			ann: Vec::new(),
			defined: false,
			introduced: false,
		})
	}
}
