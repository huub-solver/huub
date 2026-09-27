//! Output of the preprocessing trace and of the model at the start of search.
//!
//! When a preprocessing trace is requested, the library emits every step on
//! the `preprocess` tracing target and the model at the start of search on the
//! `start_model` target (see [`huub::model::preprocess`]). The layers in this
//! module write them to the requested files. Since the trace is data for a
//! checker rather than diagnostics, the layers check that no event is lost: the
//! steps must be numbered consecutively, and both outputs must be closed by an
//! event that states their length.

use std::{
	error::Error,
	fmt::{self, Display},
	fs::{self, File},
	io::{self, BufWriter, Read, Write},
	mem,
	path::{Path, PathBuf},
	sync::{Arc, Mutex},
};

use tracing::{
	Event, Subscriber,
	field::{Field, Visit},
};
use tracing_subscriber::{Layer, layer::Context};

/// The version of the trace format that is written.
const TRACE_FORMAT_VERSION: &str = "0.1";

/// A [`Layer`] that writes the `start_model` events to the start model file.
pub(crate) struct ModelLayer(Arc<Mutex<PreprocessOutput>>);

/// One of the two outputs of a preprocessing trace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Output {
	/// The model at the start of search, from the `start_model` target.
	StartModel,
	/// The steps of the trace, from the `preprocess` target.
	Trace,
}

/// The fields of an event on the `preprocess` or `start_model` target.
#[derive(Debug, Default)]
struct OutputEvent {
	/// The number of the step.
	seq: Option<u64>,
	/// The text of the step or item.
	text: Option<String>,
	/// The number of steps or items, closing the output.
	end: Option<u64>,
}

/// The state of the outputs of a preprocessing trace.
#[derive(Debug)]
enum OutputState {
	/// An event could not be handled, so the outputs are incomplete.
	///
	/// The layers cannot return the error to the code that emitted the
	/// event, so the error is kept until the outputs are completed, and later
	/// events are ignored.
	Failed(PreprocessOutputError),
	/// The outputs have been completed.
	Finished,
	/// The outputs are being written.
	Writing(Writing),
}

/// The outputs of a preprocessing trace, shared between the layers that write
/// them and the CLI that completes them.
#[derive(Debug)]
pub(crate) struct PreprocessOutput(OutputState);

/// Error that prevents the preprocessing trace or the start model from being
/// written completely.
#[derive(Debug)]
pub(crate) enum PreprocessOutputError {
	/// An output file could not be created.
	Create {
		/// The file that could not be created.
		path: PathBuf,
		/// The underlying error.
		source: io::Error,
	},
	/// An output did not receive the event that states its length, so events
	/// may have been lost.
	Incomplete {
		/// The output that is incomplete.
		output: Output,
	},
	/// The event that ends an output states a different length than the
	/// number of steps or items that were received.
	LengthMismatch {
		/// The output whose length differs.
		output: Output,
		/// The number of steps or items that were received.
		received: u64,
		/// The number of steps or items that the end of the output states.
		stated: u64,
	},
	/// An event lacked the fields that its output needs.
	MalformedEvent {
		/// The output that the event belongs to.
		output: Output,
	},
	/// A step of the trace was not received, since the next step has a later
	/// number.
	MissingStep {
		/// The number of the missing step.
		step: u64,
	},
	/// An event was received after the end of its output.
	OutputAfterEnd {
		/// The output that had already ended.
		output: Output,
	},
	/// A file could not be read to compute its digest.
	Read {
		/// The file that could not be read.
		path: PathBuf,
		/// The underlying error.
		source: io::Error,
	},
	/// An output file could not be written.
	Write {
		/// The file that could not be written.
		path: PathBuf,
		/// The underlying error.
		source: io::Error,
	},
}

/// A [`Layer`] that writes the `preprocess` events to the trace.
pub(crate) struct TraceLayer(Arc<Mutex<PreprocessOutput>>);

/// The outputs of a preprocessing trace while they are being written.
#[derive(Debug)]
struct Writing {
	/// The path of the trace file.
	trace_path: PathBuf,
	/// The path of the temporary file that holds the steps until the trace is
	/// completed.
	body_path: PathBuf,
	/// The writer of the steps.
	body: BufWriter<File>,
	/// The number of steps that have been written.
	steps: u64,
	/// Whether the last step that was written concludes that the model has no
	/// solutions, in which case there is no start model.
	concluded_unsat: bool,
	/// Whether the end of the trace has been received.
	trace_ended: bool,
	/// The path of the start model file.
	model_path: PathBuf,
	/// The writer of the start model.
	model: BufWriter<File>,
	/// The number of start model items that have been written.
	items: u64,
	/// Whether the end of the start model has been received.
	model_ended: bool,
}

/// Compute the SHA-256 digest of `data` as a lowercase hexadecimal string.
fn sha256(data: &[u8]) -> String {
	const K: [u32; 64] = [
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
		0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
		0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
		0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
		0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
		0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
		0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
		0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
		0xc67178f2,
	];
	let mut h: [u32; 8] = [
		0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
		0x5be0cd19,
	];
	// Pad the message with a single 1 bit, zeros, and its length in bits, to
	// a multiple of 512 bits.
	let mut msg = data.to_vec();
	msg.push(0x80);
	while msg.len() % 64 != 56 {
		msg.push(0);
	}
	msg.extend_from_slice(&((data.len() as u64) * 8).to_be_bytes());

	for block in msg.chunks_exact(64) {
		let mut w = [0_u32; 64];
		for (i, word) in block.chunks_exact(4).enumerate() {
			w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
		}
		for i in 16..64 {
			let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
			let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
			w[i] = w[i - 16]
				.wrapping_add(s0)
				.wrapping_add(w[i - 7])
				.wrapping_add(s1);
		}
		let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
		for i in 0..64 {
			let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
			let ch = (e & f) ^ (!e & g);
			let t1 = hh
				.wrapping_add(s1)
				.wrapping_add(ch)
				.wrapping_add(K[i])
				.wrapping_add(w[i]);
			let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
			let maj = (a & b) ^ (a & c) ^ (b & c);
			let t2 = s0.wrapping_add(maj);
			hh = g;
			g = f;
			f = e;
			e = d.wrapping_add(t1);
			d = c;
			c = b;
			b = a;
			a = t1.wrapping_add(t2);
		}
		for (x, y) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
			*x = x.wrapping_add(y);
		}
	}
	h.iter().map(|x| format!("{x:08x}")).collect()
}

/// Compute the SHA-256 digest of the file at `path`.
fn sha256_file(path: &Path) -> io::Result<String> {
	let mut data = Vec::new();
	File::open(path)?.read_to_end(&mut data)?;
	Ok(sha256(&data))
}

impl ModelLayer {
	/// Create a layer that writes the start model to `output`.
	pub(crate) fn new(output: Arc<Mutex<PreprocessOutput>>) -> Self {
		Self(output)
	}
}

impl<S: Subscriber> Layer<S> for ModelLayer {
	fn on_event(&self, event: &Event<'_>, _: Context<'_, S>) {
		let mut rec = OutputEvent::default();
		event.record(&mut rec);
		self.0.lock().unwrap().handle(Output::StartModel, rec);
	}
}

impl Display for Output {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(match self {
			Output::StartModel => "the start model",
			Output::Trace => "the preprocessing trace",
		})
	}
}

impl Visit for OutputEvent {
	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		if matches!(field.name(), "step" | "item") {
			self.text = Some(format!("{value:?}"));
		}
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		if matches!(field.name(), "step" | "item") {
			self.text = Some(value.to_owned());
		}
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		match field.name() {
			"seq" => self.seq = Some(value),
			"end" => self.end = Some(value),
			_ => {}
		}
	}
}

impl PreprocessOutput {
	/// Complete the outputs once the model has been lowered, writing the trace
	/// file with its header.
	///
	/// `received` is the FlatZinc file that the model was read from. The
	/// outputs can only be completed once.
	pub(crate) fn finish(&mut self, received: &Path) -> Result<(), PreprocessOutputError> {
		match mem::replace(&mut self.0, OutputState::Finished) {
			OutputState::Writing(w) => w.finish(received),
			OutputState::Failed(err) => Err(err),
			OutputState::Finished => unreachable!("the preprocessing outputs were completed twice"),
		}
	}

	/// Handle an event for `output`.
	///
	/// This is where the events of the layers arrive, which cannot return an
	/// error: the first error turns the outputs into the failed state, whose
	/// error [`Self::finish`] returns. Events after an error or after the
	/// outputs were completed are ignored.
	fn handle(&mut self, output: Output, event: OutputEvent) {
		let OutputState::Writing(w) = &mut self.0 else {
			return;
		};
		let res = match output {
			Output::StartModel => w.model_event(event),
			Output::Trace => w.trace_event(event),
		};
		if let Err(err) = res {
			self.0 = OutputState::Failed(err);
		}
	}

	/// Create the outputs of a preprocessing trace written to `trace_path`,
	/// with the start model written to `model_path`.
	pub(crate) fn new(
		trace_path: PathBuf,
		model_path: PathBuf,
	) -> Result<Self, PreprocessOutputError> {
		let mut body_path = trace_path.clone().into_os_string();
		body_path.push(".partial");
		let body_path = PathBuf::from(body_path);
		let create = |path: &Path| {
			File::create(path)
				.map(BufWriter::new)
				.map_err(|source| PreprocessOutputError::Create {
					path: path.to_owned(),
					source,
				})
		};
		Ok(Self(OutputState::Writing(Writing {
			body: create(&body_path)?,
			model: create(&model_path)?,
			trace_path,
			body_path,
			steps: 0,
			concluded_unsat: false,
			trace_ended: false,
			model_path,
			items: 0,
			model_ended: false,
		})))
	}
}

impl Display for PreprocessOutputError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Create { path, source } => {
				write!(f, "unable to create file “{}”: {source}", path.display())
			}
			Self::Incomplete { output } => write!(f, "{output} was not completed"),
			Self::LengthMismatch {
				output,
				received,
				stated,
			} => write!(
				f,
				"{output} states a length of {stated}, but {received} were received"
			),
			Self::MalformedEvent { output } => write!(f, "malformed event for {output}"),
			Self::MissingStep { step } => {
				write!(f, "preprocessing step {step} is missing from the trace")
			}
			Self::OutputAfterEnd { output } => {
				write!(f, "an event was received after the end of {output}")
			}
			Self::Read { path, source } => {
				write!(f, "unable to read “{}”: {source}", path.display())
			}
			Self::Write { path, source } => {
				write!(f, "unable to write “{}”: {source}", path.display())
			}
		}
	}
}

impl Error for PreprocessOutputError {
	fn source(&self) -> Option<&(dyn Error + 'static)> {
		match self {
			Self::Create { source, .. }
			| Self::Read { source, .. }
			| Self::Write { source, .. } => Some(source),
			Self::Incomplete { .. }
			| Self::LengthMismatch { .. }
			| Self::MalformedEvent { .. }
			| Self::MissingStep { .. }
			| Self::OutputAfterEnd { .. } => None,
		}
	}
}

impl TraceLayer {
	/// Create a layer that writes the preprocessing steps to `output`.
	pub(crate) fn new(output: Arc<Mutex<PreprocessOutput>>) -> Self {
		Self(output)
	}
}

impl<S: Subscriber> Layer<S> for TraceLayer {
	fn on_event(&self, event: &Event<'_>, _: Context<'_, S>) {
		let mut rec = OutputEvent::default();
		event.record(&mut rec);
		self.0.lock().unwrap().handle(Output::Trace, rec);
	}
}

impl Writing {
	/// Complete the outputs, writing the trace file with its header.
	fn finish(self, received: &Path) -> Result<(), PreprocessOutputError> {
		let Writing {
			trace_path,
			body_path,
			body,
			steps,
			concluded_unsat,
			trace_ended,
			model_path,
			model,
			items: _,
			model_ended,
		} = self;
		let flush = |w: BufWriter<File>, path: &Path| {
			w.into_inner()
				.map(drop)
				.map_err(|err| PreprocessOutputError::Write {
					path: path.to_owned(),
					source: err.into_error(),
				})
		};
		flush(body, &body_path)?;
		flush(model, &model_path)?;
		if !trace_ended {
			return Err(PreprocessOutputError::Incomplete {
				output: Output::Trace,
			});
		}
		// A trace that concludes that the model has no solutions has no start
		// model, and refers to the empty start model file.
		if !model_ended && !concluded_unsat {
			return Err(PreprocessOutputError::Incomplete {
				output: Output::StartModel,
			});
		}

		let digest = |path: &Path| {
			sha256_file(path).map_err(|source| PreprocessOutputError::Read {
				path: path.to_owned(),
				source,
			})
		};
		let header = format!(
			"trace {TRACE_FORMAT_VERSION}\nproducer huub {}\nmodel in {} sha256:{}\nmodel out {} \
			 sha256:{}\n",
			env!("CARGO_PKG_VERSION"),
			received.display(),
			digest(received)?,
			model_path.display(),
			digest(&model_path)?
		);
		let write = || -> io::Result<()> {
			let mut out = BufWriter::new(File::create(&trace_path)?);
			out.write_all(header.as_bytes())?;
			io::copy(&mut File::open(&body_path)?, &mut out)?;
			writeln!(out, "end {steps}")?;
			out.flush()
		};
		write().map_err(|source| PreprocessOutputError::Write {
			path: trace_path.clone(),
			source,
		})?;
		// A temporary file that is left behind does not affect the outputs.
		let _ = fs::remove_file(&body_path);
		Ok(())
	}

	/// Handle an event on the `start_model` target.
	fn model_event(&mut self, event: OutputEvent) -> Result<(), PreprocessOutputError> {
		if self.model_ended {
			return Err(PreprocessOutputError::OutputAfterEnd {
				output: Output::StartModel,
			});
		}
		match event {
			OutputEvent { end: Some(n), .. } => {
				if n != self.items {
					return Err(PreprocessOutputError::LengthMismatch {
						output: Output::StartModel,
						received: self.items,
						stated: n,
					});
				}
				self.model_ended = true;
			}
			OutputEvent {
				text: Some(item), ..
			} => {
				self.items += 1;
				writeln!(self.model, "{item}").map_err(|source| PreprocessOutputError::Write {
					path: self.model_path.clone(),
					source,
				})?;
			}
			_ => {
				return Err(PreprocessOutputError::MalformedEvent {
					output: Output::StartModel,
				});
			}
		}
		Ok(())
	}

	/// Handle an event on the `preprocess` target.
	fn trace_event(&mut self, event: OutputEvent) -> Result<(), PreprocessOutputError> {
		if self.trace_ended {
			return Err(PreprocessOutputError::OutputAfterEnd {
				output: Output::Trace,
			});
		}
		match event {
			OutputEvent { end: Some(n), .. } => {
				if n != self.steps {
					return Err(PreprocessOutputError::LengthMismatch {
						output: Output::Trace,
						received: self.steps,
						stated: n,
					});
				}
				self.trace_ended = true;
			}
			OutputEvent {
				seq: Some(seq),
				text: Some(step),
				..
			} => {
				if seq != self.steps + 1 {
					return Err(PreprocessOutputError::MissingStep {
						step: self.steps + 1,
					});
				}
				self.steps = seq;
				self.concluded_unsat = step.starts_with("unsat ");
				writeln!(self.body, "{step}").map_err(|source| PreprocessOutputError::Write {
					path: self.body_path.clone(),
					source,
				})?;
			}
			_ => {
				return Err(PreprocessOutputError::MalformedEvent {
					output: Output::Trace,
				});
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use std::{env, fs, process};

	use crate::preprocess::{Output, OutputEvent, PreprocessOutput, PreprocessOutputError, sha256};

	#[test]
	fn complete_trace_has_header_and_end() {
		let (dir, mut out) = output("complete");
		let received = dir.join("received.fzn.json");
		fs::write(&received, "{}").unwrap();
		out.handle(Output::Trace, step(1, "del #1 by lin-valid"));
		out.handle(Output::Trace, end(1));
		out.handle(
			Output::StartModel,
			OutputEvent {
				seq: None,
				text: Some("solve satisfy;".to_owned()),
				end: None,
			},
		);
		out.handle(Output::StartModel, end(1));
		out.finish(&received).unwrap();
		let trace = fs::read_to_string(dir.join("run.trace")).unwrap();
		let lines: Vec<_> = trace.lines().collect();
		assert_eq!(lines[0], "trace 0.1");
		assert!(lines[2].starts_with("model in ") && lines[2].ends_with(&sha256(b"{}")));
		assert!(lines[3].ends_with(&sha256(b"solve satisfy;\n")));
		assert_eq!(&lines[4..], ["del #1 by lin-valid", "end 1"]);
		fs::remove_dir_all(&dir).unwrap();
	}

	/// An event that closes an output of `n` steps or items.
	fn end(n: u64) -> OutputEvent {
		OutputEvent {
			seq: None,
			text: None,
			end: Some(n),
		}
	}

	#[test]
	fn missing_start_model_is_rejected() {
		let (dir, mut out) = output("no-model");
		out.handle(Output::Trace, step(1, "del #1 by lin-valid"));
		out.handle(Output::Trace, end(1));
		let err = out.finish(&dir.join("received.fzn.json")).unwrap_err();
		assert!(
			matches!(
				err,
				PreprocessOutputError::Incomplete {
					output: Output::StartModel
				}
			),
			"{err:?}"
		);
		fs::remove_dir_all(&dir).unwrap();
	}

	#[test]
	fn missing_step_is_rejected() {
		let (dir, mut out) = output("gap");
		out.handle(Output::Trace, step(1, "del #1 by lin-valid"));
		out.handle(Output::Trace, step(3, "del #2 by lin-valid"));
		out.handle(Output::Trace, end(3));
		out.handle(Output::StartModel, end(0));
		let err = out.finish(&dir.join("received.fzn.json")).unwrap_err();
		assert!(
			matches!(err, PreprocessOutputError::MissingStep { step: 2 }),
			"{err:?}"
		);
		fs::remove_dir_all(&dir).unwrap();
	}

	/// Create the outputs of a preprocessing trace in a fresh directory, named
	/// after `test`, returning the directory and the outputs.
	fn output(test: &str) -> (std::path::PathBuf, PreprocessOutput) {
		let dir = env::temp_dir().join(format!("huub-preprocess-{}-{test}", process::id()));
		fs::create_dir_all(&dir).unwrap();
		let out = PreprocessOutput::new(dir.join("run.trace"), dir.join("start.fzt")).unwrap();
		(dir, out)
	}

	#[test]
	fn sha256_known_digests() {
		assert_eq!(
			sha256(b""),
			"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
		);
		assert_eq!(
			sha256(b"abc"),
			"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
		);
		// Two blocks after padding.
		assert_eq!(
			sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
			"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
		);
	}

	/// A step event with the given number.
	fn step(seq: u64, text: &str) -> OutputEvent {
		OutputEvent {
			seq: Some(seq),
			text: Some(text.to_owned()),
			end: None,
		}
	}

	#[test]
	fn unfinished_trace_is_rejected() {
		let (dir, mut out) = output("unfinished");
		out.handle(Output::Trace, step(1, "del #1 by lin-valid"));
		let err = out.finish(&dir.join("received.fzn.json")).unwrap_err();
		assert!(
			matches!(
				err,
				PreprocessOutputError::Incomplete {
					output: Output::Trace
				}
			),
			"{err:?}"
		);
		fs::remove_dir_all(&dir).unwrap();
	}

	#[test]
	fn unsat_trace_needs_no_start_model() {
		let (dir, mut out) = output("unsat");
		let received = dir.join("received.fzn.json");
		fs::write(&received, "{}").unwrap();
		out.handle(Output::Trace, step(1, "unsat by preserve hint #1"));
		out.handle(Output::Trace, end(1));
		out.finish(&received).unwrap();
		let trace = fs::read_to_string(dir.join("run.trace")).unwrap();
		assert!(trace.lines().nth(3).unwrap().ends_with(&sha256(b"")));
		fs::remove_dir_all(&dir).unwrap();
	}
}
