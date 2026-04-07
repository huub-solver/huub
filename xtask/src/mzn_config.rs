//! MiniZinc solver configuration generation for the Huub CLI.

use std::{fs, path::PathBuf};

use clap::{Arg, ArgAction, Command, CommandFactory, Parser};
use serde::Serialize;
use serde_json::Value;

use crate::default_stage_dir;

/// Serialized MiniZinc extra flag entry.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct ExtraFlag(String, String, String, Value);

/// Arguments for MiniZinc solver configuration generation.
#[derive(Parser)]
pub(crate) struct MznConfigArgs {
	/// Default output path for the generated MiniZinc solver config.
	#[arg(long, value_name = "FILE", default_value_os_t = default_config_path())]
	pub(crate) output_path: PathBuf,
	/// Whether to add the `-dev` prefix to the solver name.
	#[arg(long)]
	pub(crate) dev: bool,
	/// The solver executable path.
	#[arg(long, value_name = "PATH")]
	pub(crate) executable: Option<PathBuf>,
}

/// Serialized MiniZinc solver configuration.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct SolverConfig {
	/// Display name of the solver.
	name: String,
	/// Solver version string.
	version: &'static str,
	/// Stable MiniZinc solver identifier.
	id: String,
	/// Solver capability tags.
	tags: &'static [&'static str],
	/// Input format accepted by the solver.
	input_type: &'static str,
	/// Relative path to the solver executable.
	executable: PathBuf,
	/// Relative path to the solver MiniZinc library.
	mznlib: &'static str,
	/// Standard FlatZinc flags exposed by MiniZinc.
	std_flags: Vec<String>,
	/// Additional solver-specific flags exposed by MiniZinc.
	extra_flags: Vec<ExtraFlag>,
}

/// Return the repository root as the default output prefix.
fn default_config_path() -> PathBuf {
	default_stage_dir()
		.join("share")
		.join("minizinc")
		.join("solvers")
		.join("huub.msc")
}

/// Parse the Clap default value into the corresponding JSON representation.
fn default_value_or(arg: &Arg, fallback: Value) -> Value {
	let Some(def) = arg
		.get_default_values()
		.first()
		.and_then(|value| value.to_str())
		.map(ToOwned::to_owned)
	else {
		return fallback;
	};
	if let Ok(x) = def.parse::<bool>() {
		return Value::Bool(x);
	}
	if let Ok(x) = def.parse::<i64>() {
		return Value::Number(x.into());
	}
	Value::String(def)
}

/// Convert a Clap argument into a MiniZinc extra flag entry.
fn extra_flag(arg: &Arg) -> ExtraFlag {
	let long = arg.get_long().expect("All flags must have a long form");
	let flag = format!("--{long}");

	let (ty, def) = flag_type(arg);

	let help = arg
		.get_help()
		.or_else(|| arg.get_long_help())
		.map(ToString::to_string)
		.unwrap_or_default();

	ExtraFlag(flag, help, ty, def)
}

/// Infer the MiniZinc type and default value for a Clap flag.
fn flag_type(arg: &Arg) -> (String, Value) {
	// Manual overrides
	if let Some("vsids-after-conflict") = arg.get_long() {
		return ("int".to_owned(), Value::String("".to_owned()));
	}

	let possible_values = arg
		.get_possible_values()
		.into_iter()
		.filter_map(|value| (!value.is_hide_set()).then(|| value.get_name().to_owned()))
		.collect::<Vec<_>>();

	if !possible_values.is_empty() {
		if possible_values == ["true", "false"] {
			return (
				"bool:true:false".to_owned(),
				default_value_or(arg, Value::Bool(false)),
			);
		}
		let type_name = format!("opt:{}", possible_values.join(":"));
		let def = default_value_or(
			arg,
			Value::String(possible_values.first().cloned().unwrap_or_else(String::new)),
		);
		return (type_name, def);
	}

	match arg.get_action() {
		ArgAction::SetTrue | ArgAction::SetFalse => {
			("bool".to_owned(), default_value_or(arg, Value::Bool(false)))
		}
		ArgAction::Set | ArgAction::Append => {
			let def = default_value_or(arg, Value::String(String::new()));
			let type_name = match def {
				Value::Bool(_) => "bool",
				Value::Number(_) => "int",
				Value::String(_) => "string",
				_ => unreachable!(),
			};
			(type_name.to_owned(), def)
		}
		_ => unreachable!(),
	}
}

/// Iterate over the public non-positional CLI arguments.
fn public_args(command: &Command) -> impl Iterator<Item = &Arg> {
	command
		.get_arguments()
		.filter(|arg| !arg.is_hide_set() && !arg.is_positional())
}

/// Build the MiniZinc solver configuration from the Clap command metadata.
fn solver_config() -> SolverConfig {
	let command = huub_cli::Cli::<'static>::command();
	SolverConfig {
		name: "Huub".to_owned(),
		version: env!("CARGO_PKG_VERSION"),
		id: "solutions.huub".to_owned(),
		tags: &["int", "bool", "sat", "lcg"],
		input_type: "JSON",
		executable: "../../../bin/huub".into(),
		mznlib: "../huub",
		std_flags: public_args(&command)
			.filter(|arg| std_flag(arg))
			.map(|arg| match arg.get_long() {
				Some("all-optimal") => "-a-o".to_owned(),
				_ => {
					let flag = arg
						.get_short()
						.expect("FlatZinc flags (included in stdFlags) must have a short form");
					format!("-{}", flag)
				}
			})
			.collect(),
		extra_flags: public_args(&command)
			.filter(|arg| !std_flag(arg))
			.map(extra_flag)
			.collect(),
	}
}

/// Return whether a Clap argument belongs in `stdFlags`.
fn std_flag(arg: &Arg) -> bool {
	arg.get_help_heading() == Some("Standard FlatZinc Options")
}

impl MznConfigArgs {
	/// Generate the MiniZinc solver configuration file for the Huub CLI.
	pub(crate) fn run(self) {
		let parent = self
			.output_path
			.parent()
			.expect("MiniZinc solver config path must have a parent");
		fs::create_dir_all(parent).unwrap_or_else(|err| {
			panic!("failed to create directory '{}': {err}", parent.display())
		});

		let mut msc = solver_config();
		if self.dev {
			msc.name = format!("{} (dev)", msc.name);
			msc.id = format!("{}-dev", msc.id);
		}
		if let Some(exec) = self.executable {
			msc.executable = exec;
		}

		let mut file = fs::File::create(&self.output_path).unwrap_or_else(|err| {
			panic!(
				"failed to create file '{}': {err}",
				self.output_path.display()
			)
		});
		serde_json::to_writer_pretty(&mut file, &msc).unwrap_or_else(|err| {
			panic!("unable to serialize solver config:\n{msc:?}\nerror: {err}")
		});
		println!("{}", self.output_path.display());
	}
}
