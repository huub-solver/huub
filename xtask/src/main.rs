//! Workspace automation tasks for the Huub repository.

// The Huub command-line interface is compiled into `xtask` directly, rather
// than depended upon through the `huub-cli` crate, so that generating the shell
// completions and the MiniZinc solver configuration does not require building
// the solver. `cli.rs` is kept free of any dependency on the `huub` library for
// this reason.
#[path = "../../crates/huub-cli/src/cli.rs"]
#[expect(
	dead_code,
	unreachable_pub,
	reason = "xtask only inspects the interface, it never parses arguments with it"
)]
mod cli;
mod completion;
mod mzn_config;
mod stage;

use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand};

use crate::{completion::CompletionsArgs, mzn_config::MznConfigArgs, stage::StageArgs};

/// Command-line interface for repository automation tasks.
#[derive(Parser)]
#[command(name = "xtask")]
struct Xtask {
	/// Selected xtask subcommand.
	#[command(subcommand)]
	command: XtaskCommand,
}

/// Subcommands supported by the xtask binary.
#[derive(Subcommand)]
enum XtaskCommand {
	/// Generate shell completion files for the Huub CLI.
	Completions(CompletionsArgs),
	/// Generate the MiniZinc solver configuration file.
	MznConfig(MznConfigArgs),
	/// Assemble a local staged deployment tree for debugging.
	Stage(StageArgs),
}

/// Return the default staging directory under Cargo's target directory.
fn default_stage_dir() -> PathBuf {
	target_dir().join("staging")
}

fn main() {
	let xtask = Xtask::parse();
	match xtask.command {
		XtaskCommand::Completions(args) => args.run(),
		XtaskCommand::MznConfig(args) => args.run(),
		XtaskCommand::Stage(args) => args.run(),
	}
}

/// Return the Cargo target directory used for local build artifacts.
fn target_dir() -> PathBuf {
	std::env::var_os("CARGO_TARGET_DIR")
		.map(PathBuf::from)
		.unwrap_or_else(|| workspace_root().join("target"))
}

/// Return the workspace root for the `xtask` crate.
fn workspace_root() -> &'static Path {
	Path::new(env!("CARGO_MANIFEST_DIR"))
		.parent()
		.expect("xtask must live in the workspace root")
}
