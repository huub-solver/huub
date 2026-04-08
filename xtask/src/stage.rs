//! Local staging tree assembly for debugging and ad hoc deployment checks.

use std::{
	env::consts::EXE_SUFFIX,
	fs, io,
	path::{Path, PathBuf},
};

use clap::Parser;

use crate::{
	completion::CompletionsArgs, default_stage_dir, mzn_config::MznConfigArgs, target_dir,
	workspace_root,
};

/// Arguments for building a local staged deployment tree.
#[derive(Parser)]
pub(crate) struct StageArgs {
	/// Output directory for the staged deployment tree.
	#[arg(long, value_name = "DIR", default_value_os_t = default_stage_dir())]
	output_dir: PathBuf,
}

/// Create a symlink, replacing any existing staged entry.
fn create_symlink(source: &Path, destination: &Path, directory: bool) {
	let parent = destination
		.parent()
		.expect("staged paths must have a parent directory");
	fs::create_dir_all(parent)
		.unwrap_or_else(|err| panic!("failed to create directory '{}': {err}", parent.display()));
	remove_existing(destination)
		.unwrap_or_else(|err| panic!("failed to remove '{}': {err}", destination.display()));
	if directory {
		symlink_dir(source, destination).unwrap_or_else(|err| {
			panic!(
				"failed to create directory symlink '{}' -> '{}': {err}",
				destination.display(),
				source.display()
			)
		});
	} else {
		symlink_file(source, destination).unwrap_or_else(|err| {
			panic!(
				"failed to create file symlink '{}' -> '{}': {err}",
				destination.display(),
				source.display()
			)
		});
	}
	println!("{} -> {}", destination.display(), source.display());
}

/// Remove a staged path if it already exists.
fn remove_existing(path: &Path) -> io::Result<()> {
	match fs::symlink_metadata(path) {
		Ok(metadata) => {
			if metadata.file_type().is_symlink() {
				match fs::remove_file(path) {
					Ok(()) => Ok(()),
					Err(file_err) => match fs::remove_dir(path) {
						Ok(()) => Ok(()),
						Err(dir_err) => Err(io::Error::new(
							dir_err.kind(),
							format!(
								"unable to remove symlink '{}' as a file ({file_err}) or directory ({dir_err})",
								path.display()
							),
						)),
					},
				}
			} else if metadata.is_dir() {
				fs::remove_dir_all(path)
			} else {
				fs::remove_file(path)
			}
		}
		Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
		Err(err) => Err(err),
	}
}

/// Create a directory symlink on Unix platforms.
#[cfg(unix)]
fn symlink_dir(source: &Path, destination: &Path) -> io::Result<()> {
	std::os::unix::fs::symlink(source, destination)
}

/// Create a directory symlink on Windows platforms.
#[cfg(windows)]
fn symlink_dir(source: &Path, destination: &Path) -> io::Result<()> {
	std::os::windows::fs::symlink_dir(source, destination)
}

/// Create a file symlink on Unix platforms.
#[cfg(unix)]
fn symlink_file(source: &Path, destination: &Path) -> io::Result<()> {
	std::os::unix::fs::symlink(source, destination)
}

/// Create a file symlink on Windows platforms.
#[cfg(windows)]
fn symlink_file(source: &Path, destination: &Path) -> io::Result<()> {
	std::os::windows::fs::symlink_file(source, destination)
}

impl StageArgs {
	/// Assemble a staged deployment tree for local debugging.
	pub(crate) fn run(self) {
		let debug_bin = target_dir().join("debug").join(format!("huub{EXE_SUFFIX}"));
		let release_bin = target_dir()
			.join("release")
			.join(format!("huub{EXE_SUFFIX}"));

		let mznlib = workspace_root().join("share").join("minizinc").join("huub");
		assert!(
			mznlib.is_dir(),
			"MiniZinc library '{}' does not exist",
			mznlib.display()
		);

		create_symlink(
			&debug_bin,
			&self
				.output_dir
				.join("bin")
				.join(format!("huub-dev{EXE_SUFFIX}")),
			false,
		);
		create_symlink(
			&release_bin,
			&self
				.output_dir
				.join("bin")
				.join(format!("huub{EXE_SUFFIX}")),
			false,
		);
		create_symlink(
			&mznlib,
			&self.output_dir.join("share").join("minizinc").join("huub"),
			true,
		);

		MznConfigArgs {
			output_path: self
				.output_dir
				.join("share")
				.join("minizinc")
				.join("solvers")
				.join("huub-dev.msc"),
			dev: true,
			executable: Some("../../../bin/huub-dev".into()),
		}
		.run();
		MznConfigArgs {
			output_path: self
				.output_dir
				.join("share")
				.join("minizinc")
				.join("solvers")
				.join("huub.msc"),
			dev: false,
			executable: None,
		}
		.run();
		CompletionsArgs {
			output_dir: self.output_dir,
			shell: Vec::new(),
		}
		.run();
	}
}
