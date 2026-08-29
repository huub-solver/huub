//! Shell completion generation for the Huub CLI.

use std::{fs, path::PathBuf};

use clap::{CommandFactory, Parser};
use clap_complete::{Shell, generate};

use crate::{cli::Cli, default_stage_dir};

/// Arguments for completion generation.
#[derive(Parser)]
pub(crate) struct CompletionsArgs {
	/// Prefix directory where the shell-specific `share/` tree is written.
	#[arg(long, value_name = "DIR", default_value_os_t = default_stage_dir())]
	pub(crate) output_dir: PathBuf,
	/// Shells to generate. Defaults to Bash, Fish, and Zsh, plus PowerShell on
	/// Windows.
	#[arg(long, value_enum, value_name = "SHELL")]
	pub(crate) shell: Vec<Shell>,
}

impl CompletionsArgs {
	/// Generate shell completion files for the Huub CLI.
	pub(crate) fn run(self) {
		let shells = self.selected_shells();

		let mut command = Cli::<'static>::command();
		let command_name = command.get_name().to_owned();

		for (shell, path) in shells {
			let parent = path.parent().expect("completion paths must have a parent");
			fs::create_dir_all(parent).unwrap_or_else(|err| {
				panic!("failed to create directory '{}': {err}", parent.display())
			});
			let mut file = fs::File::create(&path)
				.unwrap_or_else(|err| panic!("failed to create file '{}': {err}", path.display()));
			generate(shell, &mut command, command_name.as_str(), &mut file);
			println!("{}", path.display());
		}
	}

	/// Resolve the shells to generate together with their output paths.
	fn selected_shells(&self) -> Vec<(Shell, PathBuf)> {
		let shells = if self.shell.is_empty() {
			let mut shells = vec![Shell::Bash, Shell::Fish, Shell::Zsh];
			if cfg!(windows) {
				shells.push(Shell::PowerShell);
			}
			shells
		} else {
			self.shell.clone()
		};

		shells
			.into_iter()
			.map(|shell| {
				let path = match shell {
					Shell::Bash => PathBuf::from("share")
						.join("bash-completion")
						.join("completions")
						.join("huub"),
					Shell::Elvish => PathBuf::from("share")
						.join("elvish")
						.join("lib")
						.join("huub.elv"),
					Shell::Fish => PathBuf::from("share")
						.join("fish")
						.join("vendor_completions.d")
						.join("huub.fish"),
					Shell::PowerShell => PathBuf::from("share")
						.join("pwsh")
						.join("completions")
						.join("huub.ps1"),
					Shell::Zsh => PathBuf::from("share")
						.join("zsh")
						.join("site-functions")
						.join("_huub"),
					_ => unreachable!("only supported shells should be accepted"),
				};
				(shell, self.output_dir.join(path))
			})
			.collect()
	}
}

#[cfg(test)]
mod tests {
	use clap::CommandFactory;
	use clap_complete::generate;

	use crate::{cli::Cli, completion::Shell};

	#[test]
	fn bash_completion_contains_flags() {
		let mut command = Cli::<'static>::command();
		let command_name = command.get_name().to_owned();
		let mut completion = Vec::new();
		generate(
			Shell::Bash,
			&mut command,
			command_name.as_str(),
			&mut completion,
		);
		let completion =
			String::from_utf8(completion).expect("clap completion output must be valid UTF-8");

		assert!(completion.contains("--time-limit"));
		assert!(completion.contains("--trace-target"));
		assert!(completion.contains("--all-optimal"));
	}
}
