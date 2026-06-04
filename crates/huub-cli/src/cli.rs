//! Command-line argument definitions and parsing helpers.

use std::{
	ffi::OsString,
	fmt::{self, Debug, Write},
	fs::OpenOptions,
	io,
	path::PathBuf,
	sync::Arc,
	time::Duration,
};

use anstream::AutoStream;
use clap::{
	ArgAction, Args, ColorChoice, Parser, ValueEnum,
	builder::{BoolishValueParser, StyledStr, styling::Styles},
};
use huub::lower::{Lowerer, ReduceType};
use tracing_subscriber::fmt::writer::BoxMakeWriter;

/// Long description for the command-line interface.
const CLI_LONG_ABOUT: &str = r#"Create a Huub Solver instance tailored to a given FlatZinc JSON input file and solve the problem.

Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and maintainability in addition to speed. LCG solvers are a class of solvers that can be used to solve decision and optimization problems. They are characterized by their ability to dynamically add new Boolean variables and clauses to a Boolean Satisfiability (SAT) solver during the search process. This allows the solver to exploit the SAT solver's ability to learn from failures during the search process, without having to encode the full problem into Boolean variables and clauses.

Head to https://huub.solutions/ for more information about Huub."#;
/// Help heading used for behaviour flags.
const CLI_SECTION_BEHAVIOUR: &str = "Behaviour Options";
/// Help heading used for standard FlatZinc flags.
const CLI_SECTION_FLATZINC_STD: &str = "Standard FlatZinc Options";
/// Help heading used for initialization flags.
const CLI_SECTION_INIT: &str = "Initialization Options";
/// Help heading used for preprocessing and inprocessing flags.
const CLI_SECTION_PROCESSING: &str = "Preprocessing/Inprocessing Options";
/// Help heading used for search flags.
const CLI_SECTION_SEARCH: &str = "Search Options";

/// CaDiCaL-specific solver options.
///
/// These options configure preprocessing and inprocessing behaviour of the
/// CaDiCaL SAT solver. They have no effect when a different SAT backend is
/// used.
#[derive(Args, Debug)]
pub(crate) struct CadicalOptions {
	/// Control globally blocked clause elimination (conditioning).
	#[arg(long = "cadical-conditioning", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_CONDITIONING, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) conditioning: bool,
	/// Control SAT inprocessing during search.
	#[arg(long = "cadical-inprocessing", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_INPROCESSING, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) inprocessing: bool,
	/// Run the given number of SAT preprocessing rounds before search.
	#[arg(
		long = "cadical-preprocessing",
		value_name = "usize",
		default_value_t = Lowerer::DEFAULT_PREPROCESSING,
		help_heading = CLI_SECTION_PROCESSING
	)]
	pub(crate) preprocessing: usize,
	/// Whether to enable CaDiCaL's light preprocessing.
	#[arg(long = "cadical-preprocessing-light", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_PREPROCESSING_LIGHT, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) preprocessing_light: bool,
	/// Control failed-literal probing in the SAT solver.
	#[arg(long = "cadical-probing", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_PROBING, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) probing: bool,
	/// Request explanation clauses for all literals propagated at the conflict
	/// level.
	#[arg(long = "cadical-reason-eager", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_REASON_EAGER, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) reason_eager: bool,
	/// Set the interval (in conflicts) between clause-database reductions.
	#[arg(long = "cadical-reduce-interval", value_name = "usize", default_value_t = Lowerer::DEFAULT_REDUCE_INTERVAL, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) reduce_interval: usize,
	/// Set the function used to compute the target size of the learned clause
	/// database when it is reduced.
	#[arg(long = "cadical-reduce-type", value_enum, value_name = "type", default_value_t = CliReduceType::Sqrt, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) reduce_type: CliReduceType,
	/// Control global forward subsumption in the SAT solver.
	#[arg(long = "cadical-subsumption", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_SUBSUMPTION, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) subsumption: bool,
	/// Control bounded variable elimination in the SAT solver.
	#[arg(long = "cadical-variable-elimination", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_VARIABLE_ELIMINATION, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) variable_elimination: bool,
	/// Control clause vivification.
	#[arg(long = "cadical-vivify", action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_VIVIFICATION, help_heading = CLI_SECTION_PROCESSING)]
	pub(crate) vivification: bool,
}

/// FlatZinc command line interface for the Huub solver
///
/// This interface is intended to connect Huub with MiniZinc.
#[derive(Parser)]
#[command(
	name = "huub",
	version,
	about = "Create a Huub Solver instance tailored to a given FlatZinc JSON input file and solve the problem.",
	long_about = CLI_LONG_ABOUT,
	after_help = cli_examples(),
	disable_help_flag = true,
	disable_version_flag = true,
	disable_help_subcommand = true,
)]
pub struct Cli<'a> {
	/// Path to the FlatZinc JSON input file.
	#[arg(value_name = "FILE")]
	pub(crate) path: PathBuf,
	/// Output all (satisfiable) solutions.
	#[arg(short = 'a', long, help_heading = CLI_SECTION_FLATZINC_STD)]
	pub(crate) all_solutions: bool,
	/// Output all optimal solutions.
	///
	/// For MiniZinc compatibility, this option is also available under the
	/// (invalid short flag) alias `-a-o`.
	#[arg(long, help_heading = CLI_SECTION_FLATZINC_STD)]
	pub(crate) all_optimal: bool,
	/// Output intermediate solutions.
	#[arg(short = 'i', long, help_heading = CLI_SECTION_FLATZINC_STD)]
	pub(crate) intermediate_solutions: bool,
	/// Do not follow search annotations strictly, using Huub's determined
	/// search strategy instead.
	#[arg(short = 'f', long, help_heading = CLI_SECTION_FLATZINC_STD)]
	pub(crate) free_search: bool,
	/// Print MiniZinc-compatible solving statistics.
	#[arg(short = 's', long, help_heading = CLI_SECTION_FLATZINC_STD)]
	pub(crate) statistics: bool,
	/// Stop solving after the given time limit.
	#[arg(
		short = 't',
		long,
		value_parser = parse_time_limit,
		value_name = "duration",
		help_heading = CLI_SECTION_FLATZINC_STD
	)]
	pub(crate) time_limit: Option<Duration>,
	/// Increase tracing verbosity, repeat for more detail.
	#[arg(
		short = 'v',
		long,
		action = ArgAction::Count,
		help_heading = CLI_SECTION_FLATZINC_STD
	)]
	pub(crate) verbose: u8,

	/// Tracing targets enabled at the selected verbosity level.
	#[arg(long, value_name = "target", help_heading = CLI_SECTION_BEHAVIOUR)]
	pub(crate) trace_target: Vec<String>,
	/// Tracing targets disabled at the selected verbosity level.
	#[arg(long, value_name = "target", help_heading = CLI_SECTION_BEHAVIOUR)]
	pub(crate) no_trace_target: Vec<String>,
	/// Output log messages to a file instead of standard error.
	#[arg(long, value_name = "FILE", help_heading = CLI_SECTION_BEHAVIOUR)]
	pub(crate) log_file: Option<PathBuf>,
	/// Control ANSI color in tracing output.
	#[arg(
		long,
		value_name = "enum",
		default_value_t = ColorChoice::Auto,
		help_heading = CLI_SECTION_BEHAVIOUR
	)]
	pub(crate) color: ColorChoice,

	/// Maximum domain size for eagerly creating order literals.
	#[arg(long, value_name = "usize", default_value_t = Lowerer::DEFAULT_INT_EAGER_LIMIT, help_heading = CLI_SECTION_INIT)]
	pub(crate) int_eager_limit: usize,

	/// Auto-detection level for the model-side difference-logic service:
	/// 0/off, 1/basic = Global/Implied/Reified, 2/equals = +ImpliedEquals,
	/// 3/not-equals = +NotEquals/ImpliedNotEquals/ReifiedEquals.
	#[arg(long, value_name = "level", default_value_t = Lowerer::DEFAULT_DIFF_LOGIC_LEVEL, help_heading = CLI_SECTION_INIT)]
	pub(crate) diff_logic_level: huub::constraints::diff_logic::DiffLogicLevel,

	/// Control whether the solver may restart, overwritten by `-f`.
	#[arg(long, action = ArgAction::Set, value_parser = BoolishValueParser::new(), value_name = "bool", default_value_t = Lowerer::DEFAULT_RESTART, help_heading = CLI_SECTION_SEARCH)]
	pub(crate) restart: bool,
	/// Set the overarching search strategy used by the solver, overwritten by
	/// `-f`.
	#[arg(long, value_enum, value_name = "strategy", default_value_t = CliSearchStrategy::Branchers, help_heading = CLI_SECTION_SEARCH)]
	pub(crate) search_strategy: CliSearchStrategy,
	/// Set the search trigger used by the solver, required if
	/// `--search-strategy` is “transition” or “interleaved”.
	#[arg(long, value_enum, value_name = "trigger", default_value_t = CliSearchTrigger::Conflicts, hide_default_value = true, required_if_eq_any = [("search_strategy", "transition"), ("search_strategy", "interleaved")], help_heading = CLI_SECTION_SEARCH)]
	pub(crate) search_trigger: CliSearchTrigger,
	/// Set the required trigger interval (i.e. count) for search strategy
	/// “transition” or “interleaved”.
	///
	/// The interval is interpreted in units of the search trigger.
	/// For example, `--search-trigger conflicts --search-interval 100` triggers
	/// after/every 100 conflicts, while `--search-trigger restarts
	/// --search-interval 2` triggers after/every 2 restarts.
	#[arg(long, default_value_t = 1, value_name = "u64", hide_default_value = true, required_if_eq_any = [("search_strategy", "transition"), ("search_strategy", "interleaved")], help_heading = CLI_SECTION_SEARCH)]
	pub(crate) search_interval: u64,

	/// CaDiCaL-specific solver options.
	#[command(flatten)]
	pub(crate) cadical: CadicalOptions,

	// --- API options, not set through CLI ---
	/// Output stream for (intermediate) solutions and statistics.
	#[arg(skip = default_stdout())]
	pub(crate) stdout: Box<dyn io::Write + 'a>,

	// --- Standard Clap Flags (hidden from --help), handled by Clap ---
	/// Print help information.
	#[arg(short = 'h', long = "help", action = clap::ArgAction::Help, hide = true)]
	pub(crate) help: Option<bool>,
	/// Print version information.
	#[arg(short = 'V', long = "version", action = clap::ArgAction::Version, hide = true)]
	pub(crate) version: Option<bool>,
}

/// Clause-database reduction target functions exposed through the CLI.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum CliReduceType {
	/// Percentage-based reduction target.
	Prct,
	/// Square-root-based reduction target.
	Sqrt,
	/// Logarithmic reduction target.
	Log,
}

/// Search strategy options exposed through the CLI.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum CliSearchStrategy {
	/// Use the user provided branchers for all search decisions until they are
	/// exhausted, and only then defer to the SAT solver to make search
	/// decisions.
	Branchers,
	/// Always defer to the SAT solver to make search decisions, ignoring any
	/// user provided branchers.
	Sat,
	/// Transition from “branchers” to “sat” when the given trigger condition is
	/// met.
	Transition,
	/// Interleave “branchers” and “sat” search strategies, switching between
	/// them each time the trigger condition is met.
	Interleaved,
}

/// Trigger counters that can drive search-strategy transitions.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum CliSearchTrigger {
	/// Switch after the given number of conflicts have been encountered.
	Conflicts,
	/// Switch after the given number of restarts have been encountered.
	Restarts,
}

/// Build the styled examples block shown after the generated help output.
fn cli_examples() -> StyledStr {
	let styles = Styles::default();
	let header = styles.get_header();
	let context = styles.get_context();
	let literal = styles.get_literal();
	let prompt = context.bold().dimmed();
	let mut styled = StyledStr::new();
	let _ = write!(
		styled,
		r#"{header}Examples:{header:#}

      {context}Solve with a ten-minute time limit.{context:#}
      {prompt}${prompt:#} {literal}huub --time-limit 10min inst3.fzn.json{literal:#}

      {context}Solve an instance and stream intermediate solutions into MiniZinc for formatting.{context:#}
      {prompt}${prompt:#} {literal}huub -i schedule.fzn.json | minizinc --ozn-file schedule.ozn{literal:#}"#
	);
	styled
}

/// Create the default stdout writer for the CLI.
fn default_stdout<'a>() -> Box<dyn io::Write + 'a> {
	Box::new(io::stdout())
}

/// Parse time duration for the time limit flag.
fn parse_time_limit(s: &str) -> Result<Duration, humantime::DurationError> {
	if let Ok(ms) = s.parse() {
		Ok(Duration::from_millis(ms))
	} else {
		humantime::parse_duration(s)
	}
}

impl<'a> Cli<'a> {
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

	/// Set the writer that is used for the standard (solution) output.
	pub fn with_stdout<'new, W: io::Write + 'new>(self, stdout: W) -> Cli<'new> {
		Cli {
			help: self.help,
			version: self.version,
			path: self.path,
			all_solutions: self.all_solutions,
			all_optimal: self.all_optimal,
			intermediate_solutions: self.intermediate_solutions,
			free_search: self.free_search,
			statistics: self.statistics,
			time_limit: self.time_limit,
			verbose: self.verbose,
			trace_target: self.trace_target,
			no_trace_target: self.no_trace_target,
			int_eager_limit: self.int_eager_limit,
			diff_logic_level: self.diff_logic_level,
			restart: self.restart,
			search_strategy: self.search_strategy,
			search_trigger: self.search_trigger,
			search_interval: self.search_interval,
			cadical: self.cadical,
			log_file: self.log_file,
			color: self.color,
			stdout: Box::new(stdout),
		}
	}
}

impl Cli<'static> {
	/// Parse a CLI instance from command-line arguments.
	pub fn try_parse_from<I, T>(args: I) -> Result<Self, clap::Error>
	where
		I: IntoIterator<Item = T>,
		T: Into<OsString> + Clone,
	{
		let mut seen_double_dash = false;
		let args = args.into_iter().map(|arg| {
			let arg: OsString = arg.into();
			if seen_double_dash {
				return arg;
			}
			if arg == "--" {
				seen_double_dash = true;
				return arg;
			}
			if arg == "-a-o" {
				"--all-optimal".into()
			} else {
				arg
			}
		});
		<Self as Parser>::try_parse_from(args)
	}
}

impl Debug for Cli<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Cli")
			.field("path", &self.path)
			.field("all_solutions", &self.all_solutions)
			.field("all_optimal", &self.all_optimal)
			.field("intermediate_solutions", &self.intermediate_solutions)
			.field("free_search", &self.free_search)
			.field("statistics", &self.statistics)
			.field("time_limit", &self.time_limit)
			.field("verbose", &self.verbose)
			.field("trace_target", &self.trace_target)
			.field("no_trace_target", &self.no_trace_target)
			.field("int_eager_limit", &self.int_eager_limit)
			.field("restart", &self.restart)
			.field("search_strategy", &self.search_strategy)
			.field("search_trigger", &self.search_trigger)
			.field("search_interval", &self.search_interval)
			.field("cadical", &self.cadical)
			.field("log_file", &self.log_file)
			.field("color", &self.color)
			.finish_non_exhaustive()
	}
}

impl From<CliReduceType> for ReduceType {
	fn from(value: CliReduceType) -> Self {
		match value {
			CliReduceType::Prct => ReduceType::Percent,
			CliReduceType::Sqrt => ReduceType::Sqrt,
			CliReduceType::Log => ReduceType::Log,
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{path::PathBuf, time::Duration};

	use clap::ColorChoice;
	use huub::lower::{Lowerer, ReduceType};

	use crate::cli::{Cli, CliReduceType};

	#[test]
	fn bool_args() {
		let cli = Cli::try_parse_from([
			"huub",
			"--restart",
			"on",
			"--cadical-conditioning",
			"1",
			"--cadical-inprocessing",
			"false",
			"--cadical-reason-eager",
			"true",
			"--cadical-probing",
			"off",
			"--cadical-variable-elimination",
			"0",
			"--cadical-vivify",
			"1",
			"--cadical-subsumption",
			"on",
			"instance.fzn.json",
		])
		.unwrap();

		assert!(cli.restart);
		assert!(cli.cadical.conditioning);
		assert!(!cli.cadical.inprocessing);
		assert!(cli.cadical.reason_eager);
		assert!(!cli.cadical.probing);
		assert!(!cli.cadical.variable_elimination);
		assert!(cli.cadical.vivification);
		assert!(cli.cadical.subsumption);

		let err =
			Cli::try_parse_from(["huub", "--restart", "maybe", "instance.fzn.json"]).unwrap_err();
		let rendered = err.to_string();

		assert!(rendered.contains("invalid value 'maybe'"));
	}

	#[test]
	fn color_arg() {
		let cli = Cli::try_parse_from(["huub", "--color", "auto", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.color, ColorChoice::Auto);

		let cli = Cli::try_parse_from(["huub", "--color", "always", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.color, ColorChoice::Always);

		let cli = Cli::try_parse_from(["huub", "--color", "never", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.color, ColorChoice::Never);
	}

	#[test]
	fn duration_args() {
		let cli =
			Cli::try_parse_from(["huub", "--time-limit", "1500", "instance.fzn.json"]).unwrap();

		assert_eq!(cli.time_limit, Some(Duration::from_millis(1500)));

		let cli =
			Cli::try_parse_from(["huub", "--time-limit", "10min", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.time_limit, Some(Duration::from_mins(10)));

		let cli =
			Cli::try_parse_from(["huub", "--time-limit", "1h30min", "instance.fzn.json"]).unwrap();
		assert_eq!(
			cli.time_limit,
			Some(Duration::from_hours(1) + Duration::from_mins(30))
		);
	}

	#[test]
	fn minizinc_all_optimal_alias() {
		let cli = Cli::try_parse_from(["huub", "-a-o", "instance.fzn.json"]).unwrap();
		assert!(cli.all_optimal);
		assert!(!cli.all_solutions);

		let cli = Cli::try_parse_from(["huub", "--", "-a-o"]).unwrap();
		assert_eq!(cli.path, PathBuf::from("-a-o"));
		assert!(!cli.all_optimal);
		assert!(!cli.all_solutions);
	}

	#[test]
	fn reduce_args() {
		let cli = Cli::try_parse_from([
			"huub",
			"--cadical-reduce-type",
			"prct",
			"--cadical-reduce-interval",
			"250",
			"instance.fzn.json",
		])
		.unwrap();

		assert_eq!(cli.cadical.reduce_type, CliReduceType::Prct);
		assert_eq!(
			ReduceType::from(cli.cadical.reduce_type),
			ReduceType::Percent
		);
		assert_eq!(cli.cadical.reduce_interval, 250);

		for (input, expected) in [
			("prct", CliReduceType::Prct),
			("sqrt", CliReduceType::Sqrt),
			("log", CliReduceType::Log),
		] {
			let cli =
				Cli::try_parse_from(["huub", "--cadical-reduce-type", input, "instance.fzn.json"])
					.unwrap();
			assert_eq!(cli.cadical.reduce_type, expected);
		}

		let err = Cli::try_parse_from([
			"huub",
			"--cadical-reduce-type",
			"bogus",
			"instance.fzn.json",
		])
		.unwrap_err();
		assert!(err.to_string().contains("invalid value 'bogus'"));
	}

	#[test]
	fn solver_backed_defaults() {
		let cli = Cli::try_parse_from(["huub", "instance.fzn.json"]).unwrap();

		assert_eq!(cli.int_eager_limit, Lowerer::DEFAULT_INT_EAGER_LIMIT);
		assert_eq!(cli.restart, Lowerer::DEFAULT_RESTART);
		assert_eq!(cli.cadical.conditioning, Lowerer::DEFAULT_CONDITIONING);
		assert_eq!(cli.cadical.inprocessing, Lowerer::DEFAULT_INPROCESSING);
		assert_eq!(cli.cadical.preprocessing, Lowerer::DEFAULT_PREPROCESSING);
		assert_eq!(
			cli.cadical.preprocessing_light,
			Lowerer::DEFAULT_PREPROCESSING_LIGHT
		);
		assert_eq!(cli.cadical.probing, Lowerer::DEFAULT_PROBING);
		assert_eq!(cli.cadical.reason_eager, Lowerer::DEFAULT_REASON_EAGER);
		assert_eq!(
			cli.cadical.reduce_interval,
			Lowerer::DEFAULT_REDUCE_INTERVAL
		);
		assert_eq!(
			ReduceType::from(cli.cadical.reduce_type),
			Lowerer::DEFAULT_REDUCE_TYPE
		);
		assert_eq!(cli.cadical.subsumption, Lowerer::DEFAULT_SUBSUMPTION);
		assert_eq!(
			cli.cadical.variable_elimination,
			Lowerer::DEFAULT_VARIABLE_ELIMINATION
		);
		assert_eq!(cli.cadical.vivification, Lowerer::DEFAULT_VIVIFICATION);
	}

	#[test]
	fn string_args() {
		let cli = Cli::try_parse_from([
			"huub",
			"--trace-target",
			"brancher",
			"--no-trace-target",
			"solver",
			"--log-file",
			"huub.log",
			"instance.fzn.json",
		])
		.unwrap();

		assert_eq!(
			cli.trace_targets(),
			vec!["flatzinc".to_owned(), "brancher".to_owned()]
		);
		assert_eq!(cli.log_file.unwrap().to_string_lossy(), "huub.log");
	}

	#[test]
	fn verbose_count_arg() {
		let cli = Cli::try_parse_from(["huub", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.verbose, 0);

		let cli = Cli::try_parse_from(["huub", "-v", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.verbose, 1);

		let cli = Cli::try_parse_from(["huub", "-vv", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.verbose, 2);

		let cli = Cli::try_parse_from(["huub", "-v", "-v", "instance.fzn.json"]).unwrap();
		assert_eq!(cli.verbose, 2);
	}
}
