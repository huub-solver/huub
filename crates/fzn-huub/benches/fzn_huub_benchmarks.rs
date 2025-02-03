//! A Benchmarking framework for the full fzn-huub solver.
//!
//! Note that these benchmarks run through the full solver, providing the
//! instances as file input, and reading the output from its output stream. The
//! total time taken is repeatedly measured.

#![expect(
	unused_crate_dependencies,
	reason = "only dependencies for benchmarking are used in this file"
)]

use std::{
	io::Write,
	path::{Path, PathBuf},
	time::Duration,
};

use codspeed_criterion_compat::{
	criterion_main, measurement::Measurement, BenchmarkGroup, BenchmarkId, Criterion, SamplingMode,
};
use expect_test::expect_file;
use fzn_huub::Cli;
use pico_args::Arguments;

/// A configuration for instances that run for a few seconds.
const FEW_SECONDS_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: Some(SamplingMode::Flat),
	sample_size: Some(10),
	measurement_time: Some(Duration::from_secs(60)),
};

/// The string that is printed when the solver has proven that no more/better
/// solutions exist.
const FZN_COMPLETE: &str = "==========\n";

/// The string that is printed after every solution.
const FZN_SEPERATOR: &str = "----------\n";

// /// The string that is printed when the solver has proven that the instance is
// /// unsatisfiable.
// const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

/// A configuration for instances that run in a few milliseconds.
const INSTANT_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: None,
	sample_size: Some(60),
	measurement_time: None,
};

/// A configuration for instances that run in less than a second.
const MILLISECONDS_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: Some(SamplingMode::Flat),
	sample_size: Some(20),
	measurement_time: Some(Duration::from_secs(20)),
};

#[derive(Debug, Clone)]
/// Configuration of criterion for a specific benchmark.
struct CriterionConfig {
	/// The [`SamplingMode`] to use, or none to use the default.
	sampling_mode: Option<SamplingMode>,
	/// The number of samples to take, or none to use the default.
	sample_size: Option<usize>,
	/// The time to measure for, or none to use the default.
	measurement_time: Option<Duration>,
}

#[derive(Debug, Clone, Copy)]
/// Output stream that immediately discards all data.
struct DummyOutput;

#[derive(Debug, Clone, Copy)]
/// What the goal is when running the solver on an instance.
enum InstanceType {
	/// An optimal solution should be found.
	Optimization,
	/// A correct solution should be found.
	Satisfaction,
}

/// Run the solver on the given instance and check the output.
fn check_final(name: &str, instance_type: InstanceType) {
	let base = PathBuf::from("./corpus/").join(name);
	let fzn = base.with_extension("fzn.json");
	let out = run_solver(&fzn);
	let mut slice: &str = std::str::from_utf8(&out).expect("invalid utf-8");
	if let InstanceType::Optimization = instance_type {
		assert!(
			slice.ends_with(FZN_COMPLETE),
			"Solver did not finish with complete marker: ```\n{}\n'''",
			slice
		);
		slice = &slice[..slice.len() - FZN_COMPLETE.len()];
	}
	assert!(
		slice.ends_with(FZN_SEPERATOR),
		"Solution did not end with a seperator: ```\n{}\n'''",
		slice
	);
	slice = &slice[..slice.len() - FZN_SEPERATOR.len()];
	let sol = base.with_extension("sol").canonicalize().unwrap();
	match instance_type {
		InstanceType::Optimization => assert!(slice.contains(&expect_file![sol].data())),
		InstanceType::Satisfaction => expect_file![sol].assert_eq(slice),
	}
}

/// Benchmarks of optimization problems (finding the optimal solution).
///
/// Note that it is assumed that the solver will always find the same optimal
/// solution, which is then checked.
fn optimization(c: &mut Criterion) {
	let mut group = c.benchmark_group("optimization");
	let instances = vec![
		("jobshop_la01", &MILLISECONDS_CONFIG),
		("jobshop_la02", &FEW_SECONDS_CONFIG),
		("jobshop_la03", &MILLISECONDS_CONFIG),
		("jobshop_la04", &FEW_SECONDS_CONFIG),
		("jobshop_la05", &INSTANT_CONFIG),
		("jobshop_newspaper", &INSTANT_CONFIG),
		("portal_10_9_10", &MILLISECONDS_CONFIG),
		("radiation_i6_9", &INSTANT_CONFIG),
		("radiation_i8_9", &MILLISECONDS_CONFIG),
		("svrp_s4_v2_c3", &FEW_SECONDS_CONFIG),
	];

	for (instance, config) in instances {
		config.apply(&mut group);
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, InstanceType::Optimization));
		});
	}
	group.finish();
}

/// Run the solver on the given instance and return the output as raw bytes.
fn run_solver(fzn: &Path) -> Vec<u8> {
	let args = Arguments::from_vec(vec![fzn.into()]);
	let cli: Cli<_, _> = args.try_into().unwrap();
	let mut out = Vec::new();
	let mut cli = cli.with_stdout(&mut out).with_stderr(|| DummyOutput, false);
	cli.run()
		.expect("unexpected error while running the solver");
	out
}

/// Benchmarks of satisfaction problems (finding any correct solution).
///
/// Note that it is assumed that the solver will always find the same solution,
/// which is then checked.
fn satisfaction(c: &mut Criterion) {
	let mut group = c.benchmark_group("satisfaction");
	let instances = vec![
		("amaze3_2012_03_19", &FEW_SECONDS_CONFIG),
		("steiner_t3_k4_N8", &INSTANT_CONFIG),
		("steiner_t6_k6_N7", &INSTANT_CONFIG),
		("sudoku_p48", &MILLISECONDS_CONFIG),
	];

	for (instance, config) in instances {
		config.apply(&mut group);
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, InstanceType::Satisfaction));
		});
	}
	group.finish();
}

impl CriterionConfig {
	/// Apply the configuration to the given [`BenchmarkGroup`].
	fn apply<M: Measurement>(&self, group: &mut BenchmarkGroup<'_, M>) {
		if let Some(sampling_mode) = self.sampling_mode {
			let _ = group.sampling_mode(sampling_mode);
		}
		if let Some(sample_size) = self.sample_size {
			let _ = group.sample_size(sample_size);
		}
		if let Some(measurement_time) = self.measurement_time {
			let _ = group.measurement_time(measurement_time);
		}
	}
}

impl Write for DummyOutput {
	fn flush(&mut self) -> std::io::Result<()> {
		Ok(())
	}
	fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
		Ok(buf.len())
	}
}

/// Module to capture the generated criterion code (which cannot be documented).
mod criterion_gen {
	use codspeed_criterion_compat::criterion_group;

	use crate::{optimization, satisfaction};

	criterion_group!(benches, optimization, satisfaction);
}

criterion_main!(criterion_gen::benches);
