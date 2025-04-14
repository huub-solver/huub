//! A Benchmarking framework for the full fzn-huub solver.
//!
//! Note that these benchmarks run through the full solver, providing the
//! instances as file input, and reading the output from its output stream. The
//! total time taken is repeatedly measured.

#![expect(
	unused_crate_dependencies,
	reason = "only dependencies for benchmarking are used in this file"
)]

#[path = "../tests/helpers/mod.rs"]
mod helpers;

use std::{path::PathBuf, time::Duration};

use codspeed_criterion_compat::{
	criterion_main, measurement::Measurement, BenchmarkGroup, BenchmarkId, Criterion, SamplingMode,
};
use expect_test::expect_file;

use crate::helpers::check_final;

/// A configuration for instances that run for a few seconds.
const FEW_SECONDS_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: Some(SamplingMode::Flat),
	sample_size: Some(10),
	measurement_time: Some(Duration::from_secs(60)),
};

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
		("jobshop_la04", &MILLISECONDS_CONFIG),
		("jobshop_la05", &INSTANT_CONFIG),
		("jobshop_newspaper", &INSTANT_CONFIG),
		("portal_10_9_10", &MILLISECONDS_CONFIG),
		("radiation_i6_9", &INSTANT_CONFIG),
		("radiation_i8_9", &MILLISECONDS_CONFIG),
		("svrp_s4_v2_c3", &MILLISECONDS_CONFIG),
		("ccmcp_3_20_015_3", &MILLISECONDS_CONFIG),
		("peaceable_queens_n5_q3", &MILLISECONDS_CONFIG),
	];

	for (instance, config) in instances {
		config.apply(&mut group);
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			let base = PathBuf::from("./corpus/").join(s);
			let fzn = base.with_extension("fzn.json");
			let sol = base.with_extension("sol").canonicalize().unwrap();
			b.iter(|| check_final(&fzn, true, expect_file![&sol]));
		});
	}
	group.finish();
}

/// Benchmarks of satisfaction problems (finding any correct solution).
///
/// Note that it is assumed that the solver will always find the same solution,
/// which is then checked.
fn satisfaction(c: &mut Criterion) {
	let mut group = c.benchmark_group("satisfaction");
	let instances = vec![
		("amaze3_2012_03_19", &MILLISECONDS_CONFIG),
		("steiner_t3_k4_N8", &INSTANT_CONFIG),
		("steiner_t6_k6_N7", &INSTANT_CONFIG),
		("sudoku_p48", &INSTANT_CONFIG),
	];

	for (instance, config) in instances {
		config.apply(&mut group);
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			let base = PathBuf::from("./corpus/").join(s);
			let fzn = base.with_extension("fzn.json");
			let sol = base.with_extension("sol").canonicalize().unwrap();
			b.iter(|| check_final(&fzn, false, expect_file![&sol]));
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

/// Module to capture the generated criterion code (which cannot be documented).
mod criterion_gen {
	use codspeed_criterion_compat::criterion_group;

	use crate::{optimization, satisfaction};

	criterion_group!(benches, optimization, satisfaction);
}

criterion_main!(criterion_gen::benches);
