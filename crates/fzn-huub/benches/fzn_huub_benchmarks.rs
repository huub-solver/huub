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
	criterion_group, criterion_main, measurement::Measurement, BenchmarkGroup, BenchmarkId,
	Criterion, SamplingMode,
};
use expect_test::expect_file;
use fzn_huub::Cli;
use pico_args::Arguments;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
// const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

#[derive(Debug, Clone)]
struct CriterionConfig {
	sampling_mode: Option<SamplingMode>,
	sample_size: Option<usize>,
	measurement_time: Option<Duration>,
}

const INSTANT_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: None,
	sample_size: Some(60),
	measurement_time: None,
};
const MILLISECONDS_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: Some(SamplingMode::Flat),
	sample_size: Some(20),
	measurement_time: Some(Duration::from_secs(20)),
};
const FEW_SECONDS_CONFIG: CriterionConfig = CriterionConfig {
	sampling_mode: Some(SamplingMode::Flat),
	sample_size: Some(10),
	measurement_time: Some(Duration::from_secs(60)),
};

#[derive(Debug, Clone, Copy)]
struct DummyOutput;

#[derive(Debug, Clone, Copy)]
enum InstanceType {
	Optimization,
	Satisfaction,
}

fn run_solver(fzn: &Path) -> Vec<u8> {
	let args = Arguments::from_vec(vec![fzn.into()]);
	let cli: Cli<_, _> = args.try_into().unwrap();
	let mut out = Vec::new();
	let mut cli = cli.with_stdout(&mut out).with_stderr(|| DummyOutput, false);
	cli.run()
		.expect("unexpected error while running the solver");
	out
}

fn check_final(name: &str, instance_type: InstanceType) {
	let base = PathBuf::from("./corpus/").join(name);
	let fzn = base.with_extension("fzn.json");
	let out = run_solver(&fzn);
	let mut slice: &str = std::str::from_utf8(&out).expect("invalid utf-8");
	if let InstanceType::Optimization = instance_type {
		assert!(
			slice.ends_with(FZN_COMPLETE),
			"Solver did not finish with complete marker"
		);
		slice = &slice[..slice.len() - FZN_COMPLETE.len()];
	}
	assert!(
		slice.ends_with(FZN_SEPERATOR),
		"Solution did not end with a seperator"
	);
	slice = &slice[..slice.len() - FZN_SEPERATOR.len()];
	let sol = base.with_extension("sol").canonicalize().unwrap();
	match instance_type {
		InstanceType::Optimization => assert!(slice.contains(&expect_file![sol].data())),
		InstanceType::Satisfaction => expect_file![sol].assert_eq(slice),
	}
}

fn optimization(c: &mut Criterion) {
	let mut group = c.benchmark_group("optimization");
	let instances = vec![
		("jobshop_la01", &MILLISECONDS_CONFIG),
		("jobshop_la02", &FEW_SECONDS_CONFIG),
		("jobshop_la03", &MILLISECONDS_CONFIG),
		("jobshop_la04", &FEW_SECONDS_CONFIG),
		("jobshop_la05", &INSTANT_CONFIG),
		("jobshop_newspaper", &INSTANT_CONFIG),
		("radiation_i6_9", &INSTANT_CONFIG),
		("radiation_i8_9", &MILLISECONDS_CONFIG),
		("svrp_s4_v2_c3", &FEW_SECONDS_CONFIG),
	];

	for (instance, config) in instances {
		config.apply(&mut group);
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, InstanceType::Optimization))
		});
	}
	group.finish();
}

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
			b.iter(|| check_final(s, InstanceType::Satisfaction))
		});
	}
	group.finish();
}

criterion_group!(benches, optimization, satisfaction);
criterion_main!(benches);

impl CriterionConfig {
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
	fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
		Ok(buf.len())
	}
	fn flush(&mut self) -> std::io::Result<()> {
		Ok(())
	}
}
