#![allow(unused_crate_dependencies)]
use std::{
	io::Write,
	path::{Path, PathBuf},
	time::Duration,
};

use codspeed_criterion_compat::{
	criterion_group, criterion_main, BenchmarkId, Criterion, SamplingMode,
};
use expect_test::expect_file;
use fzn_huub::Cli;
use pico_args::Arguments;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
// const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

#[derive(Debug, Clone, Copy)]
enum InstanceType {
	Optimization,
	Satisfaction,
}

#[derive(Debug, Clone, Copy)]
struct DummyOutput;

fn run_solver(fzn: &Path) -> Vec<u8> {
	let args = Arguments::from_vec(vec![fzn.into()]);
	let cli: Cli<_, _> = args.try_into().unwrap();
	let mut out = Vec::new();
	let mut cli = cli.with_stdout(&mut out).with_stderr(|| DummyOutput, false);
	cli.run()
		.expect("unexpected error while running the solver");
	out
}

pub(crate) fn check_final(name: &str, instance_type: InstanceType) {
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

/// Instances that can be solve instantly
fn instant(c: &mut Criterion) {
	let mut group = c.benchmark_group("instant");
	let group = group.sample_size(60);
	let instances = vec![
		("jobshop_newspaper", InstanceType::Optimization),
		("radiation_i6_9", InstanceType::Optimization),
		("jobshop_la05", InstanceType::Optimization),
		("steiner_t3_k4_N8", InstanceType::Satisfaction),
		("steiner_t6_k6_N7", InstanceType::Satisfaction),
	];
	for (instance, instance_type) in instances {
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, instance_type))
		});
	}
}

/// Instances that can be solved under a second
fn milliseconds(c: &mut Criterion) {
	let mut group = c.benchmark_group("under_second");
	let group = group
		.sample_size(20)
		.measurement_time(Duration::from_secs(20))
		.sampling_mode(SamplingMode::Flat);
	// optimization instances
	let instances = vec![
		("jobshop_la01", InstanceType::Optimization),
		("jobshop_la03", InstanceType::Optimization),
		("radiation_i8_9", InstanceType::Optimization),
		("sudoku_p48", InstanceType::Satisfaction),
	];
	for (instance, instance_type) in instances {
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, instance_type))
		});
	}
}

/// Instances that be solved within 5 seconds
fn a_few_seconds(c: &mut Criterion) {
	let mut group = c.benchmark_group("a_few_seconds");
	let group = group
		.sample_size(10)
		.measurement_time(Duration::from_secs(60))
		.sampling_mode(SamplingMode::Flat);

	let instances = vec![
		("jobshop_la02", InstanceType::Optimization),
		("jobshop_la04", InstanceType::Optimization),
		("kidney_exchange_3_20_0_15_3", InstanceType::Optimization),
		("kidney_exchange_3_25_0_10_2", InstanceType::Optimization),
		("svrp_s4_v2_c3", InstanceType::Optimization),
		("rotating_workforce_25_s_7", InstanceType::Satisfaction),
		("amaze3_2012_03_19", InstanceType::Satisfaction),
	];
	for (instance, instance_type) in instances {
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, instance_type))
		});
	}
}

criterion_group!(benches, instant, milliseconds, a_few_seconds);
criterion_main!(benches);

impl Write for DummyOutput {
	fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
		Ok(buf.len())
	}
	fn flush(&mut self) -> std::io::Result<()> {
		Ok(())
	}
}
