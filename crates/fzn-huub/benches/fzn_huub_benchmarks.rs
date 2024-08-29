#![allow(unused_crate_dependencies)]
use std::{
	io::Write,
	path::{Path, PathBuf},
};

use codspeed_criterion_compat::{criterion_group, criterion_main, BenchmarkId, Criterion};
use expect_test::expect_file;
use fzn_huub::Cli;
use pico_args::Arguments;

const FZN_COMPLETE: &str = "==========\n";
const FZN_SEPERATOR: &str = "----------\n";
// const FZN_UNSATISFIABLE: &str = "=====UNSATISFIABLE=====\n";

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

pub(crate) fn check_final(name: &str, expect_optimal: bool) {
	let base = PathBuf::from("./corpus/").join(name);
	let fzn = base.with_extension("fzn.json");
	let out = run_solver(&fzn);
	let mut slice: &str = std::str::from_utf8(&out).expect("invalid utf-8");
	if expect_optimal {
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
	expect_file![sol].assert_eq(slice);
}

fn instant(c: &mut Criterion) {
	let mut group = c.benchmark_group("instant");
	let _ = group.sample_size(60);
	let instances = vec!["jobshop_la05"];
	for instance in instances {
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, true))
		});
	}
}

fn milliseconds(c: &mut Criterion) {
	let mut group = c.benchmark_group("under_second");
	let _ = group.sample_size(20);
	let instances = vec!["jobshop_la04"];
	for instance in instances {
		let _ = group.bench_with_input(BenchmarkId::from_parameter(instance), &instance, |b, s| {
			b.iter(|| check_final(s, true))
		});
	}
}

criterion_group!(benches, instant, milliseconds);
criterion_main!(benches);

impl Write for DummyOutput {
	fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
		Ok(buf.len())
	}
	fn flush(&mut self) -> std::io::Result<()> {
		Ok(())
	}
}
