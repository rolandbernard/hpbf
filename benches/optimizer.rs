//! Benchmark the optimizer.

use hpbf::{CellType, Program};
use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use std::{fs, hint::black_box};

fn read_file(file: &str) -> String {
    fs::read_to_string(file).unwrap()
}

fn parse_program(code: &str) -> Program<u8> {
    Program::parse(code).unwrap()
}

fn read_and_parse(file: &str) -> Program<u8> {
    parse_program(&read_file(file))
}

fn optimize<C: CellType>(program: Program<C>, level: u32) -> Program<C> {
    program.optimize(level)
}

#[library_benchmark]
#[benches::with_setup(args = [
    "examples/hello.bf",
    "examples/hello2.bf",
    "examples/hanoi.bf",
    "examples/fib.bf",
    "examples/primes.bf",
    "examples/mandel.bf",
    "examples/dbfi.bf",
    "examples/bsort.bf",
    "examples/qsort.bf",
    "examples/factor.bf",
    "examples/factorial.bf",
    "examples/factorial2.bf",
    "examples/widthcheck.bf",
], setup = read_file)]
fn bench_parse(code: String) -> Program<u8> {
    black_box(parse_program(&code))
}

#[library_benchmark]
#[benches::with_setup(args = [
    "examples/hello.bf",
    "examples/hello2.bf",
    "examples/hanoi.bf",
    "examples/fib.bf",
    "examples/primes.bf",
    "examples/mandel.bf",
    "examples/dbfi.bf",
    "examples/bsort.bf",
    "examples/qsort.bf",
    "examples/factor.bf",
    "examples/factorial.bf",
    "examples/factorial2.bf",
    "examples/widthcheck.bf",
], setup = read_and_parse)]
fn bench_optimize(program: Program<u8>) -> Program<u8> {
    black_box(optimize(program, 2))
}

library_benchmark_group!(
    name = bench_group;
    benchmarks = bench_optimize, bench_parse
);

main!(library_benchmark_groups = bench_group);
