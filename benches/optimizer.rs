//! Benchmark the optimizer.

use hpbf::{CellType, Program};
use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use std::{fs, hint::black_box};

fn read_and_parse(file: &str) -> Program<u8> {
    Program::parse(&fs::read_to_string(file).unwrap()).unwrap()
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
], setup = read_and_parse)]
fn bench_opt_level_default(program: Program<u8>) -> Program<u8> {
    black_box(optimize(program, 1))
}

library_benchmark_group!(
    name = bench_opt_group;
    benchmarks = bench_opt_level_default
);

main!(library_benchmark_groups = bench_opt_group);
