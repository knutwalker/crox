use criterion::{black_box, criterion_group, criterion_main, Criterion, SamplingMode};
use std::time::Duration;

fn lox_benchmarks(c: &mut Criterion) {
    fn run(content: &str) {
        let mut arena = crox::Bump::new();
        black_box(
            crox::run_as_script(true, std::io::sink(), std::io::sink(), &arena, content).unwrap(),
        );
        arena.reset();
    }

    let mut benches = c.benchmark_group("Benches");
    // These benchmarks take some time (in the seconds), to hit the target time
    // we reduce the sample size, use flat sampling and increasing the target time
    benches.sample_size(10);
    benches.sampling_mode(SamplingMode::Flat);
    benches.measurement_time(Duration::from_secs(120));

    benches.bench_function("binary_trees", |b| {
        let input = include_str!("../tests/benchmark/binary_trees.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("equality", |b| {
        let input = include_str!("../tests/benchmark/equality.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("fib", |b| {
        let input = include_str!("../tests/benchmark/fib.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("instantiation", |b| {
        let input = include_str!("../tests/benchmark/instantiation.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("invocation", |b| {
        let input = include_str!("../tests/benchmark/invocation.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("method_call", |b| {
        let input = include_str!("../tests/benchmark/method_call.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("properties", |b| {
        let input = include_str!("../tests/benchmark/properties.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("string_equality", |b| {
        let input = include_str!("../tests/benchmark/string_equality.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("trees", |b| {
        let input = include_str!("../tests/benchmark/trees.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("zoo", |b| {
        let input = include_str!("../tests/benchmark/zoo.lox");
        b.iter(|| run(input));
    });
    benches.bench_function("zoo_batch", |b| {
        let input = include_str!("../tests/benchmark/zoo_batch.lox");
        b.iter(|| run(input));
    });

    benches.finish();
}

criterion_group!(benches, lox_benchmarks);
criterion_main!(benches);
