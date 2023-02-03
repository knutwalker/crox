use criterion::{criterion_group, criterion_main, BatchSize, Criterion, SamplingMode};
use crox::{Bump, CroxErrors};
use std::time::Duration;

fn lox_benchmarks(c: &mut Criterion) {
    fn run<'env>(content: &'env str, arena: &'env Bump) -> Result<(), CroxErrors> {
        crox::run(std::io::sink(), arena, content).map(drop)
    }

    let mut benches = c.benchmark_group("Benches");
    // These benchmarks take some time (in the seconds), to hit the target time
    // we reduce the sample size, use flat sampling and increasing the target time
    benches.sample_size(10);
    benches.sampling_mode(SamplingMode::Flat);
    benches.measurement_time(Duration::from_secs(60));

    benches.bench_function("binary_trees", |b| {
        let input = include_str!("../tests/benchmark/binary_trees.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("equality", |b| {
        let input = include_str!("../tests/benchmark/equality.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("fib", |b| {
        let input = include_str!("../tests/benchmark/fib.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("instantiation", |b| {
        let input = include_str!("../tests/benchmark/instantiation.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("invocation", |b| {
        let input = include_str!("../tests/benchmark/invocation.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("method_call", |b| {
        let input = include_str!("../tests/benchmark/method_call.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("properties", |b| {
        let input = include_str!("../tests/benchmark/properties.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("string_equality", |b| {
        let input = include_str!("../tests/benchmark/string_equality.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("trees", |b| {
        let input = include_str!("../tests/benchmark/trees.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("zoo", |b| {
        let input = include_str!("../tests/benchmark/zoo.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });
    benches.bench_function("zoo_batch", |b| {
        let input = include_str!("../tests/benchmark/zoo_batch.lox");
        b.iter_batched_ref(
            Bump::new,
            |arena| run(input, arena),
            BatchSize::PerIteration,
        )
    });

    benches.finish();
}

criterion_group!(benches, lox_benchmarks);
criterion_main!(benches);
