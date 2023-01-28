use criterion::{criterion_group, criterion_main, Criterion, Throughput};

fn parser_benchmarks(c: &mut Criterion) {
    let mut parser = c.benchmark_group("Parser");

    let input = include_str!("../tests/scanner/classes.crox");
    parser.throughput(Throughput::Bytes(input.len() as u64));

    parser.bench_function("scanner", |b| {
        b.iter(|| crox::scan(input).scan_all().unwrap());
    });
    parser.bench_function("parser", |b| {
        let arena = crox::Bump::new();
        b.iter(|| crox::parse(input, &arena))
    });

    parser.finish();
}

criterion_group!(benches, parser_benchmarks);
criterion_main!(benches);
