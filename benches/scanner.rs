#![cfg(benches)]
#![feature(test)]

extern crate test;
use test::Bencher;

use crox::scan;

#[bench]
fn bench_scanner(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| scan(input).into_iter().collect::<Vec<_>>());
}

#[cfg(feature = "chumsky")]
#[bench]
fn bench_chumsky(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| scan(input).into_chumsky().unwrap());
}

#[cfg(feature = "nom")]
#[bench]
fn bench_nom(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| scan(input).into_nom().unwrap());
}
