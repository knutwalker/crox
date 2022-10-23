#![cfg_attr(benches, feature(test))]

#[cfg(not(benches))]
compile_error!("You must use the nightly toolchain to run benchmarks: cargo +nightly bench");

#[cfg(benches)]
extern crate test;

#[cfg(benches)]
use test::Bencher;

#[cfg(benches)]
#[bench]
fn crox_scanner(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| crox::scan(input).into_iter().collect::<Vec<_>>());
}

#[cfg(all(benches, feature = "chumsky"))]
#[bench]
fn chumsky_scanner(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| crox::scan(input).into_chumsky().unwrap());
}

#[cfg(all(benches, feature = "nom"))]
#[bench]
fn nom_scanner(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| crox::scan(input).into_nom().unwrap());
}
