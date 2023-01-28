#![cfg(benches)]
#![feature(test)]

extern crate test;
use test::Bencher;

#[bench]
fn crox_parser(b: &mut Bencher) {
    let input = include_str!("../tests/scanner/classes.crox");
    let arena = crox::Bump::new();
    b.bytes = input.len() as u64;
    b.iter(|| crox::parse(input, &arena))
}
