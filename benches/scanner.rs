#![cfg(benches)]
#![feature(test)]

extern crate test;
use test::Bencher;

#[bench]
fn crox_scanner(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    b.bytes = input.len() as u64;
    b.iter(|| crox::scan(input).scan_all().unwrap());
}
