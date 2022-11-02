#![cfg(benches)]
#![feature(test)]

extern crate test;
use std::vec::Vec;

use test::Bencher;

#[bench]
fn crox_parser(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    let source = crox::scan(input);
    let tokens = source.scan_all().unwrap();
    b.bytes = input.len() as u64;
    b.iter(|| crox::parser(source, tokens.iter().copied()).collect::<Vec<_>>());
}
